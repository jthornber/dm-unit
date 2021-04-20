use log::*;
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::rc::Rc;
use thiserror::Error;

use crate::emulator::decode::*;
use crate::emulator::memory::*;
use crate::emulator::ir::*;

//-----------------------------

#[derive(Default)]
pub struct InstCache {
    basic_blocks: BTreeMap<u64, Rc<RefCell<BasicBlock>>>,
}

impl InstCache {
    pub fn new() -> Self {
        InstCache {
            basic_blocks: BTreeMap::new(),
        }
    }

    /// If loc occurs in any other block (eg, jumping back in a loop),
    /// that that block will be truncated.
    pub fn insert(&mut self, loc: u64, bb: BasicBlock) -> Rc<RefCell<BasicBlock>> {
        let r = Rc::new(RefCell::new(bb));
        self.basic_blocks.insert(loc, r.clone());
        r
    }

    pub fn get(&self, loc: u64) -> Option<Rc<RefCell<BasicBlock>>> {
        self.basic_blocks.get(&loc).cloned()
    }

    /// Removes any blocks that contain loc (there can be only one).
    pub fn invalidate(&mut self, _loc: u64) {}
}

//-----------------------------

pub struct BBStats {
    pub begin: Addr,
    pub end: Addr,
    pub hits: u64,
}

//-----------------------------

use Reg::*;

pub struct Stats {
    pub instrs: u64,
}

pub struct VM {
    reg: Vec<u64>,
    pub mem: Memory,
    breakpoints: BTreeSet<u64>,
    last_bp: Option<Addr>,
    pub stats: Stats,
    inst_cache: InstCache,
    next_bb_hits: u64,
    next_bb_misses: u64,
}

impl Drop for VM {
    fn drop(&mut self) {
        let hits = self.next_bb_hits as f64;
        let total = (self.next_bb_misses + self.next_bb_hits) as f64;
        let percent = (hits * 100.0) / total;
        debug!("next bb hits {:.0}%", percent);
    }
}

impl fmt::Display for VM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            r#"zero {:016x} ra {:016x} sp  {:016x} gp  {:016x}
tp   {:016x} t0 {:016x} t1  {:016x} t2  {:016x}
s0   {:016x} s1 {:016x} a0  {:016x} a1  {:016x}
a2   {:016x} a3 {:016x} a4  {:016x} a5  {:016x}
a6   {:016x} a7 {:016x} s2  {:016x} s3  {:016x}
s4   {:016x} s5 {:016x} s6  {:016x} s7  {:016x}
s8   {:016x} s9 {:016x} s10 {:016x} s11 {:016x}
t3   {:016x} t4 {:016x} t5  {:016x} t6  {:016x}
pc   {:016x}"#,
            self.reg(Zero),
            self.reg(Ra),
            self.reg(Sp),
            self.reg(Gp),
            self.reg(Tp),
            self.reg(T0),
            self.reg(T1),
            self.reg(T2),
            self.reg(S0),
            self.reg(S1),
            self.reg(A0),
            self.reg(A1),
            self.reg(A2),
            self.reg(A3),
            self.reg(A4),
            self.reg(A5),
            self.reg(A6),
            self.reg(A7),
            self.reg(S2),
            self.reg(S3),
            self.reg(S4),
            self.reg(S5),
            self.reg(S6),
            self.reg(S7),
            self.reg(S8),
            self.reg(S9),
            self.reg(S10),
            self.reg(S11),
            self.reg(T3),
            self.reg(T4),
            self.reg(T5),
            self.reg(T6),
            self.reg(PC)
        )
    }
}

#[derive(Error, Clone, Copy, Debug)]
pub enum VmErr {
    // FIXME: rename to MemoryError
    #[error("Bad memory access: {0:?}")]
    BadAccess(MemErr),

    #[error("Unable to decode instruction: {0}")]
    DecodeError(u32),

    #[error("Unimplemented instruction: {0:?}")]
    UnimplementedInstruction(Inst),

    #[error("ecall")]
    ECall,

    #[error("ebreak")]
    EBreak,

    #[error("User defined breakpoint")]
    Breakpoint,
}

pub type Result<T> = std::result::Result<T, VmErr>;

impl VM {
    pub fn new(mem: Memory) -> Self {
        VM {
            reg: vec![0; 33],
            mem,
            breakpoints: BTreeSet::new(),
            last_bp: None,
            stats: Stats { instrs: 0 },
            inst_cache: InstCache::new(),
            next_bb_hits: 0,
            next_bb_misses: 0,
        }
    }

    pub fn setup_stack(&mut self, size: u64) -> Result<()> {
        // We put the stack just below the 4G mark.
        let top = 1 << 32;
        let base = top - size;
        self.mem
            .mmap_zeroes(Addr(base), Addr(top), PERM_READ | PERM_WRITE)
            .map_err(VmErr::BadAccess)?;
        self.set_reg(Sp, top);
        Ok(())
    }

    pub fn push(&mut self, v: u64) -> Result<()> {
        let sp = self.reg(Reg::Sp) - 8;
        let bytes = v.to_le_bytes();
        self.mem
            .write(Addr(sp), &bytes, 0)
            .map_err(VmErr::BadAccess)?;
        self.set_reg(Sp, sp);
        Ok(())
    }

    pub fn reg(&self, r: Reg) -> u64 {
        if r == Zero {
            0u64
        } else {
            self.reg[r as usize]
        }
    }

    pub fn set_reg(&mut self, r: Reg, v: u64) {
        if r != Zero {
            self.reg[r as usize] = v;
        }
    }

    pub fn set_pc(&mut self, loc: Addr) {
        self.reg[PC as usize] = loc.0;
    }

    pub fn inc_pc(&mut self, delta: u64) {
        self.reg[PC as usize] = self.pc().0.wrapping_add(delta);
    }

    pub fn pc(&self) -> Addr {
        Addr(self.reg[PC as usize])
    }

    pub fn branch(&mut self, pred: bool, dest: u64, pc_increment: u64) {
        if pred {
            self.set_reg(PC, dest);
        } else {
            self.inc_pc(pc_increment);
        }
    }

    fn deref_u32(&self, r: Reg) -> Result<u32> {
        let src = Addr(self.reg(r));
        let mut bytes = [0u8; 4];
        self.mem
            .read(src, &mut bytes, PERM_READ)
            .map_err(VmErr::BadAccess)?;
        Ok(u32::from_le_bytes(bytes))
    }

    fn deref_u64(&self, r: Reg) -> Result<u64> {
        let src = Addr(self.reg(r));
        let mut bytes = [0u8; 8];
        self.mem
            .read(src, &mut bytes, PERM_READ)
            .map_err(VmErr::BadAccess)?;
        Ok(u64::from_le_bytes(bytes))
    }

    fn set_deref_u32(&mut self, dest: Reg, v: u32) -> Result<()> {
        let dest = Addr(self.reg(dest));
        let bytes = v.to_le_bytes();
        self.mem
            .write(dest, &bytes, PERM_WRITE)
            .map_err(VmErr::BadAccess)
    }

    fn set_deref_u64(&mut self, dest: Reg, v: u64) -> Result<()> {
        let dest = Addr(self.reg(dest));
        let bytes = v.to_le_bytes();
        self.mem
            .write(dest, &bytes, PERM_WRITE)
            .map_err(VmErr::BadAccess)
    }

    fn amo_op_u32<F: FnOnce(u32, u32) -> u32>(
        &mut self,
        rd: Reg,
        rs1: Reg,
        rs2: Reg,
        f: F,
    ) -> Result<()> {
        let t = self.deref_u32(rs1)?;
        self.set_deref_u32(rs1, f(t, self.reg(rs2) as u32))?;
        self.set_reg(rd, t as i32 as i64 as u64);
        Ok(())
    }

    fn amo_op_u64<F: FnOnce(u64, u64) -> u64>(
        &mut self,
        rd: Reg,
        rs1: Reg,
        rs2: Reg,
        f: F,
    ) -> Result<()> {
        let t = self.deref_u64(rs1)?;
        self.set_deref_u64(rs1, f(t, self.reg(rs2)))?;
        self.set_reg(rd, t);
        Ok(())
    }

    // executes an ad-hoc 'ret' instruction after putting a return value in A0.  Useful for breakpoints.
    pub fn ret(&mut self, v: u64) {
        self.set_reg(A0, v);
        self.set_reg(PC, self.reg(Ra))
    }

    // Pushes a register onto the stack
    pub fn push_reg(&mut self, rd: Reg) -> Result<()> {
        // addi sp,sp,-8
        self.set_reg(Sp, self.reg(Sp).wrapping_add(-8i64 as u64));

        // sd r,0(sp)
        let dest = Addr(self.reg(Sp));
        let v = self.reg(rd);
        let bytes = v.to_le_bytes();
        self.mem
            .write(dest, &bytes, PERM_WRITE)
            .map_err(VmErr::BadAccess)?;
        Ok(())
    }

    // Pops the stack into a register
    pub fn pop_reg(&mut self, rd: Reg) -> Result<()> {
        // ld r,0(sp)
        let src = Addr(self.reg(Sp));
        let mut bytes = [0u8; 8];
        self.mem
            .read(src, &mut bytes, PERM_READ)
            .map_err(VmErr::BadAccess)?;
        self.set_reg(rd, i64::from_le_bytes(bytes) as i64 as u64);

        // addi sp,sp,8
        self.set_reg(Sp, self.reg(Sp).wrapping_add(8u64));
        Ok(())
    }

    pub fn step(&mut self, inst: Inst, pc_increment: u64) -> Result<()> {
        let pc = self.pc();
        self.stats.instrs += 1;

        use Inst::*;
        match inst {
            Lui { rd, imm } => {
                self.set_reg(rd, (imm << 12) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Auipc { rd, imm } => {
                self.set_reg(rd, pc.0.wrapping_add((imm << 12) as i64 as u64));
                self.inc_pc(pc_increment);
            }
            Jal { rd, imm } => {
                let dest = pc.0.wrapping_add(imm as i64 as u64);
                let ret = pc.0.wrapping_add(pc_increment);

                self.set_reg(PC, dest);
                self.set_reg(rd, ret);
            }
            Jalr { rd, rs, imm } => {
                let dest = self.reg(rs).wrapping_add(imm as i64 as u64);
                let ret = pc.0.wrapping_add(pc_increment);

                self.set_reg(rd, ret);
                self.set_reg(PC, dest);
            }
            Beq { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) == self.reg(rs2), dest, pc_increment);
            }
            Bne { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) != self.reg(rs2), dest, pc_increment);
            }
            Blt { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(
                    (self.reg(rs1) as i64) < (self.reg(rs2) as i64),
                    dest,
                    pc_increment,
                );
            }
            Bge { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(
                    (self.reg(rs1) as i64) >= (self.reg(rs2) as i64),
                    dest,
                    pc_increment,
                );
            }
            Bltu { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) < self.reg(rs2), dest, pc_increment);
            }
            Bgeu { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) >= self.reg(rs2), dest, pc_increment);
            }
            Lb { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<i8>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Lh { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<i16>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Lw { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<i32>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Ld { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<i64>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as u64);
                self.inc_pc(pc_increment);
            }
            Lbu { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<u8>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as u64);
                self.inc_pc(pc_increment);
            }
            Lhu { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<u16>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as u64);
                self.inc_pc(pc_increment);
            }
            Lwu { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let v = self
                    .mem
                    .read_into::<u32>(src, PERM_READ)
                    .map_err(VmErr::BadAccess)?;
                self.set_reg(rd, v as u64);
                self.inc_pc(pc_increment);
            }
            Sb { rs1, rs2, imm } => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2) as u8;
                self.mem
                    .write_out::<u8>(v, dest, PERM_WRITE)
                    .map_err(VmErr::BadAccess)?;
                self.inc_pc(pc_increment);
            }
            Sh { rs1, rs2, imm } => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2) as u16;
                self.mem
                    .write_out::<u16>(v, dest, PERM_WRITE)
                    .map_err(VmErr::BadAccess)?;
                self.inc_pc(pc_increment);
            }
            Sw { rs1, rs2, imm } => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2) as u32;
                self.mem
                    .write_out::<u32>(v, dest, PERM_WRITE)
                    .map_err(VmErr::BadAccess)?;
                self.inc_pc(pc_increment);
            }
            Sd { rs1, rs2, imm } => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2);
                self.mem
                    .write_out::<u64>(v, dest, PERM_WRITE)
                    .map_err(VmErr::BadAccess)?;
                self.inc_pc(pc_increment);
            }
            Addi { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs).wrapping_add(imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            Addiw { rd, rs, imm } => {
                let rs = self.reg(rs) as u32;
                self.set_reg(rd, rs.wrapping_add(imm as u32) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Slti { rd, rs, imm } => {
                let v = if (self.reg(rs) as i64) < (imm as i64) {
                    1
                } else {
                    0
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            Sltiu { rd, rs, imm } => {
                let v = if (self.reg(rs) as u64) < (imm as u64) {
                    1
                } else {
                    0
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            Xori { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs) ^ (imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            Ori { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs) | (imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            Andi { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs) & (imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            Slli { rd, rs, shamt } => {
                self.set_reg(rd, self.reg(rs) << shamt);
                self.inc_pc(pc_increment);
            }
            Srli { rd, rs, shamt } => {
                self.set_reg(rd, self.reg(rs) >> shamt);
                self.inc_pc(pc_increment);
            }
            Srai { rd, rs, shamt } => {
                self.set_reg(rd, ((self.reg(rs) as i64) >> shamt) as u64);
                self.inc_pc(pc_increment);
            }
            Add { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1).wrapping_add(self.reg(rs2)));
                self.inc_pc(pc_increment);
            }
            Sub { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1).wrapping_sub(self.reg(rs2)));
                self.inc_pc(pc_increment);
            }
            Sll { rd, rs1, rs2 } => {
                let shamt = self.reg(rs2) & 0b111111;
                self.set_reg(rd, self.reg(rs1) << shamt);
                self.inc_pc(pc_increment);
            }
            Slt { rd, rs1, rs2 } => {
                let v = if (self.reg(rs1) as i64) < (self.reg(rs2) as i64) {
                    1
                } else {
                    0
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            Sltu { rd, rs1, rs2 } => {
                let v = if self.reg(rs1) < self.reg(rs2) { 1 } else { 0 };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            Xor { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1) ^ self.reg(rs2));
                self.inc_pc(pc_increment);
            }
            Srl { rd, rs1, rs2 } => {
                let shamt = self.reg(rs2) & 0b111111;
                self.set_reg(rd, self.reg(rs1) >> shamt);
                self.inc_pc(pc_increment);
            }
            Sra { rd, rs1, rs2 } => {
                let shamt = self.reg(rs2) & 0b111111;
                self.set_reg(rd, ((self.reg(rs1) as i64) >> shamt) as u64);
                self.inc_pc(pc_increment);
            }
            Or { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1) | self.reg(rs2));
                self.inc_pc(pc_increment);
            }
            And { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1) & self.reg(rs2));
                self.inc_pc(pc_increment);
            }
            Slliw { rd, rs, shamt } => {
                let rs = self.reg(rs) as i32;
                self.set_reg(rd, (rs << shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Srliw { rd, rs, shamt } => {
                let rs = self.reg(rs) as u32;
                self.set_reg(rd, (rs >> shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Sraiw { rd, rs, shamt } => {
                let rs = self.reg(rs) as i32;
                self.set_reg(rd, ((rs as i32) >> shamt) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Addw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                self.set_reg(rd, rs1.wrapping_add(rs2) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Subw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                self.set_reg(rd, rs1.wrapping_sub(rs2) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Sllw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let shamt = rs2 & 0b11111;
                self.set_reg(rd, (rs1 << shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Srlw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let shamt = rs2 & 0b11111;
                self.set_reg(rd, (rs1 >> shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Sraw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let shamt = rs2 & 0b11111;
                self.set_reg(rd, ((rs1 as i32) >> shamt) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Mul { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1);
                let rs2 = self.reg(rs2);
                self.set_reg(rd, rs1.wrapping_mul(rs2));
                self.inc_pc(pc_increment);
            }

            Mulh { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as i64 as u128;
                let rs2 = self.reg(rs2) as i64 as u128;
                self.set_reg(rd, (rs1.wrapping_mul(rs2) >> 64) as u64);
                self.inc_pc(pc_increment);
            }
            Mulhsu { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as i64 as u128;
                let rs2 = self.reg(rs2) as u64 as u128;
                self.set_reg(rd, (rs1.wrapping_mul(rs2) >> 64) as u64);
                self.inc_pc(pc_increment);
            }
            Mulhu { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u64 as u128;
                let rs2 = self.reg(rs2) as u64 as u128;
                self.set_reg(rd, (rs1.wrapping_mul(rs2) >> 64) as u64);
                self.inc_pc(pc_increment);
            }
            Div { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as i64;
                let rs2 = self.reg(rs2) as i64;
                let v = if rs2 == 0 { -1 } else { rs1.wrapping_div(rs2) };
                self.set_reg(rd, v as u64);
                self.inc_pc(pc_increment);
            }
            Divu { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1);
                let rs2 = self.reg(rs2);
                let v = if rs2 == 0 {
                    core::u64::MAX
                } else {
                    rs1.wrapping_div(rs2)
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            Rem { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as i64;
                let rs2 = self.reg(rs2) as i64;
                let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                self.set_reg(rd, v as u64);
                self.inc_pc(pc_increment);
            }
            Remu { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1);
                let rs2 = self.reg(rs2);
                let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            Mulw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let v = (rs1 as u32).wrapping_mul(rs2 as u32);
                self.set_reg(rd, v as i32 as u64);
                self.inc_pc(pc_increment);
            }
            Divw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as i32;
                let rs2 = self.reg(rs2) as i32;
                let v = if rs2 == 0 { -1 } else { rs1.wrapping_div(rs2) };
                self.set_reg(rd, v as i32 as u64);
                self.inc_pc(pc_increment);
            }
            Divuw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let v = if rs2 == 0 {
                    core::u32::MAX
                } else {
                    rs1.wrapping_div(rs2)
                };
                self.set_reg(rd, v as i32 as u64);
                self.inc_pc(pc_increment);
            }
            Remw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as i32;
                let rs2 = self.reg(rs2) as i32;
                let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                self.set_reg(rd, v as i32 as u64);
                self.inc_pc(pc_increment);
            }
            Remuw { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1);
                let rs2 = self.reg(rs2);
                let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                self.set_reg(rd, v as i32 as u64);
                self.inc_pc(pc_increment);
            }
            Fence {} => {
                self.inc_pc(pc_increment);
            }
            Fencei {} => {
                self.inc_pc(pc_increment);
            }

            Lrw { rd, rs } => {
                self.set_reg(rd, self.deref_u32(rs)? as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Scw { rd, rs1, rs2 } => {
                self.set_deref_u32(rs1, self.reg(rs2) as u32)?;
                self.set_reg(rd, 0);
                self.inc_pc(pc_increment);
            }
            Amoswapw { rd, rs1, rs2 } => {
                let t = self.deref_u32(rs1)?;
                self.set_deref_u32(rs1, self.reg(rs2) as u32)?;
                self.set_reg(rd, t as i32 as u32 as u64);
                self.inc_pc(pc_increment);
            }
            Amoaddw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, |l, r| l + r)?;
                self.inc_pc(pc_increment);
            }
            Amoxorw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, |l, r| l ^ r)?;
                self.inc_pc(pc_increment);
            }
            Amoandw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, |l, r| l & r)?;
                self.inc_pc(pc_increment);
            }
            Amoorw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, |l, r| l | r)?;
                self.inc_pc(pc_increment);
            }
            Amominw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, |l, r| i32::min(l as i32, r as i32) as u32)?;
                self.inc_pc(pc_increment);
            }
            Amomaxw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, |l, r| i32::max(l as i32, r as i32) as u32)?;
                self.inc_pc(pc_increment);
            }
            Amominuw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, u32::min)?;
                self.inc_pc(pc_increment);
            }
            Amomaxuw { rd, rs1, rs2 } => {
                self.amo_op_u32(rd, rs1, rs2, u32::max)?;
                self.inc_pc(pc_increment);
            }
            Lrd { rd, rs } => {
                self.set_reg(rd, self.deref_u64(rs)? as i64 as u64);
                self.inc_pc(pc_increment);
            }
            Scd { rd, rs1, rs2 } => {
                self.set_deref_u64(rs1, self.reg(rs2))?;
                self.set_reg(rd, 0);
                self.inc_pc(pc_increment);
            }
            Amoswapd { rd, rs1, rs2 } => {
                let t = self.deref_u64(rs1)?;
                self.set_deref_u64(rs1, self.reg(rs2))?;
                self.set_reg(rd, t);
                self.inc_pc(pc_increment);
            }
            Amoaddd { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, |l, r| l + r)?;
                self.inc_pc(pc_increment);
            }
            Amoxord { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, |l, r| l ^ r)?;
                self.inc_pc(pc_increment);
            }
            Amoandd { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, |l, r| l & r)?;
                self.inc_pc(pc_increment);
            }
            Amoord { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, |l, r| l | r)?;
                self.inc_pc(pc_increment);
            }
            Amomind { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, |l, r| i64::min(l as i64, r as i64) as u64)?;
                self.inc_pc(pc_increment);
            }
            Amomaxd { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, |l, r| i64::max(l as i64, r as i64) as u64)?;
                self.inc_pc(pc_increment);
            }
            Amominud { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, u64::min)?;
                self.inc_pc(pc_increment);
            }
            Amomaxud { rd, rs1, rs2 } => {
                self.amo_op_u64(rd, rs1, rs2, u64::max)?;
                self.inc_pc(pc_increment);
            }
            Ecall => {
                return Err(VmErr::ECall);
            }
            Ebreak => {
                return Err(VmErr::EBreak);
            }
        }

        Ok(())
    }

    fn find_bb(&mut self) -> Result<Rc<RefCell<BasicBlock>>> {
        let pc = self.pc();
        let bb = match self.inst_cache.get(pc.0) {
            None => {
                let bb = self
                    .mem
                    .read_some(pc, PERM_EXEC, |bytes| {
                        decode_basic_block(pc.0, bytes, 100, &self.breakpoints)
                            .map_err(VmErr::DecodeError)
                    })
                    .map_err(VmErr::BadAccess)?;

                self.inst_cache.insert(pc.0, bb?)
            }
            Some(bb) => bb,
        };

        Ok(bb)
    }

    fn follow_or_find_bb(
        &mut self,
        prev_bb: &Option<Rc<RefCell<BasicBlock>>>,
    ) -> Result<Rc<RefCell<BasicBlock>>> {
        let pc = self.pc();
        if let Some(prev_bb) = prev_bb {
            let prev_bb = prev_bb.borrow();
            if let Some(next) = prev_bb.next.upgrade() {
                if next.borrow().begin == pc.0 {
                    self.next_bb_hits += 1;
                    return Ok(next);
                }
            }
        }

        self.next_bb_misses += 1;
        self.find_bb()
    }

    fn exec_bb(&mut self, bb: &Rc<RefCell<BasicBlock>>) -> Result<()> {
        let pc = self.pc();
        let mut bb = bb.borrow_mut();
        if bb.breakpoint {
            if self.last_bp.is_none() || self.last_bp.unwrap() != pc {
                self.last_bp = Some(pc);
                return Err(VmErr::Breakpoint);
            }
        } else if self.last_bp.is_some() && pc != self.last_bp.unwrap() {
            self.last_bp = None;
        }

        bb.hits += 1;

        if bb.hits > 100 && bb.instrs.len() >= 22 {
                debug!("riscv ({} instructions):", bb.instrs.len());
		for (inst, _width) in &bb.instrs {
    		    debug!("    {}", inst);
		}

		let ir = to_ir(&bb.instrs);
		debug!("ir ({} instructions):", ir.len());
		for inst in ir {
    		    debug!("    {}", inst);
		}

		assert!(false);
        }

        for (inst, width) in &bb.instrs {
            // debug!("{:08x}: {}", addr, inst);
            self.step(*inst, *width as u64)?;
        }
        Ok(())
    }

    pub fn run(&mut self) -> Result<()> {
        let mut prev_bb: Option<Rc<RefCell<BasicBlock>>> = None;
        loop {
            let bb = self.follow_or_find_bb(&prev_bb)?;

            if let Some(prev_bb) = prev_bb {
                let mut prev_bb = prev_bb.borrow_mut();
                prev_bb.next = Rc::downgrade(&bb);
            }

            self.exec_bb(&bb)?;
            prev_bb = Some(bb);
        }
    }

    pub fn add_breakpoint(&mut self, loc: Addr) {
        self.breakpoints.insert(loc.0);
        self.inst_cache.invalidate(loc.0);
    }

    pub fn rm_breakpoint(&mut self, loc: Addr) -> bool {
        self.inst_cache.invalidate(loc.0);
        self.breakpoints.remove(&loc.0)
    }

    pub fn get_hot_basic_blocks(&self) -> Vec<BBStats> {
        let mut stats = Vec::with_capacity(self.inst_cache.basic_blocks.len());

        for (_, bb) in &self.inst_cache.basic_blocks {
            let bb = bb.borrow();
            stats.push(BBStats {
                begin: Addr(bb.begin),
                end: Addr(bb.end),
                hits: bb.hits,
            });
        }

        stats.sort_by_key(|bbs| Reverse(bbs.hits));
        stats
    }

    pub fn get_bb_stats(&self, ptr: Addr) -> Option<BBStats> {
        self.inst_cache.basic_blocks.get(&ptr.0).map(|bb| {
            let bb = bb.borrow();
            BBStats {
                begin: Addr(bb.begin),
                end: Addr(bb.end),
                hits: bb.hits,
            }
        })
    }
}

//------------------------
