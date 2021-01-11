use crate::decode::*;
use crate::memory::*;
use thiserror::Error;

use std::fmt;

//-----------------------------

use Reg::*;

pub struct VM {
    reg: Vec<u64>,
    pub mem: Memory,
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

#[derive(Error, Debug)]
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
}

pub type Result<T> = std::result::Result<T, VmErr>;

impl VM {
    pub fn new() -> Self {
        VM {
            reg: vec![0; 33],
            mem: Memory::new(),
        }
    }

    pub fn setup_stack(&mut self, size: u64) -> Result<()> {
        // We put the stack just below the 4G mark.
        let top = 0xffffffff;
        let base = top - size;
        self.mem
            .mmap_zeroes(Addr(base), Addr(top), PERM_READ | PERM_WRITE)
            .map_err(|e| VmErr::BadAccess(e))?;
        self.set_reg(Sp, top);
        Ok(())
    }

    pub fn setup_heap(&mut self, size: u64) -> Result<Heap> {
        let begin = 1024 * 1024 * 1024 * 3;
        let end = begin + size;
        self.mem
            .create_heap(Addr(begin), Addr(end))
            .map_err(|e| VmErr::BadAccess(e))
    }

    pub fn push(&mut self, v: u64) -> Result<()> {
        let sp = self.reg(Reg::Sp) - 8;
        let bytes = v.to_le_bytes();
        self.mem
            .write(Addr(sp), &bytes, 0)
            .map_err(|e| VmErr::BadAccess(e))?;
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

    pub fn step(&mut self) -> Result<()> {
        let pc = self.pc();
        let mut bits = self
            .mem
            .read_into::<u32>(pc, PERM_EXEC)
            .map_err(|e| VmErr::BadAccess(e))?;

        let (inst, pc_increment) = decode_instr(bits).ok_or(VmErr::DecodeError(bits))?;
        if pc_increment == 2 {
            bits = bits & 0xffff;
        }

        if pc_increment == 2 {
            // Compressed instruction
            eprintln!("{:08x}: {:0>4x}\t{}", pc, bits, inst);
        } else {
            eprintln!("{:08x}: {:0>8x}\t{}", pc, bits, inst);
        }

        use Inst::*;
        match inst {
            LUI { rd, imm } => {
                self.set_reg(rd, (imm << 12) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            AUIPC { rd, imm } => {
                self.set_reg(rd, pc.0.wrapping_add((imm << 12) as i64 as u64));
                self.inc_pc(pc_increment);
            }
            JAL { rd, imm } => {
                let dest = pc.0.wrapping_add(imm as i64 as u64);
                let ret = pc.0.wrapping_add(4);

                self.set_reg(PC, dest);
                self.set_reg(rd, ret);
            }
            JALR { rd, rs, imm } => {
                let dest = self.reg(rs).wrapping_add(imm as i64 as u64);
                let ret = pc.0.wrapping_add(4);

                self.set_reg(rd, ret);
                self.set_reg(PC, dest);
            }
            BEQ { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) == self.reg(rs2), dest, pc_increment);
            }
            BNE { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) != self.reg(rs2), dest, pc_increment);
            }
            BLT { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(
                    (self.reg(rs1) as i64) < (self.reg(rs2) as i64),
                    dest,
                    pc_increment,
                );
            }
            BGE { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(
                    (self.reg(rs1) as i64) >= (self.reg(rs2) as i64),
                    dest,
                    pc_increment,
                );
            }
            BLTU { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) < self.reg(rs2), dest, pc_increment);
            }
            BGEU { rs1, rs2, imm } => {
                let dest = self.pc().0.wrapping_add(imm as i64 as u64);
                self.branch(self.reg(rs1) >= self.reg(rs2), dest, pc_increment);
            }
            LB { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 1];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, i8::from_le_bytes(bytes) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            LH { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 2];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, i16::from_le_bytes(bytes) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            LW { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 4];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, i32::from_le_bytes(bytes) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            LD { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 8];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, i64::from_le_bytes(bytes) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            LBU { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 1];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, u8::from_le_bytes(bytes) as u64);
                self.inc_pc(pc_increment);
            }
            LHU { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 2];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, u16::from_le_bytes(bytes) as u64);
                self.inc_pc(pc_increment);
            }
            LWU { rd, rs, imm } => {
                let src = Addr(self.reg(rs).wrapping_add(imm as i64 as u64));
                let mut bytes = [0u8; 4];
                self.mem
                    .read(src, &mut bytes, PERM_READ)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.set_reg(rd, u32::from_le_bytes(bytes) as u64);
                self.inc_pc(pc_increment);
            }
            SB { rs1, rs2, imm } => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2) as u8;
                let bytes = v.to_le_bytes();
                self.mem
                    .write(dest, &bytes, 0)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.inc_pc(pc_increment);
            }
            SH { rs1, rs2, imm } => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2) as u16;
                let bytes = v.to_le_bytes();
                self.mem
                    .write(dest, &bytes, 0)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.inc_pc(pc_increment);
            }
            SW { rs1, rs2, imm} => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2) as u32;
                let bytes = v.to_le_bytes();
                self.mem
                    .write(dest, &bytes, 0)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.inc_pc(pc_increment);
            }
            SD { rs1, rs2, imm} => {
                let dest = Addr(self.reg(rs1).wrapping_add(imm as i64 as u64));
                let v = self.reg(rs2);
                let bytes = v.to_le_bytes();
                self.mem
                    .write(dest, &bytes, 0)
                    .map_err(|e| VmErr::BadAccess(e))?;
                self.inc_pc(pc_increment);
            }
            ADDI { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs).wrapping_add(imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            SLTI { rd, rs, imm } => {
                let v = if (self.reg(rs) as i64) < (imm as i64) {
                    1
                } else {
                    0
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            SLTIU { rd, rs, imm } => {
                let v = if (self.reg(rs) as u64) < (imm as u64) {
                    1
                } else {
                    0
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            XORI { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs) ^ (imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            ORI { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs) | (imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            ANDI { rd, rs, imm } => {
                self.set_reg(rd, self.reg(rs) & (imm as i64 as u64));
                self.inc_pc(pc_increment);
            }
            SLLI { rd, rs, shamt } => {
                self.set_reg(rd, self.reg(rs) << shamt);
                self.inc_pc(pc_increment);
            }
            SRLI { rd, rs, shamt } => {
                self.set_reg(rd, self.reg(rs) >> shamt);
                self.inc_pc(pc_increment);
            }
            SRAI { rd, rs, shamt } => {
                self.set_reg(rd, ((self.reg(rs) as i64) >> shamt) as u64);
                self.inc_pc(pc_increment);
            }
            ADD { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1).wrapping_add(self.reg(rs2)));
                self.inc_pc(pc_increment);
            }
            SUB { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1).wrapping_sub(self.reg(rs2)));
                self.inc_pc(pc_increment);
            }
            SLL { rd, rs1, rs2 } => {
                let shamt = self.reg(rs2) & 0b111111;
                self.set_reg(rd, self.reg(rs1) << shamt);
                self.inc_pc(pc_increment);
            }
            SLT { rd, rs1, rs2 } => {
                let v = if (self.reg(rs1) as i64) < (self.reg(rs2) as i64) {
                    1
                } else {
                    0
                };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            SLTU { rd, rs1, rs2 } => {
                let v = if self.reg(rs1) < self.reg(rs2) { 1 } else { 0 };
                self.set_reg(rd, v);
                self.inc_pc(pc_increment);
            }
            XOR { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1) ^ self.reg(rs2));
                self.inc_pc(pc_increment);
            }
            SRL { rd, rs1, rs2 } => {
                let shamt = self.reg(rs2) & 0b111111;
                self.set_reg(rd, self.reg(rs1) >> shamt);
                self.inc_pc(pc_increment);
            }
            SRA { rd, rs1, rs2 } => {
                let shamt = self.reg(rs2) & 0b111111;
                self.set_reg(rd, ((self.reg(rs1) as i64) >> shamt) as u64);
                self.inc_pc(pc_increment);
            }
            OR { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1) | self.reg(rs2));
                self.inc_pc(pc_increment);
            }
            AND { rd, rs1, rs2 } => {
                self.set_reg(rd, self.reg(rs1) & self.reg(rs2));
                self.inc_pc(pc_increment);
            }
            ANDIW { rd, rs, imm } => {
                let rs = self.reg(rs) as i32;
                self.set_reg(rd, rs.wrapping_add(imm) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SLLIW { rd, rs, shamt } => {
                let rs = self.reg(rs) as i32;
                self.set_reg(rd, (rs << shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SRLIW { rd, rs, shamt } => {
                let rs = self.reg(rs) as i32;
                self.set_reg(rd, (rs >> shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SRAIW { rd, rs, shamt } => {
                let rs = self.reg(rs) as i32;
                self.set_reg(rd, ((rs as i32) >> shamt) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            ADDW { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                self.set_reg(rd, rs1.wrapping_add(rs2) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SUBW { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                self.set_reg(rd, rs1.wrapping_sub(rs2) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SLLW { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let shamt = rs2 & 0b11111;
                self.set_reg(rd, (rs1 << shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SRLW { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let shamt = rs2 & 0b11111;
                self.set_reg(rd, (rs1 >> shamt) as i32 as i64 as u64);
                self.inc_pc(pc_increment);
            }
            SRAW { rd, rs1, rs2 } => {
                let rs1 = self.reg(rs1) as u32;
                let rs2 = self.reg(rs2) as u32;
                let shamt = rs2 & 0b11111;
                self.set_reg(rd, ((rs1 as i32) >> shamt) as i64 as u64);
                self.inc_pc(pc_increment);
            }
            FENCE {} => {
                self.inc_pc(pc_increment);
            }
            FENCEI {} => {
                self.inc_pc(pc_increment);
            }
            _ => {
                return Err(VmErr::UnimplementedInstruction(inst));
            }
        }

        Ok(())
    }

    pub fn run(&mut self) -> Result<()> {
        loop {
            self.step()?;
        }
    }
}

//------------------------
