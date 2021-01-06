use crate::memory::*;
use thiserror::Error;

use std::fmt;

//------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Reg {
    Zero = 0,
    Ra,
    Sp,
    Gp,
    Tp,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
    PC,
}

impl From<u32> for Reg {
    fn from(v: u32) -> Self {
        assert!(v < 33);
        unsafe { core::ptr::read_unaligned(&(v as usize) as *const usize as *const Reg) }
    }
}

// Extracts the register from an instruction, pass in the first/lowest
// bit of the register field.
fn reg_at(inst: u32, bit: usize) -> Reg {
    Reg::from((inst >> bit) & 0b11111)
}

use Reg::*;

pub struct VM {
    reg: Vec<u64>,
    pub mem: Memory,
}

impl fmt::Display for VM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f,
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
        self.reg(PC))
    }
}

#[derive(Error, Debug)]
pub enum VmErr {
    // FIXME: rename to MemoryError
    #[error("Bad memory access: {0:?}")]
    BadAccess(MemErr),

    #[error("Unknown instruction")]
    UnknownInstruction,

    #[error("ecall")]
    ECall,

    #[error("ebreak")]
    EBreak,
}

pub type Result<T> = std::result::Result<T, VmErr>;

/// There are 6 instruction encodings (see spec 2.3)
struct RType {
    rd: Reg,
    rs1: Reg,
    rs2: Reg,

    func7: u32,
    func3: u32,
}

impl From<u32> for RType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let rs1 = reg_at(inst, 15);
        let rs2 = reg_at(inst, 20);
        let func7 = (inst >> 25) & 0b1111111;
        let func3 = (inst >> 12) & 0b111;

        RType { rd, rs1, rs2, func7, func3 }
    }
}

struct IType {
    rd: Reg,
    rs: Reg,

    imm: i32,
    func: u32,
}

impl From<u32> for IType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let rs = reg_at(inst, 15);
        let imm = (inst as i32) >> 20;
        let func = ((inst >> 12) & 0b111) as u32;

        IType { rd, rs, imm, func }
    }
}

struct SType {
    rs1: Reg,
    rs2: Reg,

    imm: i32,
    func: u32,
}

impl From<u32> for SType {
    fn from(inst: u32) -> Self {
        let rs1 = reg_at(inst, 15);
        let rs2 = reg_at(inst, 20);
        let func = (inst >> 12) & 0b111;
        let imm_11_5 = (inst >> 25) & 0b1111111;
        let imm_4_0 = (inst >> 7) & 0b11111;
        let imm = (imm_11_5 << 5) | imm_4_0;
        let imm = (imm as i32) << 20 >> 20;

        SType {
            rs1,
            rs2,
            imm,
            func,
        }
    }
}

struct BType {
    rs1: Reg,
    rs2: Reg,

    imm: i32,
    func: u32,
}

impl From<u32> for BType {
    fn from(inst: u32) -> Self {
        let rs1 = reg_at(inst, 15);
        let rs2 = reg_at(inst, 20);

        let func = (inst >> 21) & 0b111;
        let imm_12 = (inst >> 31) & 0b1;
        let imm_10_5 = (inst >> 25) & 0b111111;
        let imm_4_1 = (inst >> 8) & 0b1111;
        let imm_11 = (inst >> 7) & 0b1;
        let imm = (imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1);
        let imm = ((imm as i32) << 19) >> 19;

        BType {
            rs1,
            rs2,
            imm,
            func,
        }
    }
}

struct UType {
    rd: Reg,
    imm: i32,
}

impl From<u32> for UType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let imm = ((inst as i32) >> 12) << 12;

        assert!(imm == ((inst & !0xfff) as i32));

        UType { rd, imm }
    }
}

struct JType {
    rd: Reg,
    imm: i32,
}

impl From<u32> for JType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);
        let imm_20 = (inst >> 31) & 0b1;
        let imm_10_1 = (inst >> 21) & 0b1111111111;
        let imm_11 = (inst >> 20) & 0b1;
        let imm_19_12 = (inst >> 12) & 0b11111111;

        let imm = (imm_20 << 20) | (imm_19_12 << 12) | (imm_11 << 11) | (imm_10_1 << 1);
        let imm = ((imm as i32) << 11) >> 11;

        JType { rd, imm }
    }
}

impl VM {
    pub fn new() -> Self {
        VM {
            reg: vec![0; 33],
            mem: Memory::new(),
        }
    }

    pub fn setup_stack(&mut self, size: u64) -> Result<()> {
        /*
        // Let's put the stack right at the top of the address space
        // FIXME: we need to sort out a proper allocator
        self.set_reg(Sp, self.mem.len() as u64);

        // Set read/write permissions for the whole stack
        self.mem.set_perms(Addr(self.mem.len() - size), size, PERM_READ | PERM_WRITE).map_err(|e| VmErr::BadAccess(e))?;
        Ok(())
        */
        todo!();
    }

    pub fn push(&mut self, v: u64) -> Result<()> {
        let sp = self.reg(Reg::Sp) - 8;
        let bytes = v.to_le_bytes();
        self.mem.write(Addr(sp), &bytes, 0).map_err(|e| VmErr::BadAccess(e))?;
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

    pub fn inc_pc(&mut self) {
        self.reg[PC as usize] = self.pc().0.wrapping_add(4);
    }

    pub fn pc(&self) -> Addr {
        Addr(self.reg[PC as usize])
    }

    pub fn step(&mut self) -> Result<()> {
        let pc = self.pc();
        let inst = self
            .mem
            .read_into::<u32>(pc, PERM_EXEC)
            .map_err(|e| VmErr::BadAccess(e))?;
        eprintln!("{pc:08x}: {inst:08x}", pc = pc, inst = inst);

        // Opcode is in the first 7 bits of the instruction
        let opcode = inst & 0b1111111;

        match opcode {
            0b0110111 => {
                // LUI
                let inst = UType::from(inst);
                self.set_reg(inst.rd, inst.imm as i64 as u64);
                self.inc_pc();
            }
            0b0010111 => {
                // AUIPC
                let inst = UType::from(inst);
                self.set_reg(inst.rd, pc.0.wrapping_add(inst.imm as i64 as u64));
                self.inc_pc();
            }
            0b1101111 => {
                // JAL
                let inst = JType::from(inst);
                let dest = pc.0.wrapping_add(inst.imm as i64 as u64);
                let ret = pc.0.wrapping_add(4);

                assert!((dest & 3) == 0);
                self.set_reg(PC, dest);
                self.set_reg(inst.rd, ret);
            }
            0b1100111 => {
                let inst = IType::from(inst);
                match inst.func {
                    0b000 => {
                        // JALR
                        let dest = self.reg(inst.rs).wrapping_add(inst.imm as i64 as u64);
                        let ret = pc.0.wrapping_add(4);

                        assert!((dest & 3) == 0);
                        self.set_reg(inst.rd, ret);
                        self.set_reg(PC, dest);
                    }
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
            }
            0b1100011 => {
                // Conditional branches
                let inst = BType::from(inst);
                let dest = self.pc().0.wrapping_add(inst.imm as i64 as u64);
                assert!((dest & 3) == 0);
                let rs1 = inst.rs1;
                let rs2 = inst.rs2;

                let pred = match inst.func {
                    0b000 => rs1 == rs2,                   // BEQ
                    0b001 => rs1 != rs2,                   // BNE
                    0b100 => (rs1 as i64) < (rs2 as i64),  // BLT
                    0b101 => (rs1 as i64) >= (rs2 as i64), // BGE
                    0b110 => (rs1 as u64) < (rs2 as u64),  // BLTU
                    0b111 => (rs1 as u64) >= (rs2 as u64), // BGEU
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                };

                if pred {
                    self.set_reg(PC, dest);
                } else {
                    self.inc_pc();
                }
            }
            0b0000011 => {
                // Loads
                let inst = IType::from(inst);
                let src = Addr(self.reg(inst.rs).wrapping_add(inst.imm as i64 as u64));

                match inst.func {
                    0b000 => {
                        // LB
                        let mut bytes = [0u8; 1];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, i8::from_le_bytes(bytes) as i64 as u64);
                    }
                    0b001 => {
                        // LH
                        let mut bytes = [0u8; 2];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, i16::from_le_bytes(bytes) as i64 as u64);
                    }
                    0b010 => {
                        // LW
                        let mut bytes = [0u8; 4];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, i32::from_le_bytes(bytes) as i64 as u64);
                    }
                    0b011 => {
                        // LD
                        eprintln!("in LD, rs = {:?}, imm = {}, src = {:?}", inst.rs, inst.imm, src);
                        let mut bytes = [0u8; 8];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, i64::from_le_bytes(bytes) as i64 as u64);
                    }
                    0b100 => {
                        // LBU
                        let mut bytes = [0u8; 1];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, u8::from_le_bytes(bytes) as u64);
                    }
                    0b101 => {
                        // LHU
                        let mut bytes = [0u8; 2];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, u16::from_le_bytes(bytes) as u64);
                    }
                    0b110 => {
                        // LWU
                        let mut bytes = [0u8; 4];
                        self.mem
                            .read(src, &mut bytes, PERM_READ)
                            .map_err(|e| VmErr::BadAccess(e))?;
                        self.set_reg(inst.rd, u32::from_le_bytes(bytes) as u64);
                    }
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
                self.inc_pc();
            }
            0b0100011 => {
                // Stores
                let inst = SType::from(inst);
                let dest = Addr(self.reg(inst.rs1).wrapping_add(inst.imm as i64 as u64));
                
                match inst.func {
                    0b000 => {
                        // SB
                        let v = self.reg(inst.rs2) as u8;
                        let bytes = v.to_le_bytes();
                        self.mem.write(dest, &bytes, 0).map_err(|e| VmErr::BadAccess(e))?;
                    }
                    0b001 => {
                        // SH
                        let v = self.reg(inst.rs2) as u16;
                        let bytes = v.to_le_bytes();
                        self.mem.write(dest, &bytes, 0).map_err(|e| VmErr::BadAccess(e))?;
                    }
                    0b010 => {
                        // SW
                        let v = self.reg(inst.rs2) as u32;
                        let bytes = v.to_le_bytes();
                        self.mem.write(dest, &bytes, 0).map_err(|e| VmErr::BadAccess(e))?;
                    }
                    0b011 => {
                        // SD
                        let v = self.reg(inst.rs2);
                        let bytes = v.to_le_bytes();
                        self.mem.write(dest, &bytes, 0).map_err(|e| VmErr::BadAccess(e))?;
                    }
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
                self.inc_pc();
            }
            0b0010011 => {
                // Immediate arithmetic
                let inst = IType::from(inst);
                let rd = inst.rd;
                let rs = self.reg(inst.rs);
                let imm = inst.imm as i64 as u64;
                
                match inst.func {
                    0b000 => {
                        // ADDI
                        self.set_reg(rd, rs.wrapping_add(imm));
                    }
                    0b010 => {
                        // SLTI
                        let v = if (rs as i64) < (imm as i64) { 1 } else { 0 };
                        self.set_reg(rd, v);
                    }
                    0b011 => {
                        // SLTIU
                        let v = if (rs as u64) < (imm as u64) { 1 } else { 0 };
                        self.set_reg(rd, v);
                    }
                    0b100 => {
                        // XORI
                        self.set_reg(rd, rs ^ imm);
                    }
                    0b110 => {
                        // ORI
                        self.set_reg(rd, rs | imm);
                    }
                    0b111 => {
                        // ANDI
                        self.set_reg(rd, rs & imm);
                    }
                    0b001 => {
                        let mode = (inst.imm >> 6) & 0b111111;
                        match mode {
                            0b000000 => {
                                // SLLI
                                let shamt = inst.imm & 0b111111;
                                self.set_reg(rd, rs << shamt);
                            }
                            _ => {
                                return Err(VmErr::UnknownInstruction);
                            }
                       }
                    }
                    0b101 => {
                        let mode = (inst.imm >> 6) & 0b111111;
                        match mode {
                            0b000000 => {
                                // SRLI
                                let shamt = inst.imm & 0b111111;
                                self.set_reg(rd, rs >> shamt);
                            }
                            0b010000 => {
                                // SRAI
                                let shamt = inst.imm & 0b111111;
                                self.set_reg(rd, ((rs as i64) >> shamt) as u64);
                            }
                            _ => {
                                return Err(VmErr::UnknownInstruction);
                            }
                        }
                    }
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
                self.inc_pc();
            }
            0b0110011 => {
                // Register arithmetic
                let inst = RType::from(inst);
                let rd = inst.rd;
                let rs1 = self.reg(inst.rs1);
                let rs2 = self.reg(inst.rs2);

                match (inst.func7, inst.func3) {
                    (0b0000000, 0b000) => {
                        // ADD
                        self.set_reg(rd, rs1.wrapping_add(rs2));
                    }
                    (0b0100000, 0b000) => {
                        // SUB
                        self.set_reg(rd, rs1.wrapping_sub(rs2));
                    }
                    (0b0000000, 0b001) => {
                        // SLL
                        let shamt = rs2 & 0b111111;
                        self.set_reg(rd, rs1 << shamt);
                    }
                    (0b0000000, 0b010) => {
                        // SLT
                        let v = if (rs1 as i64) < (rs2 as i64) { 1 } else { 0 };
                        self.set_reg(rd, v);
                    }
                    (0b0000000, 0b011) => {
                        // SLTU
                        let v = if rs1 < rs2 { 1 } else { 0 };
                        self.set_reg(rd, v);
                    }
                    (0b0000000, 0b100) => {
                        // XOR
                        self.set_reg(rd, rs1 ^ rs2);
                    }
                    (0b0000000, 0b101) => {
                        // SRL
                        let shamt = rs2 & 0b111111;
                        self.set_reg(rd, rs1 >> shamt);
                    }
                    (0b0100000, 0b101) => {
                        // SRA
                        let shamt = rs2 & 0b111111;
                        self.set_reg(rd, ((rs1 as i64) >> shamt) as u64);
                    }
                    (0b0000000, 0b110) => {
                        // OR
                        self.set_reg(rd, rs1 | rs2);
                    }
                    (0b0000000, 0b111) => {
                        // AND
                        self.set_reg(rd, rs1 & rs2);
                    }

                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
                self.inc_pc();
            }
            0b0011011 => {
                let inst = IType::from(inst);
                let rd = inst.rd;
                let rs = self.reg(inst.rs) as i32;
                let imm = inst.imm;
                match inst.func {
                    0b000 => {
                        // ADDIW
                        self.set_reg(rd, rs.wrapping_add(imm) as i32 as i64 as u64);
                    }
                    0b001 => {
                        let mode = (inst.imm >> 5) & 0b1111111;
                        match mode {
                            0b0000000 => {
                                // SLLIW
                                let shamt = imm & 0b11111;
                                self.set_reg(rd, (rs << shamt) as i32 as i64 as u64);
                            }
                            _ => {
                                return Err(VmErr::UnknownInstruction);
                            }
                        }
                    }
                    0b101 => {
                        let mode = (inst.imm >> 5) & 0b1111111;
                        let shamt = imm & 0b11111;
                        match mode {
                            0b0000000 => {
                                // SRLIW
                                self.set_reg(rd, (rs >> shamt) as i32 as i64 as u64);
                            }
                            0b0100000 => {
                                // SRAIW
                                self.set_reg(rd, ((rs as i32) >> shamt) as i64 as u64);
                            }
                            _ => {
                                return Err(VmErr::UnknownInstruction);
                            }
                        }
                    }
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
                self.inc_pc();
            }
            0b0111011 => {
                let inst = RType::from(inst);
                let rd = inst.rd;
                let rs1 = self.reg(inst.rs1) as u32;
                let rs2 = self.reg(inst.rs2) as u32;
                match (inst.func7, inst.func3) {
                    (0b0000000, 0b000) => {
                        // ADDW
                        self.set_reg(rd, rs1.wrapping_add(rs2) as i32 as i64 as u64);
                    }
                    (0b0100000, 0b000) => {
                        // SUBW
                        self.set_reg(rd, rs1.wrapping_sub(rs2) as i32 as i64 as u64);
                    }
                    (0b0000000, 0b001) => {
                        // SLLW
                        let shamt = rs2 & 0b11111;
                        self.set_reg(rd, (rs1 << shamt) as i32 as i64 as u64);
                    }
                    (0b0000000, 0b101) => {
                        // SRLW
                        let shamt = rs2 & 0b11111;
                        self.set_reg(rd, (rs1 >> shamt) as i32 as i64 as u64);
                    }
                    (0b0100000, 0b101) => {
                        // SRAW
                        let shamt = rs2 & 0b11111;
                        self.set_reg(rd, ((rs1 as i32) >> shamt) as i64 as u64);
                    }
                    _ => {
                        return Err(VmErr::UnknownInstruction);
                    }
                }
                self.inc_pc();
            }
            0b0001111 => {
                // Fence
                self.inc_pc();
            }
            0b1110011 => {
                // Environment
                todo!();
            }
            _ => {
                return Err(VmErr::UnknownInstruction);
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
