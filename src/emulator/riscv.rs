use byteorder::{LittleEndian, ReadBytesExt};
use log::*;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt;
use std::io::Cursor;
use std::rc::Weak;

use crate::emulator::ir::ir::IR;

//-------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Reg::*;
        match self {
            Zero => write!(f, "zero"),
            Ra => write!(f, "ra"),
            Sp => write!(f, "sp"),
            Gp => write!(f, "gp"),
            Tp => write!(f, "tp"),
            T0 => write!(f, "t0"),
            T1 => write!(f, "t1"),
            T2 => write!(f, "t2"),
            S0 => write!(f, "s0"),
            S1 => write!(f, "s1"),
            A0 => write!(f, "a0"),
            A1 => write!(f, "a1"),
            A2 => write!(f, "a2"),
            A3 => write!(f, "a3"),
            A4 => write!(f, "a4"),
            A5 => write!(f, "a5"),
            A6 => write!(f, "a6"),
            A7 => write!(f, "a7"),
            S2 => write!(f, "s2"),
            S3 => write!(f, "s3"),
            S4 => write!(f, "s4"),
            S5 => write!(f, "s5"),
            S6 => write!(f, "s6"),
            S7 => write!(f, "s7"),
            S8 => write!(f, "s8"),
            S9 => write!(f, "s9"),
            S10 => write!(f, "s10"),
            S11 => write!(f, "s11"),
            T3 => write!(f, "t3"),
            T4 => write!(f, "t4"),
            T5 => write!(f, "t5"),
            T6 => write!(f, "t6"),
            PC => write!(f, "pc"),
        }
    }
}

impl From<u32> for Reg {
    fn from(v: u32) -> Self {
        assert!(v < 33);
        unsafe { core::ptr::read_unaligned(&(v as usize) as *const usize as *const Reg) }
    }
}

/// Extracts the register from an instruction, pass in the first/lowest
/// bit of the register field.
fn reg_at(inst: u32, bit: usize) -> Reg {
    Reg::from((inst >> bit) & 0b11111)
}

/// Extracts a register from a _compressed_ bit field. pass in the first/lowest
/// bit of the field.
fn creg_at(bits: u16, bit: usize) -> Reg {
    Reg::from((((bits >> bit) & 0b111) + 8) as u32)
}

/// Sign extends a given number of bits.
fn sign_extend(x: i32, nbits: u32) -> i32 {
    let n = std::mem::size_of_val(&x) as u32 * 8 - nbits - 1;
    x.wrapping_shl(n).wrapping_shr(n)
}

#[derive(Clone, Copy, Debug)]
pub enum Inst {
    Lui { rd: Reg, imm: i32 },
    Auipc { rd: Reg, imm: i32 },

    Jal { rd: Reg, imm: i32 },
    Jalr { rd: Reg, rs: Reg, imm: i32 },

    Beq { rs1: Reg, rs2: Reg, imm: i32 },
    Bne { rs1: Reg, rs2: Reg, imm: i32 },
    Blt { rs1: Reg, rs2: Reg, imm: i32 },
    Bge { rs1: Reg, rs2: Reg, imm: i32 },
    Bltu { rs1: Reg, rs2: Reg, imm: i32 },
    Bgeu { rs1: Reg, rs2: Reg, imm: i32 },

    Lb { rd: Reg, rs: Reg, imm: i32 },
    Lh { rd: Reg, rs: Reg, imm: i32 },
    Lw { rd: Reg, rs: Reg, imm: i32 },
    Lwu { rd: Reg, rs: Reg, imm: i32 },
    Ld { rd: Reg, rs: Reg, imm: i32 },

    Lbu { rd: Reg, rs: Reg, imm: i32 },
    Lhu { rd: Reg, rs: Reg, imm: i32 },

    Sb { rs1: Reg, rs2: Reg, imm: i32 },
    Sh { rs1: Reg, rs2: Reg, imm: i32 },
    Sw { rs1: Reg, rs2: Reg, imm: i32 },
    Sd { rs1: Reg, rs2: Reg, imm: i32 },

    Addi { rd: Reg, rs: Reg, imm: i32 },
    Addiw { rd: Reg, rs: Reg, imm: i32 },
    Slti { rd: Reg, rs: Reg, imm: i32 },
    Sltiu { rd: Reg, rs: Reg, imm: i32 },
    Xori { rd: Reg, rs: Reg, imm: i32 },
    Ori { rd: Reg, rs: Reg, imm: i32 },
    Andi { rd: Reg, rs: Reg, imm: i32 },
    Slli { rd: Reg, rs: Reg, shamt: i32 },
    Slliw { rd: Reg, rs: Reg, shamt: u32 },
    Srli { rd: Reg, rs: Reg, shamt: u32 },
    Srliw { rd: Reg, rs: Reg, shamt: u32 },
    Sraiw { rd: Reg, rs: Reg, shamt: u32 },
    Srai { rd: Reg, rs: Reg, shamt: u32 },

    Add { rd: Reg, rs1: Reg, rs2: Reg },
    Addw { rd: Reg, rs1: Reg, rs2: Reg },
    Sub { rd: Reg, rs1: Reg, rs2: Reg },
    Subw { rd: Reg, rs1: Reg, rs2: Reg },
    Sll { rd: Reg, rs1: Reg, rs2: Reg },
    Sllw { rd: Reg, rs1: Reg, rs2: Reg },
    Srlw { rd: Reg, rs1: Reg, rs2: Reg },
    Sraw { rd: Reg, rs1: Reg, rs2: Reg },
    Slt { rd: Reg, rs1: Reg, rs2: Reg },
    Sltu { rd: Reg, rs1: Reg, rs2: Reg },

    Xor { rd: Reg, rs1: Reg, rs2: Reg },
    Srl { rd: Reg, rs1: Reg, rs2: Reg },
    Sra { rd: Reg, rs1: Reg, rs2: Reg },
    Or { rd: Reg, rs1: Reg, rs2: Reg },
    And { rd: Reg, rs1: Reg, rs2: Reg },

    // mul
    Mul { rd: Reg, rs1: Reg, rs2: Reg },
    Mulh { rd: Reg, rs1: Reg, rs2: Reg },
    Mulhsu { rd: Reg, rs1: Reg, rs2: Reg },
    Mulhu { rd: Reg, rs1: Reg, rs2: Reg },
    Mulw { rd: Reg, rs1: Reg, rs2: Reg },
    Div { rd: Reg, rs1: Reg, rs2: Reg },
    Divu { rd: Reg, rs1: Reg, rs2: Reg },
    Divw { rd: Reg, rs1: Reg, rs2: Reg },
    Divuw { rd: Reg, rs1: Reg, rs2: Reg },
    Rem { rd: Reg, rs1: Reg, rs2: Reg },
    Remu { rd: Reg, rs1: Reg, rs2: Reg },
    Remw { rd: Reg, rs1: Reg, rs2: Reg },
    Remuw { rd: Reg, rs1: Reg, rs2: Reg },

    Fence,
    Fencei,

    Ecall,
    Ebreak,

    // atomics
    Lrw { rd: Reg, rs: Reg },
    Scw { rd: Reg, rs1: Reg, rs2: Reg },
    Amoswapw { rd: Reg, rs1: Reg, rs2: Reg },
    Amoaddw { rd: Reg, rs1: Reg, rs2: Reg },
    Amoxorw { rd: Reg, rs1: Reg, rs2: Reg },
    Amoandw { rd: Reg, rs1: Reg, rs2: Reg },
    Amoorw { rd: Reg, rs1: Reg, rs2: Reg },
    Amominw { rd: Reg, rs1: Reg, rs2: Reg },
    Amomaxw { rd: Reg, rs1: Reg, rs2: Reg },
    Amominuw { rd: Reg, rs1: Reg, rs2: Reg },
    Amomaxuw { rd: Reg, rs1: Reg, rs2: Reg },
    Lrd { rd: Reg, rs: Reg },
    Scd { rd: Reg, rs1: Reg, rs2: Reg },
    Amoswapd { rd: Reg, rs1: Reg, rs2: Reg },
    Amoaddd { rd: Reg, rs1: Reg, rs2: Reg },
    Amoxord { rd: Reg, rs1: Reg, rs2: Reg },
    Amoandd { rd: Reg, rs1: Reg, rs2: Reg },
    Amoord { rd: Reg, rs1: Reg, rs2: Reg },
    Amomind { rd: Reg, rs1: Reg, rs2: Reg },
    Amomaxd { rd: Reg, rs1: Reg, rs2: Reg },
    Amominud { rd: Reg, rs1: Reg, rs2: Reg },
    Amomaxud { rd: Reg, rs1: Reg, rs2: Reg },
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Inst::*;
        use Reg::*;

        match self {
            Lui { rd, imm } => write!(f, "lui\t{},0x{:x}", rd, imm),
            Auipc { rd, imm } => write!(f, "auipc\t{},0x{:x}", rd, imm),

            Jal { rd, imm } => write!(f, "jal\t{},0x{:x}", rd, imm),
            Jalr { rd, rs, imm } => {
                if *rd == Zero && *rs == Ra && *imm == 0 {
                    write!(f, "ret")
                } else {
                    write!(f, "jalr\t{},{},0x{:x}", rd, rs, imm)
                }
            }

            Beq { rs1, rs2, imm } => {
                if *rs2 == Zero {
                    write!(f, "beqz\t{},{}", rs1, imm)
                } else {
                    write!(f, "beq\t{},{},{}", rs1, rs2, imm)
                }
            }
            Bne { rs1, rs2, imm } => write!(f, "bne\t{},{},{}", rs1, rs2, imm),
            Blt { rs1, rs2, imm } => write!(f, "blt\t{},{},{}", rs1, rs2, imm),
            Bge { rs1, rs2, imm } => write!(f, "bge\t{},{},{}", rs1, rs2, imm),
            Bltu { rs1, rs2, imm } => write!(f, "bltu\t{},{},{}", rs1, rs2, imm),
            Bgeu { rs1, rs2, imm } => write!(f, "bgeu\t{},{},{}", rs1, rs2, imm),

            Lb { rd, rs, imm } => write!(f, "lb\t{},{}({})", rd, imm, rs),
            Lh { rd, rs, imm } => write!(f, "lh\t{},{}({})", rd, imm, rs),
            Lw { rd, rs, imm } => write!(f, "lw\t{},{}({})", rd, imm, rs),
            Lwu { rd, rs, imm } => write!(f, "lwu\t{},{}({})", rd, imm, rs),
            Ld { rd, rs, imm } => write!(f, "ld\t{},{}({})", rd, imm, rs),

            Lbu { rd, rs, imm } => write!(f, "lbu\t{},{}({})", rd, imm, rs),
            Lhu { rd, rs, imm } => write!(f, "lhu\t{},{}({})", rd, imm, rs),

            Sb { rs1, rs2, imm } => write!(f, "sb\t{},{}({})", rs2, imm, rs1),
            Sh { rs1, rs2, imm } => write!(f, "sh\t{},{}({})", rs2, imm, rs1),
            Sw { rs1, rs2, imm } => write!(f, "sw\t{},{}({})", rs2, imm, rs1),
            Sd { rs1, rs2, imm } => write!(f, "sd\t{},{}({})", rs2, imm, rs1),

            Addi { rd, rs, imm } => {
                if *rs == Zero {
                    write!(f, "li\t{},{}", rd, imm)
                } else {
                    write!(f, "addi\t{},{},{}", rd, rs, imm)
                }
            }
            Addiw { rd, rs, imm } => write!(f, "addiw\t{},{},{}", rd, rs, imm),
            Slti { rd, rs, imm } => write!(f, "slti\t{},{},{}", rd, rs, imm),
            Sltiu { rd, rs, imm } => write!(f, "sltiu\t{},{},{}", rd, rs, imm),
            Xori { rd, rs, imm } => write!(f, "xori\t{},{},{}", rd, rs, imm),
            Ori { rd, rs, imm } => write!(f, "ori\t{},{},{}", rd, rs, imm),
            Andi { rd, rs, imm } => write!(f, "andi\t{},{},{}", rd, rs, imm),
            Slli { rd, rs, shamt } => write!(f, "slli\t{},{},{}", rd, rs, shamt),
            Slliw { rd, rs, shamt } => write!(f, "slliw\t{},{},{}", rd, rs, shamt),
            Srli { rd, rs, shamt } => write!(f, "srli\t{},{},{}", rd, rs, shamt),
            Srliw { rd, rs, shamt } => write!(f, "srliw\t{},{},{}", rd, rs, shamt),
            Sraiw { rd, rs, shamt } => write!(f, "sraiw\t{},{},{}", rd, rs, shamt),
            Srai { rd, rs, shamt } => write!(f, "srai\t{},{},{}", rd, rs, shamt),

            Add { rd, rs1, rs2 } => {
                if *rs1 == Zero {
                    write!(f, "mv\t{},{}", rd, rs2)
                } else {
                    write!(f, "add\t{},{},{}", rd, rs1, rs2)
                }
            }
            Addw { rd, rs1, rs2 } => write!(f, "addw\t{},{},{}", rd, rs1, rs2),
            Sub { rd, rs1, rs2 } => write!(f, "sub\t{},{},{}", rd, rs1, rs2),
            Subw { rd, rs1, rs2 } => write!(f, "subw\t{},{},{}", rd, rs1, rs2),
            Sll { rd, rs1, rs2 } => write!(f, "sll\t{},{},{}", rd, rs1, rs2),
            Sllw { rd, rs1, rs2 } => write!(f, "sllw\t{},{},{}", rd, rs1, rs2),
            Srlw { rd, rs1, rs2 } => write!(f, "srlw\t{},{},{}", rd, rs1, rs2),
            Sraw { rd, rs1, rs2 } => write!(f, "sraw\t{},{},{}", rd, rs1, rs2),
            Slt { rd, rs1, rs2 } => write!(f, "slt\t{},{},{}", rd, rs1, rs2),
            Sltu { rd, rs1, rs2 } => write!(f, "sltu\t{},{},{}", rd, rs1, rs2),

            Xor { rd, rs1, rs2 } => write!(f, "xor\t{},{},{}", rd, rs1, rs2),
            Srl { rd, rs1, rs2 } => write!(f, "srl\t{},{},{}", rd, rs1, rs2),
            Sra { rd, rs1, rs2 } => write!(f, "sra\t{},{},{}", rd, rs1, rs2),
            Or { rd, rs1, rs2 } => write!(f, "or\t{},{},{}", rd, rs1, rs2),
            And { rd, rs1, rs2 } => write!(f, "and\t{},{},{}", rd, rs1, rs2),

            Mul { rd, rs1, rs2 } => write!(f, "mul\t{},{},{}", rd, rs1, rs2),
            Mulh { rd, rs1, rs2 } => write!(f, "mulh\t{},{},{}", rd, rs1, rs2),
            Mulhsu { rd, rs1, rs2 } => write!(f, "mulhsu\t{},{},{}", rd, rs1, rs2),
            Mulhu { rd, rs1, rs2 } => write!(f, "mulhu\t{},{},{}", rd, rs1, rs2),
            Mulw { rd, rs1, rs2 } => write!(f, "mulw\t{},{},{}", rd, rs1, rs2),
            Div { rd, rs1, rs2 } => write!(f, "div\t{},{},{}", rd, rs1, rs2),
            Divu { rd, rs1, rs2 } => write!(f, "divu\t{},{},{}", rd, rs1, rs2),
            Divw { rd, rs1, rs2 } => write!(f, "divw\t{},{},{}", rd, rs1, rs2),
            Divuw { rd, rs1, rs2 } => write!(f, "divuw\t{},{},{}", rd, rs1, rs2),
            Rem { rd, rs1, rs2 } => write!(f, "rem\t{},{},{}", rd, rs1, rs2),
            Remu { rd, rs1, rs2 } => write!(f, "remu\t{},{},{}", rd, rs1, rs2),
            Remw { rd, rs1, rs2 } => write!(f, "remw\t{},{},{}", rd, rs1, rs2),
            Remuw { rd, rs1, rs2 } => write!(f, "remuw\t{},{},{}", rd, rs1, rs2),

            Fence => write!(f, "fence"),
            Fencei => write!(f, "fence_i"),

            Ecall => write!(f, "ecall"),
            Ebreak => write!(f, "ebreak"),

            Lrw { rd, rs } => write!(f, "lr.w {},{}", rd, rs),
            Scw { rd, rs1, rs2 } => write!(f, "sc.w {},{},({})", rd, rs1, rs2),
            Amoswapw { rd, rs1, rs2 } => write!(f, "amoswap.w {},{},({})", rd, rs1, rs2),
            Amoaddw { rd, rs1, rs2 } => write!(f, "amoadd.w {},{},({})", rd, rs1, rs2),
            Amoxorw { rd, rs1, rs2 } => write!(f, "amoxor.w {},{},({})", rd, rs1, rs2),
            Amoandw { rd, rs1, rs2 } => write!(f, "amoand.w {},{},({})", rd, rs1, rs2),
            Amoorw { rd, rs1, rs2 } => write!(f, "amoor.w {},{},({})", rd, rs1, rs2),
            Amominw { rd, rs1, rs2 } => write!(f, "amomin.w {},{},({})", rd, rs1, rs2),
            Amomaxw { rd, rs1, rs2 } => write!(f, "amomax.w {},{},({})", rd, rs1, rs2),
            Amominuw { rd, rs1, rs2 } => write!(f, "amominu.w {},{},({})", rd, rs1, rs2),
            Amomaxuw { rd, rs1, rs2 } => write!(f, "amomaxu.w {},{},({})", rd, rs1, rs2),
            Lrd { rd, rs } => write!(f, "lr.d {},{}", rd, rs),
            Scd { rd, rs1, rs2 } => write!(f, "sc.d {},{},({})", rd, rs1, rs2),
            Amoswapd { rd, rs1, rs2 } => write!(f, "amoswap.d {},{},({})", rd, rs1, rs2),
            Amoaddd { rd, rs1, rs2 } => write!(f, "amoadd.d {},{},({})", rd, rs1, rs2),
            Amoxord { rd, rs1, rs2 } => write!(f, "amoxor.d {},{},({})", rd, rs1, rs2),
            Amoandd { rd, rs1, rs2 } => write!(f, "amoand.d {},{},({})", rd, rs1, rs2),
            Amoord { rd, rs1, rs2 } => write!(f, "amoor.d {},{},({})", rd, rs1, rs2),
            Amomind { rd, rs1, rs2 } => write!(f, "amomin.d {},{},({})", rd, rs1, rs2),
            Amomaxd { rd, rs1, rs2 } => write!(f, "amomax.d {},{},({})", rd, rs1, rs2),
            Amominud { rd, rs1, rs2 } => write!(f, "amominu.d {},{},({})", rd, rs1, rs2),
            Amomaxud { rd, rs1, rs2 } => write!(f, "amomaxu.d {},{},({})", rd, rs1, rs2),
        }
    }
}

/// There are 6 instruction encodings (see spec 2.3)
#[derive(Debug)]
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

        RType {
            rd,
            rs1,
            rs2,
            func7,
            func3,
        }
    }
}

#[derive(Debug)]
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
        let func = (inst >> 12) & 0b111;

        IType { rd, rs, imm, func }
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
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

        let func = (inst >> 12) & 0b111;
        let imm_12 = (inst >> 31) & 0b1;
        let imm_10_5 = (inst >> 25) & 0b111111;
        let imm_4_1 = (inst >> 8) & 0b1111;
        let imm_11 = (inst >> 7) & 0b1;
        let imm = (imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1);
        let imm = sign_extend(imm as i32, 12);

        BType {
            rs1,
            rs2,
            imm,
            func,
        }
    }
}

#[derive(Debug)]
struct UType {
    rd: Reg,
    imm: i32,
}

impl From<u32> for UType {
    fn from(inst: u32) -> Self {
        let rd = reg_at(inst, 7);

        // We could shift << 12 since the two instructions that
        // use this format (LUI and AUIPC) want that, but then
        // the disassembly will not match objdump.
        let imm = (inst as i32) >> 12;

        UType { rd, imm }
    }
}

#[derive(Debug)]
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

fn decode_32bit_instr(bits: u32) -> Option<Inst> {
    use Inst::*;

    // Opcode is in the first 7 bits of the instruction
    let opcode = bits & 0b1111111;

    let inst = match opcode {
        0b0110111 => {
            let inst = UType::from(bits);
            Lui {
                rd: inst.rd,
                imm: inst.imm,
            }
        }
        0b0010111 => {
            let inst = UType::from(bits);
            Auipc {
                rd: inst.rd,
                imm: inst.imm,
            }
        }
        0b1101111 => {
            let inst = JType::from(bits);
            Jal {
                rd: inst.rd,
                imm: inst.imm,
            }
        }
        0b1100111 => {
            let inst = IType::from(bits);
            match inst.func {
                0b000 => Jalr {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b1100011 => {
            // Conditional branches
            let inst = BType::from(bits);

            match inst.func {
                0b000 => Beq {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b001 => Bne {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b100 => Blt {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b101 => Bge {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b110 => Bltu {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b111 => Bgeu {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0000011 => {
            // Loads
            let inst = IType::from(bits);
            match inst.func {
                0b000 => Lb {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b001 => Lh {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b010 => Lw {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b011 => Ld {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b100 => Lbu {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b101 => Lhu {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b110 => Lwu {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0100011 => {
            // Stores
            let inst = SType::from(bits);
            match inst.func {
                0b000 => Sb {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b001 => Sh {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b010 => Sw {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                0b011 => Sd {
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                    imm: inst.imm,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0010011 => {
            // Immediate arithmetic
            let inst = IType::from(bits);
            match inst.func {
                0b000 => Addi {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b010 => Slti {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b011 => Sltiu {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b100 => Xori {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b110 => Ori {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b111 => Andi {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b001 => {
                    let mode = (inst.imm >> 6) & 0b111111;
                    let shamt = inst.imm & 0b111111;
                    match mode {
                        0b000000 => Slli {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                0b101 => {
                    let mode = (inst.imm >> 6) & 0b111111;
                    let shamt = inst.imm & 0b111111;
                    match mode {
                        0b000000 => Srli {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt: shamt as u32,
                        },
                        0b010000 => Srai {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt: shamt as u32,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                _ => {
                    return None;
                }
            }
        }
        0b0110011 => {
            // Register arithmetic
            let inst = RType::from(bits);
            match (inst.func7, inst.func3) {
                (0b0000000, 0b000) => Add {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b000) => Sub {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b001) => Sll {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b010) => Slt {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b011) => Sltu {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b100) => Xor {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b101) => Srl {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b101) => Sra {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b110) => Or {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b111) => And {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b000) => Mul {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b001) => Mulh {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b010) => Mulhsu {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b011) => Mulhu {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b100) => Div {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b101) => Divu {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b110) => Rem {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b111) => Remu {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0011011 => {
            let inst = IType::from(bits);
            match inst.func {
                0b000 => Addiw {
                    rd: inst.rd,
                    rs: inst.rs,
                    imm: inst.imm,
                },
                0b001 => {
                    let mode = (inst.imm >> 5) & 0b1111111;
                    let shamt = (inst.imm & 0b11111) as u32;
                    match mode {
                        0b0000000 => Slliw {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                0b101 => {
                    let mode = (inst.imm >> 5) & 0b1111111;
                    let shamt = (inst.imm & 0b11111) as u32;
                    match mode {
                        0b0000000 => Srliw {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        0b0100000 => Sraiw {
                            rd: inst.rd,
                            rs: inst.rs,
                            shamt,
                        },
                        _ => {
                            return None;
                        }
                    }
                }
                _ => {
                    return None;
                }
            }
        }
        0b0111011 => {
            let inst = RType::from(bits);
            match (inst.func7, inst.func3) {
                (0b0000000, 0b000) => Addw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b000) => Subw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b001) => Sllw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000000, 0b101) => Srlw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0100000, 0b101) => Sraw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b000) => Mulw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b100) => Divw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b101) => Divuw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b110) => Remw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                (0b0000001, 0b111) => Remuw {
                    rd: inst.rd,
                    rs1: inst.rs1,
                    rs2: inst.rs2,
                },
                _ => {
                    return None;
                }
            }
        }
        0b0001111 => Fence {},
        0b1110011 => {
            if (bits >> 7) == 0 {
                Ecall
            } else if (bits >> 20) == 1 {
                Ebreak
            } else {
                return None;
            }
        }
        0b0101111 => {
            let inst = RType::from(bits);
            match inst.func3 {
                0b010 => match inst.func7 >> 2 {
                    0b00010 => Lrw {
                        rd: inst.rd,
                        rs: inst.rs1,
                    },
                    0b00011 => Scw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00001 => Amoswapw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00000 => Amoaddw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00100 => Amoxorw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01100 => Amoandw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01000 => Amoorw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10000 => Amominw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10100 => Amomaxw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11000 => Amominuw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11100 => Amomaxuw {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    _ => {
                        return None;
                    }
                },
                0b011 => match inst.func7 >> 2 {
                    0b00010 => Lrd {
                        rd: inst.rd,
                        rs: inst.rs1,
                    },
                    0b00011 => Scd {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00001 => Amoswapd {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00000 => Amoaddd {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b00100 => Amoxord {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01100 => Amoandd {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b01000 => Amoord {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10000 => Amomind {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b10100 => Amomaxd {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11000 => Amominud {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    0b11100 => Amomaxud {
                        rd: inst.rd,
                        rs1: inst.rs1,
                        rs2: inst.rs2,
                    },
                    _ => {
                        return None;
                    }
                },
                _ => {
                    return None;
                }
            }
        }
        _ => {
            return None;
        }
    };

    Some(inst)
}

fn decode_16bit_instr(bits: u16) -> Option<Inst> {
    use Inst::*;
    use Reg::*;

    if bits == 0 {
        return None;
    }

    let inst = match bits & 0b11 {
        0b00 => {
            match bits >> 13 {
                0b000 => {
                    // ADDI4SPN
                    let rd = creg_at(bits, 2);
                    let imm_3 = (bits >> 5) & 0b1;
                    let imm_2 = (bits >> 6) & 0b1;
                    let imm_9_6 = (bits >> 7) & 0b1111;
                    let imm_5_4 = (bits >> 11) & 0b11;
                    let imm = (imm_9_6 << 6) | (imm_5_4 << 4) | (imm_3 << 3) | (imm_2 << 2);
                    let imm = sign_extend(imm as i32, 9);
                    Addi { rd, rs: Sp, imm }
                }
                0b010 => {
                    // LW
                    let rd = creg_at(bits, 2);
                    let rs = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_2 = (bits >> 6) & 0b1;
                    let imm_6 = (bits >> 5) & 0b1;
                    let imm = (imm_6 << 6) | (imm_5_3 << 3) | (imm_2 << 2);
                    let imm = imm as i32;
                    Lw { rd, rs, imm }
                }
                0b011 => {
                    // LD
                    let rd = creg_at(bits, 2);
                    let rs = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm = (imm_7_6 << 6) | (imm_5_3 << 3);
                    let imm = imm as i32;
                    Ld { rd, rs, imm }
                }
                0b110 => {
                    // SW
                    let rs2 = creg_at(bits, 2);
                    let rs1 = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_2 = (bits >> 6) & 0b1;
                    let imm_6 = (bits >> 5) & 0b1;
                    let imm = (imm_6 << 6) | (imm_5_3 << 3) | (imm_2 << 2);
                    let imm = imm as i32;
                    Sw { rs1, rs2, imm }
                }
                0b111 => {
                    // SD
                    let rs2 = creg_at(bits, 2);
                    let rs1 = creg_at(bits, 7);
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm = (imm_7_6 << 6) | (imm_5_3 << 3);
                    let imm = imm as i32;
                    Sd { rs1, rs2, imm }
                }
                _ => {
                    return None;
                }
            }
        }
        0b01 => {
            match bits >> 13 {
                0b000 => {
                    // ADDI
                    let rd = reg_at(bits as u32, 7);
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let imm = sign_extend(imm as i32, 5);
                    Addi { rd, rs: rd, imm }
                }
                0b001 => {
                    // ADDIW
                    let rd = reg_at(bits as u32, 7);
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let imm = sign_extend(imm as i32, 5);
                    Addiw { rd, rs: rd, imm }
                }
                0b010 => {
                    // LI
                    let rd = reg_at(bits as u32, 7);
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let imm = sign_extend(imm as i32, 5);
                    Addi { rd, rs: Zero, imm }
                }
                0b011 => {
                    if ((bits >> 7) & 0b11111) == 2 {
                        // ADDI16SP
                        let imm_9 = (bits >> 12) & 0b1;
                        let imm_5 = (bits >> 2) & 0b1;
                        let imm_8_7 = (bits >> 3) & 0b11;
                        let imm_6 = (bits >> 5) & 0b1;
                        let imm_4 = (bits >> 6) & 0b1;
                        let imm = (imm_9 << 9)
                            | (imm_8_7 << 7)
                            | (imm_6 << 6)
                            | (imm_5 << 5)
                            | (imm_4 << 4);
                        let imm = sign_extend(imm as i32, 9);
                        Addi {
                            rd: Sp,
                            rs: Sp,
                            imm,
                        }
                    } else {
                        // LUI
                        let rd = reg_at(bits as u32, 7);
                        let imm_17 = (bits >> 12) & 0b1;
                        let imm_16_12 = (bits >> 2) & 0b11111;
                        let imm = ((imm_17 as u32) << 17) | ((imm_16_12 as u32) << 12);
                        let imm = sign_extend(imm as i32, 17);
                        Lui { rd, imm: imm >> 12 }
                    }
                }
                0b100 => {
                    match (bits >> 10) & 0b11 {
                        0b00 => {
                            // SRLI
                            let rd = creg_at(bits, 7);
                            let imm_5 = (bits >> 12) & 0b1;
                            let imm_4_0 = (bits >> 2) & 0b11111;
                            let imm = (imm_5 << 5) | imm_4_0;
                            let shamt = imm as u32;
                            Srli { rd, rs: rd, shamt }
                        }
                        0b01 => {
                            // SRAI
                            let rd = creg_at(bits, 7);
                            let imm_5 = (bits >> 12) & 0b1;
                            let imm_4_0 = (bits >> 2) & 0b11111;
                            let imm = (imm_5 << 5) | imm_4_0;
                            let shamt = imm as u32;
                            Srai { rd, rs: rd, shamt }
                        }
                        0b10 => {
                            // ANDI
                            let rd = creg_at(bits, 7);
                            let imm_5 = (bits >> 12) & 0b1;
                            let imm_4_0 = (bits >> 2) & 0b11111;
                            let imm = (imm_5 << 5) | imm_4_0;
                            let imm = sign_extend(imm as i32, 5);
                            Andi { rd, rs: rd, imm }
                        }
                        0b11 => {
                            let rd = creg_at(bits, 7);
                            let rs2 = creg_at(bits, 2);
                            match ((bits >> 12) & 0b1, (bits >> 5) & 0b11) {
                                (0b0, 0b00) => Sub { rd, rs1: rd, rs2 },
                                (0b0, 0b01) => Xor { rd, rs1: rd, rs2 },
                                (0b0, 0b10) => Or { rd, rs1: rd, rs2 },
                                (0b0, 0b11) => And { rd, rs1: rd, rs2 },
                                (0b1, 0b00) => Subw { rd, rs1: rd, rs2 },
                                (0b1, 0b01) => Addw { rd, rs1: rd, rs2 },
                                _ => return None,
                            }
                        }
                        _ => {
                            return None;
                        }
                    }
                }
                0b101 => {
                    // J
                    let imm_5 = (bits >> 2) & 0b1;
                    let imm_3_1 = (bits >> 3) & 0b111;
                    let imm_7 = (bits >> 6) & 0b1;
                    let imm_6 = (bits >> 7) & 0b1;
                    let imm_10 = (bits >> 8) & 0b1;
                    let imm_9_8 = (bits >> 9) & 0b11;
                    let imm_4 = (bits >> 11) & 0b1;
                    let imm_11 = (bits >> 12) & 0b1;
                    let imm = (imm_11 << 11)
                        | (imm_10 << 10)
                        | (imm_9_8 << 8)
                        | (imm_7 << 7)
                        | (imm_6 << 6)
                        | (imm_5 << 5)
                        | (imm_4 << 4)
                        | (imm_3_1 << 1);
                    let imm = sign_extend(imm as i32, 11);
                    Jal { rd: Zero, imm }
                }
                0b110 => {
                    // BEQZ
                    let rs1 = creg_at(bits, 7);
                    let imm_5 = (bits >> 2) & 0b1;
                    let imm_2_1 = (bits >> 3) & 0b11;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm_4_3 = (bits >> 10) & 0b11;
                    let imm_8 = (bits >> 12) & 0b1;
                    let imm = (imm_8 << 8)
                        | (imm_7_6 << 6)
                        | (imm_5 << 5)
                        | (imm_4_3 << 3)
                        | (imm_2_1 << 1);
                    let imm = sign_extend(imm as i32, 8);
                    Beq {
                        rs1,
                        rs2: Zero,
                        imm,
                    }
                }
                0b111 => {
                    // BNEZ
                    let rs1 = creg_at(bits, 7);
                    let imm_5 = (bits >> 2) & 0b1;
                    let imm_2_1 = (bits >> 3) & 0b11;
                    let imm_7_6 = (bits >> 5) & 0b11;
                    let imm_4_3 = (bits >> 10) & 0b11;
                    let imm_8 = (bits >> 12) & 0b1;
                    let imm = (imm_8 << 8)
                        | (imm_7_6 << 6)
                        | (imm_5 << 5)
                        | (imm_4_3 << 3)
                        | (imm_2_1 << 1);
                    let imm = sign_extend(imm as i32, 8);
                    Bne {
                        rs1,
                        rs2: Zero,
                        imm,
                    }
                }
                _ => {
                    return None;
                }
            }
        }
        0b10 => {
            match (bits >> 13) & 0b111 {
                0b000 => {
                    // SLLI
                    let rd = reg_at(bits as u32, 7);
                    let imm_4_0 = (bits >> 2) & 0b11111;
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm = (imm_5 << 5) | imm_4_0;
                    let shamt = imm as i32;
                    Slli { rd, rs: rd, shamt }
                }
                0b010 => {
                    // LWSP
                    let rd = reg_at(bits as u32, 7);
                    let imm_7_6 = (bits >> 2) & 0b11;
                    let imm_4_2 = (bits >> 4) & 0b111;
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm = (imm_7_6 << 6) | (imm_5 << 5) | (imm_4_2 << 2);
                    let imm = imm as i32;
                    Lw { rd, rs: Sp, imm }
                }
                0b011 => {
                    // LDSP
                    let rd = reg_at(bits as u32, 7);
                    let imm_8_6 = (bits >> 2) & 0b111;
                    let imm_4_3 = (bits >> 5) & 0b11;
                    let imm_5 = (bits >> 12) & 0b1;
                    let imm = (imm_8_6 << 6) | (imm_5 << 5) | (imm_4_3 << 3);
                    let imm = imm as i32;
                    Ld { rd, rs: Sp, imm }
                }
                0b100 => {
                    let imm12 = (bits >> 12) & 0b1;
                    let rs1 = reg_at(bits as u32, 7);
                    let rs2 = reg_at(bits as u32, 2);
                    match (imm12, rs1, rs2) {
                        (0, rs, Reg::Zero) => Jalr {
                            rd: Zero,
                            rs,
                            imm: 0,
                        },
                        (0, rd, rs2) => Add { rd, rs1: Zero, rs2 },
                        (1, Zero, Zero) => Ebreak,
                        (1, rs, Zero) => Jalr { rd: Ra, rs, imm: 0 },
                        (1, rd, rs2) => Add { rd, rs1: rd, rs2 },
                        _ => {
                            return None;
                        }
                    }
                }
                0b110 => {
                    // SWSP
                    let rs2 = reg_at(bits as u32, 2);
                    let imm_7_6 = (bits >> 7) & 0b11;
                    let imm_5_2 = (bits >> 9) & 0b1111;
                    let imm = (imm_7_6 << 6) | (imm_5_2 << 2);
                    let imm = imm as i32;
                    Sw { rs1: Sp, rs2, imm }
                }
                0b111 => {
                    // SDSP
                    let rs2 = reg_at(bits as u32, 2);
                    let imm_8_6 = (bits >> 7) & 0b111;
                    let imm_5_3 = (bits >> 10) & 0b111;
                    let imm = (imm_8_6 << 6) | (imm_5_3 << 3);
                    let imm = imm as i32;
                    Sd { rs1: Sp, rs2, imm }
                }
                _ => {
                    return None;
                }
            }
        }
        _ => {
            return None;
        }
    };

    Some(inst)
}

/// Decodes an instruction.  Also returns the width of the decoded
/// instruction for incrementing the PC.  This allows us to handle
/// the compressed instructions too.
pub fn decode_instr(bits: u32) -> Option<(Inst, u64)> {
    if (bits & 3) == 3 {
        let inst = decode_32bit_instr(bits)?;
        Some((inst, 4))
    } else {
        let inst = decode_16bit_instr(bits as u16)?;
        Some((inst, 2))
    }
}

fn is_branch(inst: Inst) -> bool {
    use Inst::*;

    matches!(
        inst,
        Jal { .. }
            | Jalr { .. }
            | Beq { .. }
            | Bne { .. }
            | Blt { .. }
            | Bge { .. }
            | Bltu { .. }
            | Bgeu { .. }
            | Ecall
            | Ebreak
    )
}

//----------------------------------

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct BasicBlock {
    // How many times has this been executed.
    pub hits: u64,

    // The addresses this basic block covers
    pub begin: u64,
    pub end: u64,

    // Set if the first instruction has a breakpoint against it
    pub breakpoint: bool,

    pub instrs: Vec<(Inst, u8)>,
    pub ir: Option<Vec<IR>>,

    // The bb that was executed after this one, might save
    // a lookup in the bb cache.
    pub next: Weak<RefCell<BasicBlock>>,
}

/// Decodes a basic block.  Returns an error if it can't decode at least one instruction.
pub fn decode_basic_block(
    base: u64,
    bytes: &[u8],
    mut max_instrs: usize,
    breakpoints: &BTreeSet<u64>,
) -> std::result::Result<BasicBlock, u32> {
    let mut pc = base;
    let mut instrs = Vec::with_capacity(8);
    let mut r = Cursor::new(bytes);
    let is_bp = breakpoints.contains(&pc);

    while let Ok(low_bits) = r.read_u16::<LittleEndian>() {
        let (inst, width) = if (low_bits & 3) == 3 {
            // 32 bit instruction
            if let Ok(high_bits) = r.read_u16::<LittleEndian>() {
                let bits = ((high_bits as u32) << 16) | low_bits as u32;
                if let Some(inst) = decode_32bit_instr(bits) {
                    (inst, 4u8)
                } else {
                    debug!("decode failed at 0x{:x}", pc);
                    return Err(bits);
                }
            } else {
                debug!("decode failed at 0x{:x}", pc);
                return Err(low_bits as u32);
            }
        } else {
            // 16 bit instruction
            if let Some(inst) = decode_16bit_instr(low_bits) {
                (inst, 2u8)
            } else {
                debug!("decode failed at 0x{:x}", pc);
                return Err(low_bits as u32);
            }
        };

        // debug!("decoded: 0x{:x} {}", pc, inst);
        instrs.push((inst, width));
        pc += width as u64;

        if breakpoints.contains(&pc) {
            break;
        }

        max_instrs -= 1;
        if max_instrs == 0 || is_branch(inst) {
            break;
        }
    }

    Ok(BasicBlock {
        hits: 0,
        begin: base,
        end: pc,
        breakpoint: is_bp,
        instrs,
        ir: None,
        next: Weak::new(),
    })
}

/// Collects a set of registers that are used in a block of code.
pub fn collect_regs(insts: &[(Inst, u8)]) -> BTreeSet<Reg> {
    use Inst::*;
    let mut r: BTreeSet<Reg> = BTreeSet::new();
    for (i, _) in insts {
        match i {
            Lui { rd, .. } => {
                r.insert(*rd);
            }
            Auipc { rd, .. } => {
                r.insert(*rd);
            }
            Jal { rd, .. } => {
                r.insert(*rd);
            }
            Jalr { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Beq { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Bne { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Blt { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Bge { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Bltu { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Bgeu { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }

            Lb { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Lh { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Lw { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Lwu { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Ld { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Lbu { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Lhu { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Sb { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sh { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sw { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sd { rs1, rs2, .. } => {
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Addi { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Addiw { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Slti { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Sltiu { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Xori { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Ori { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Andi { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Slli { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Slliw { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Srli { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Srliw { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Sraiw { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Srai { rd, rs, .. } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Add { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Addw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sub { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Subw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sll { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sllw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Srlw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sraw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Slt { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sltu { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Xor { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Srl { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Sra { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Or { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            And { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Mul { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Mulh { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Mulhsu { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Mulhu { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Mulw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Div { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Divu { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Divw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Divuw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Rem { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Remu { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Remw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Remuw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Fence => {}
            Fencei => {}
            Ecall => {}
            Ebreak => {}
            Lrw { rd, rs } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Scw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoswapw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoaddw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoxorw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoandw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoorw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amominw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amomaxw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amominuw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amomaxuw { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Lrd { rd, rs } => {
                r.insert(*rd);
                r.insert(*rs);
            }
            Scd { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoswapd { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoaddd { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoxord { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoandd { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amoord { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amomind { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amomaxd { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amominud { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
            Amomaxud { rd, rs1, rs2 } => {
                r.insert(*rd);
                r.insert(*rs1);
                r.insert(*rs2);
            }
        }
    }
    r.insert(Reg::PC);
    r
}

//----------------------------------
