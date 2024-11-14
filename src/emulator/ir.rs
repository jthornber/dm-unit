use std::cmp::Ordering;

use crate::emulator::ir_optimise::*;
use crate::emulator::riscv::{self, *};
use crate::emulator::riscv_to_ir::*;

//------------------------------------------------------------------

/// The intermediate representation is very similar to riscv, except:
/// - it uses static single assignment, no registers/infinite registers.
/// - it uses host addresses, there is an instruction for translating
///   from guest to host address space.
/// - There are no branches, since we use IR to encode basic blocks only.
///   Instead there is a mvif instruction that can be used to set the guest
///   PC.
/// - There is an instruction for getting the base of the guest register file.
///   This is doing no more than making a calling convention explicit.
/// - No need for atomics, we only have one core.

#[derive(Clone, Copy, Debug, Eq)]
pub struct IReg(pub u32, pub Option<riscv::Reg>);

impl PartialOrd for IReg {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl Ord for IReg {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialEq for IReg {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

// impl Eq for Reg {};

impl std::fmt::Display for IReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = if let Some(greg) = self.1 {
            format!("t{}({})", self.0, greg)
        } else {
            format!("t{}", self.0)
        };
        f.pad(&str)
    }
}

//------------------------------

#[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum TestOp {
    Eq,
    Ne,
    Lt,
    Ge,
    Ltu,
    Geu,
}

use TestOp::*;

#[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Addw,
    Sub,
    Subw,
    Sll,
    Sllw,
    Srlw,
    Sraw,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Mulw,
    Div,
    Divu,
    Divw,
    Divuw,
    Rem,
    Remu,
    Remw,
    Remuw,
}

use BinOp::*;

#[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum ImmOp {
    Addi,
    Addiw,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
}

use ImmOp::*;

#[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum ShiftOp {
    Slli,
    Slliw,
    Srli,
    Srliw,
    Sraiw,
    Srai,
}

use ShiftOp::*;

#[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum RValue {
    Gbase,
    Gtoh { guest: IReg, len: u32, perms: u8 },
    Li { imm: i64 },

    Test { op: TestOp, rs1: IReg, rs2: IReg },

    // Conditional move, if t != 0 then rd = rs1, else rs2
    Cond { t: IReg, rs1: IReg, rs2: IReg },

    Ld { rs: IReg },
    Lb { rs: IReg },
    Lh { rs: IReg },
    Lw { rs: IReg },
    Lbu { rs: IReg },
    Lhu { rs: IReg },
    Lwu { rs: IReg },

    Imm { op: ImmOp, rs: IReg, imm: i32 },
    Shift { op: ShiftOp, rs: IReg, shamt: u8 },
    Bin { op: BinOp, rs1: IReg, rs2: IReg },
}

use RValue::*;

#[derive(Clone, Copy, Debug)]
pub enum IR {
    Assign { rd: IReg, rval: RValue },

    Sb { rs1: IReg, rs2: IReg },
    Sh { rs1: IReg, rs2: IReg },
    Sw { rs1: IReg, rs2: IReg },
    Sd { rs1: IReg, rs2: IReg },

    Ecall,
    Ebreak,
}

use IR::*;

//-------------------------------

impl std::fmt::Display for TestOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Eq => write!(f, "=="),
            Ne => write!(f, "!="),
            Lt => write!(f, "<"),
            Ge => write!(f, ">="),
            Ltu => write!(f, "<u"),
            Geu => write!(f, ">=u"),
        }
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Add => write!(f, "+"),
            Addw => write!(f, "+w"),
            Sub => write!(f, "-"),
            Subw => write!(f, "-w"),
            Sll => write!(f, "<<"),
            Sllw => write!(f, "<<w"),
            Srlw => write!(f, ">>w"),
            Sraw => write!(f, ">>aw"),
            Slt => write!(f, "slt"),
            Sltu => write!(f, "sltu"),
            Xor => write!(f, "^"),
            Srl => write!(f, ">>"),
            Sra => write!(f, ">>a"),
            Or => write!(f, "|"),
            And => write!(f, "&"),
            Mul => write!(f, "*"),
            Mulh => write!(f, "*h"),
            Mulhsu => write!(f, "*hsu"),
            Mulhu => write!(f, "*hu"),
            Mulw => write!(f, "*w"),
            Div => write!(f, "/"),
            Divu => write!(f, "/u"),
            Divw => write!(f, "/w"),
            Divuw => write!(f, "/uw"),
            Rem => write!(f, "rem"),
            Remu => write!(f, "remu"),
            Remw => write!(f, "remw"),
            Remuw => write!(f, "remuw"),
        }
    }
}

impl std::fmt::Display for ImmOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Addi => write!(f, "+"),
            Addiw => write!(f, "+w"),
            Slti => write!(f, "slti"),
            Sltiu => write!(f, "sltiu"),
            Xori => write!(f, "^"),
            Ori => write!(f, "|"),
            Andi => write!(f, "&"),
        }
    }
}

impl std::fmt::Display for ShiftOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Slli => write!(f, "<<"),
            Slliw => write!(f, "<<w"),
            Srli => write!(f, ">>"),
            Srliw => write!(f, ">>w"),
            Sraiw => write!(f, ">>aw"),
            Srai => write!(f, ">>a"),
        }
    }
}

impl std::fmt::Display for RValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Gbase => write!(f, "gbase"),
            Gtoh { guest, len, perms } => {
                write!(f, "gtoh {},{},{}", guest, len, perms)
            }
            Li { imm } => {
                write!(f, "li 0x{:x}", imm)
            }
            Test { op, rs1, rs2 } => {
                write!(f, "test {},{},{}", op, rs1, rs2)
            }
            Cond { t, rs1, rs2 } => {
                write!(f, "cond {},{},{}", t, rs1, rs2)
            }
            Ld { rs } => {
                write!(f, "ld {}", rs)
            }
            Lb { rs } => {
                write!(f, "lb {}", rs)
            }
            Lh { rs } => {
                write!(f, "lh {}", rs)
            }
            Lw { rs } => {
                write!(f, "lw {}", rs)
            }
            Lbu { rs } => {
                write!(f, "lbu {}", rs)
            }
            Lhu { rs } => {
                write!(f, "lhu {}", rs)
            }
            Lwu { rs } => {
                write!(f, "lwu {}", rs)
            }
            Imm { op, rs, imm } => {
                write!(f, "{} {} 0x{:x}", rs, op, imm)
            }
            Shift { op, rs, shamt } => {
                write!(f, "{} {} 0x{:x}", rs, op, shamt)
            }
            Bin { op, rs1, rs2 } => {
                write!(f, "{} {} {}", rs1, op, rs2)
            }
        }
    }
}

impl std::fmt::Display for IR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Assign { rd, rval } => {
                write!(f, "{:<10} <- {}", rd, rval)
            }
            Sb { rs1, rs2 } => {
                write!(f, "              sb {} {}", rs1, rs2)
            }
            Sh { rs1, rs2 } => {
                write!(f, "              sh {} {}", rs1, rs2)
            }
            Sw { rs1, rs2 } => {
                write!(f, "              sw {} {}", rs1, rs2)
            }
            Sd { rs1, rs2 } => {
                write!(f, "              sd {} {}", rs1, rs2)
            }
            Ecall => {
                write!(f, "              ecall")
            }
            Ebreak => {
                write!(f, "              ebreak")
            }
        }
    }
}

//--------------------------------

pub fn to_ir(insts: &[(Inst, u8)], opt: bool) -> Vec<IR> {
    let ir = riscv_to_ir(insts);
    if opt {
        optimise(&ir)
    } else {
        ir
    }
}

//------------------------------------------------------------------
