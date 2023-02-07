use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use crate::emulator::memory::*;
use crate::emulator::riscv::{self, *};

/// The intermediate representation is vey similar to riscv, except:
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
pub struct Reg(u32, Option<riscv::Reg>);

impl PartialOrd for Reg {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl Ord for Reg {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialEq for Reg {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

// impl Eq for Reg {};

impl std::fmt::Display for Reg {
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
    Gtoh { guest: Reg, len: u32, perms: u8 },
    Li { imm: i64 },

    Test { op: TestOp, rs1: Reg, rs2: Reg },

    // Conditional move, if t != 0 then rd = rs1, else rs2
    Cond { t: Reg, rs1: Reg, rs2: Reg },

    Ld { rs: Reg },
    Lb { rs: Reg },
    Lh { rs: Reg },
    Lw { rs: Reg },
    Lbu { rs: Reg },
    Lhu { rs: Reg },
    Lwu { rs: Reg },

    Imm { op: ImmOp, rs: Reg, imm: i32 },
    Shift { op: ShiftOp, rs: Reg, shamt: u8 },
    Bin { op: BinOp, rs1: Reg, rs2: Reg },
}

use RValue::*;

#[derive(Clone, Copy, Debug)]
pub enum IR {
    Assign { rd: Reg, rval: RValue },

    Sb { rs1: Reg, rs2: Reg },
    Sh { rs1: Reg, rs2: Reg },
    Sw { rs1: Reg, rs2: Reg },
    Sd { rs1: Reg, rs2: Reg },

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

//----------------------------------

#[derive(Default)]
struct Builder {
    buffer: Vec<IR>,
    current_reg: u32,
    guest_regs: BTreeMap<riscv::Reg, Reg>,
}

impl Builder {
    fn push(&mut self, inst: IR) {
        self.buffer.push(inst);
    }

    // Get a new reg to represent greg (guest reg).  After this,
    // calls to ref_greg() for this register will return the new reg,
    // so make sure you don't do this:
    //     let rd = self.def_greg(rd);
    //     let rs = self.ref_greg(rs);
    // Since rs could be rd, and so you'll end up with something like: t59 <- t59 + 0x0.
    // Instead call def_greg() after getting any references you need to build the instruction.
    fn def_greg(&mut self, greg: &riscv::Reg) -> Reg {
        let reg = Reg(self.current_reg, Some(*greg));
        self.current_reg += 1;
        self.guest_regs.insert(*greg, reg);
        reg
    }

    /// Returns the IR register that contains the guest reg
    fn ref_greg(&self, greg: &riscv::Reg) -> Reg {
        *self.guest_regs.get(greg).unwrap()
    }

    /// Call this when you want to mutate the value of a guest register.
    /// It returns (old, new)
    fn mut_greg(&mut self, greg: &riscv::Reg) -> (Reg, Reg) {
        let mut new = self.next_reg();
        new.1 = Some(*greg);
        let old = *self.guest_regs.get(greg).unwrap();

        // We don't insert the new reg for zero, since it
        // shouldn't change.
        if *greg != riscv::Reg::Zero {
            self.guest_regs.insert(*greg, new);
        }
        (old, new)
    }

    fn next_reg(&mut self) -> Reg {
        let r = self.current_reg;
        self.current_reg += 1;
        Reg(r, None)
    }

    /// Pushes a new assignment operation
    fn assign(&mut self, rd: Reg, rval: RValue) {
        self.push(IR::Assign { rd, rval });
    }

    /// Generates a new register, and pushes an assignment to it.
    fn assign_next(&mut self, rval: RValue) -> Reg {
        let rd = self.next_reg();
        self.assign(rd, rval);
        rd
    }

    /// Pushes instructions to increment the program counter
    fn inc_pc(&mut self, delta: i32) {
        let (old, new) = self.mut_greg(&riscv::Reg::PC);
        self.assign(
            new,
            RValue::Imm {
                op: ImmOp::Addi,
                rs: old,
                imm: delta,
            },
        );
    }

    // Pushes a sequence of instructions that implement a branch.
    // if rs1 <op> rs2 { pc += offset } else { pc += width }
    fn branch(&mut self, rs1: &riscv::Reg, rs2: &riscv::Reg, offset: &i32, op: TestOp, width: i32) {
        let rs1 = self.ref_greg(rs1);
        let rs2 = self.ref_greg(rs2);
        let (old_pc, new_pc) = self.mut_greg(&riscv::Reg::PC);

        // FIXME: double check that this only gets executed if the branch
        // is taken.
        let dest = self.assign_next(Imm {
            op: Addi,
            rs: old_pc,
            imm: *offset,
        });
        let t = self.assign_next(Test { op, rs1, rs2 });
        let next_instr = self.assign_next(Imm {
            op: Addi,
            rs: old_pc,
            imm: width,
        });
        self.assign(
            new_pc,
            Cond {
                t,
                rs1: dest,
                rs2: next_instr,
            },
        );
    }

    fn load<F: FnOnce(Reg) -> RValue>(
        &mut self,
        rd: &riscv::Reg,
        rs: &riscv::Reg,
        imm: &i32,
        len: usize,
        func: F,
    ) {
        let rs = self.ref_greg(rs);
        let rd1 = self.assign_next(Imm {
            op: Addi,
            rs,
            imm: *imm,
        });

        let rd2 = self.assign_next(Gtoh {
            guest: rd1,
            len: len as u32,
            perms: PERM_READ,
        });

        let (_old_rd, new_rd) = self.mut_greg(rd);
        self.assign(new_rd, func(rd2));
    }

    fn store<F: FnOnce(Reg, Reg) -> IR>(
        &mut self,
        rs1: &riscv::Reg,
        rs2: &riscv::Reg,
        imm: &i32,
        len: usize,
        func: F,
    ) {
        // Calc dest address
        let rs1 = self.ref_greg(rs1);
        let dest = self.assign_next(Imm {
            op: Addi,
            rs: rs1,
            imm: *imm,
        });

        // Convert guest to host address
        let host_addr = self.assign_next(Gtoh {
            guest: dest,
            len: len as u32,
            perms: PERM_WRITE,
        });

        let rs2 = self.ref_greg(rs2);
        self.push(func(host_addr, rs2));
    }

    fn xlate_shift(&mut self, rd: &riscv::Reg, op: ShiftOp, rs: &riscv::Reg, shamt: u8) {
        let rs = self.ref_greg(rs);
        let rd = self.def_greg(rd);
        self.assign(rd, RValue::Shift { op, rs, shamt });
    }

    fn imm(&mut self, rd: &riscv::Reg, op: ImmOp, rs: &riscv::Reg, imm: &i32) {
        let rs = self.ref_greg(rs);
        let rd = self.def_greg(rd);
        self.assign(rd, RValue::Imm { op, rs, imm: *imm });
    }

    fn bin(&mut self, rd: &riscv::Reg, op: BinOp, rs1: &riscv::Reg, rs2: &riscv::Reg) {
        let rs1 = self.ref_greg(rs1);
        let rs2 = self.ref_greg(rs2);
        let rd = self.def_greg(rd);
        self.assign(rd, RValue::Bin { op, rs1, rs2 });
    }
}

//------------------------------
// Riscv to IR

fn xlate_inst(b: &mut Builder, inst: &Inst, width: u8) {
    let width = width as i32;

    match inst {
        Inst::Lui { rd, imm } => {
            let rd = b.ref_greg(rd);
            b.assign(
                rd,
                Li {
                    imm: (*imm as i64) << 12,
                },
            );
            b.inc_pc(width);
        }
        Inst::Auipc { rd, imm } => {
            let pc = b.ref_greg(&riscv::Reg::PC);
            let rd1 = b.assign_next(Li {
                imm: (*imm as i64) << 12,
            });
            let rd2 = b.def_greg(rd);
            b.assign(
                rd2,
                Bin {
                    op: Add,
                    rs1: pc,
                    rs2: rd1,
                },
            );
            b.inc_pc(width);
        }
        Inst::Jal { .. } => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Jalr { rd, rs, imm } => {
            let (old_pc, new_pc) = b.mut_greg(&riscv::Reg::PC);

            // Save the return address
            let rd = b.def_greg(rd);
            b.assign(
                rd,
                Imm {
                    op: Addi,
                    rs: old_pc,
                    imm: width,
                },
            );

            // And jump
            let rs = b.ref_greg(rs);
            b.assign(
                new_pc,
                Imm {
                    op: Addi,
                    rs,
                    imm: *imm,
                },
            );
        }
        Inst::Beq { rs1, rs2, imm } => {
            b.branch(rs1, rs2, imm, TestOp::Eq, width);
        }
        Inst::Bne { rs1, rs2, imm } => {
            b.branch(rs1, rs2, imm, TestOp::Ne, width);
        }
        Inst::Blt { rs1, rs2, imm } => {
            b.branch(rs1, rs2, imm, TestOp::Lt, width);
        }
        Inst::Bge { rs1, rs2, imm } => {
            b.branch(rs1, rs2, imm, TestOp::Ge, width);
        }
        Inst::Bltu { rs1, rs2, imm } => {
            b.branch(rs1, rs2, imm, TestOp::Ltu, width);
        }
        Inst::Bgeu { rs1, rs2, imm } => {
            b.branch(rs1, rs2, imm, TestOp::Geu, width);
        }
        Inst::Lb { rd, rs, imm } => {
            b.load(rd, rs, imm, 1, |rs| Lb { rs });
            b.inc_pc(width);
        }
        Inst::Lh { rd, rs, imm } => {
            b.load(rd, rs, imm, 2, |rs| Lh { rs });
            b.inc_pc(width);
        }
        Inst::Lw { rd, rs, imm } => {
            b.load(rd, rs, imm, 4, |rs| Lw { rs });
            b.inc_pc(width);
        }
        Inst::Lwu { rd, rs, imm } => {
            b.load(rd, rs, imm, 4, |rs| Lwu { rs });
            b.inc_pc(width);
        }
        Inst::Ld { rd, rs, imm } => {
            b.load(rd, rs, imm, 8, |rs| Ld { rs });
            b.inc_pc(width);
        }
        Inst::Lbu { rd, rs, imm } => {
            b.load(rd, rs, imm, 1, |rs| Lbu { rs });
            b.inc_pc(width);
        }
        Inst::Lhu { rd, rs, imm } => {
            b.load(rd, rs, imm, 2, |rs| Lhu { rs });
            b.inc_pc(width);
        }
        Inst::Sb { rs1, rs2, imm } => {
            b.store(rs1, rs2, imm, 1, |rs1, rs2| Sb { rs1, rs2 });
            b.inc_pc(width);
        }
        Inst::Sh { rs1, rs2, imm } => {
            b.store(rs1, rs2, imm, 2, |rs1, rs2| Sh { rs1, rs2 });
            b.inc_pc(width);
        }
        Inst::Sw { rs1, rs2, imm } => {
            b.store(rs1, rs2, imm, 4, |rs1, rs2| Sw { rs1, rs2 });
            b.inc_pc(width);
        }
        Inst::Sd { rs1, rs2, imm } => {
            b.store(rs1, rs2, imm, 8, |rs1, rs2| Sd { rs1, rs2 });
            b.inc_pc(width);
        }
        Inst::Addi { rd, rs, imm } => {
            b.imm(rd, Addi, rs, imm);
            b.inc_pc(width);
        }
        Inst::Addiw { rd, rs, imm } => {
            b.imm(rd, Addiw, rs, imm);
            b.inc_pc(width);
        }
        Inst::Slti { rd, rs, imm } => {
            b.imm(rd, Slti, rs, imm);
            b.inc_pc(width);
        }
        Inst::Sltiu { rd, rs, imm } => {
            b.imm(rd, Sltiu, rs, imm);
            b.inc_pc(width);
        }
        Inst::Xori { rd, rs, imm } => {
            b.imm(rd, Xori, rs, imm);
            b.inc_pc(width);
        }
        Inst::Ori { rd, rs, imm } => {
            b.imm(rd, Ori, rs, imm);
            b.inc_pc(width);
        }
        Inst::Andi { rd, rs, imm } => {
            b.imm(rd, Andi, rs, imm);
            b.inc_pc(width);
        }
        Inst::Slli { rd, rs, shamt } => {
            b.xlate_shift(rd, Slli, rs, *shamt as u8);
            b.inc_pc(width);
        }
        Inst::Slliw { rd, rs, shamt } => {
            b.xlate_shift(rd, Slliw, rs, *shamt as u8);
            b.inc_pc(width);
        }
        Inst::Srli { rd, rs, shamt } => {
            b.xlate_shift(rd, Srli, rs, *shamt as u8);
            b.inc_pc(width);
        }
        Inst::Srliw { rd, rs, shamt } => {
            b.xlate_shift(rd, Srliw, rs, *shamt as u8);
            b.inc_pc(width);
        }
        Inst::Sraiw { rd, rs, shamt } => {
            b.xlate_shift(rd, Sraiw, rs, *shamt as u8);
            b.inc_pc(width);
        }
        Inst::Srai { rd, rs, shamt } => {
            b.xlate_shift(rd, Srai, rs, *shamt as u8);
            b.inc_pc(width);
        }
        Inst::Add { rd, rs1, rs2 } => {
            b.bin(rd, Add, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Addw { rd, rs1, rs2 } => {
            b.bin(rd, Addw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Sub { rd, rs1, rs2 } => {
            b.bin(rd, Sub, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Subw { rd, rs1, rs2 } => {
            b.bin(rd, Subw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Sll { rd, rs1, rs2 } => {
            b.bin(rd, Sll, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Sllw { rd, rs1, rs2 } => {
            b.bin(rd, Sllw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Srlw { rd, rs1, rs2 } => {
            b.bin(rd, Srlw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Sraw { rd, rs1, rs2 } => {
            b.bin(rd, Sraw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Slt { rd, rs1, rs2 } => {
            b.bin(rd, Slt, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Sltu { rd, rs1, rs2 } => {
            b.bin(rd, Sltu, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Xor { rd, rs1, rs2 } => {
            b.bin(rd, Xor, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Srl { rd, rs1, rs2 } => {
            b.bin(rd, Srl, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Sra { rd, rs1, rs2 } => {
            b.bin(rd, Sra, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Or { rd, rs1, rs2 } => {
            b.bin(rd, Or, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::And { rd, rs1, rs2 } => {
            b.bin(rd, And, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Mul { rd, rs1, rs2 } => {
            b.bin(rd, Mul, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Mulh { rd, rs1, rs2 } => {
            b.bin(rd, Mulh, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Mulhsu { rd, rs1, rs2 } => {
            b.bin(rd, Mulhsu, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Mulhu { rd, rs1, rs2 } => {
            b.bin(rd, Mulhu, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Mulw { rd, rs1, rs2 } => {
            b.bin(rd, Mulw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Div { rd, rs1, rs2 } => {
            b.bin(rd, Div, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Divu { rd, rs1, rs2 } => {
            b.bin(rd, Divu, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Divw { rd, rs1, rs2 } => {
            b.bin(rd, Divw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Divuw { rd, rs1, rs2 } => {
            b.bin(rd, Divuw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Rem { rd, rs1, rs2 } => {
            b.bin(rd, Rem, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Remu { rd, rs1, rs2 } => {
            b.bin(rd, Remu, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Remw { rd, rs1, rs2 } => {
            b.bin(rd, Remw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Remuw { rd, rs1, rs2 } => {
            b.bin(rd, Remuw, rs1, rs2);
            b.inc_pc(width);
        }
        Inst::Fence => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Fencei => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Ecall => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Ebreak => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Lrw { .. } => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Scw { .. /* rd, rs1, rs2 */ } => {
            // FIXME: finish
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoswapw { rd, rs1, rs2 } => {
            let t = b.assign_next(Lw {
                rs: b.ref_greg(rs1),
            });
            b.store(rs1, rs2, &0, 4, |rs1, rs2| Sw { rs1, rs2 });
            let rd = b.def_greg(rd);
            b.assign(
                rd,
                Imm {
                    op: Addi,
                    rs: t,
                    imm: 0,
                },
            );
            b.inc_pc(width);
        }
        Inst::Amoaddw { .. /* rd, rs1, rs2 */ } => {
            /*
            let rs1 = b.ref_greg(rs1);
            let rs2 = b.ref_greg(rs2);
            let t = b.assign_next(Lw { rs: rs1 });

            let new_value = b.assign_next(RValue::Bin { Addw, t, rs2 });
            b.store(rs1, new_value, &0, 4, |rs1, rs2| Sw { rs1, rs2 });
            let rd = b.def_greg(rd);
            b.assign(rd, Mv { rs: t });
            */

            b.inc_pc(width);
            todo!();
        }
        Inst::Amoxorw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoandw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoorw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amominw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amomaxw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amominuw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amomaxuw { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Lrd { .. /* rd, rs */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Scd { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoswapd { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoaddd { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoxord { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoandd { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amoord { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amomind { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amomaxd { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amominud { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
        Inst::Amomaxud { .. /* rd, rs1, rs2 */ } => {
            b.inc_pc(width);
            todo!();
        }
    }
}

fn riscv_to_ir(b: &mut Builder, insts: &[(Inst, u8)]) {
    let live_regs = collect_regs(insts);
    if live_regs.contains(&riscv::Reg::Zero) {
        let zero = b.def_greg(&riscv::Reg::Zero);
        b.assign(zero, Li { imm: 0 });
    }

    // Load all guest registers, except zero
    let base = b.assign_next(Gbase);
    for greg in &live_regs {
        if *greg == riscv::Reg::Zero {
            continue;
        }

        let rd1 = b.assign_next(Imm {
            op: Addi,
            rs: base,
            imm: *greg as i32 * 8,
        });
        let rd2 = b.def_greg(greg);
        b.assign(rd2, Ld { rs: rd1 });
    }

    // xlate instructions
    for (inst, width) in insts {
        xlate_inst(b, inst, *width);
    }

    // Save all guest registers, except zero
    for greg in &live_regs {
        if *greg == riscv::Reg::Zero {
            continue;
        }
        let rs1 = b.assign_next(Imm {
            op: Addi,
            rs: base,
            imm: *greg as i32 * 8,
        });
        let rs2 = b.ref_greg(greg);
        b.push(Sd { rs1, rs2 });
    }
}

//--------------------------------
// Optimisation passes

fn subst_reg(r: Reg, substs: &BTreeMap<Reg, Reg>) -> Reg {
    if let Some(old) = substs.get(&r) {
        *old
    } else {
        r
    }
}

fn apply_substitutions(rval: &RValue, substs: &BTreeMap<Reg, Reg>) -> RValue {
    match rval {
        Gbase => Gbase,
        Gtoh { guest, len, perms } => Gtoh {
            guest: subst_reg(*guest, substs),
            len: *len,
            perms: *perms,
        },
        Li { imm } => Li { imm: *imm },
        Test { op, rs1, rs2 } => Test {
            op: *op,
            rs1: subst_reg(*rs1, substs),
            rs2: subst_reg(*rs2, substs),
        },
        Cond { t, rs1, rs2 } => Cond {
            t: subst_reg(*t, substs),
            rs1: subst_reg(*rs1, substs),
            rs2: subst_reg(*rs2, substs),
        },
        Ld { rs } => Ld {
            rs: subst_reg(*rs, substs),
        },
        Lb { rs } => Lb {
            rs: subst_reg(*rs, substs),
        },
        Lh { rs } => Lh {
            rs: subst_reg(*rs, substs),
        },
        Lw { rs } => Lw {
            rs: subst_reg(*rs, substs),
        },
        Lbu { rs } => Lbu {
            rs: subst_reg(*rs, substs),
        },
        Lhu { rs } => Lhu {
            rs: subst_reg(*rs, substs),
        },
        Lwu { rs } => Lwu {
            rs: subst_reg(*rs, substs),
        },
        Imm { op, rs, imm } => Imm {
            op: *op,
            rs: subst_reg(*rs, substs),
            imm: *imm,
        },
        Shift { op, rs, shamt } => Shift {
            op: *op,
            rs: subst_reg(*rs, substs),
            shamt: *shamt,
        },
        Bin { op, rs1, rs2 } => Bin {
            op: *op,
            rs1: subst_reg(*rs1, substs),
            rs2: subst_reg(*rs2, substs),
        },
    }
}

fn is_load(rval: &RValue) -> bool {
    match rval {
        Ld { .. } | Lb { .. } | Lh { .. } | Lw { .. } | Lbu { .. } | Lhu { .. } | Lwu { .. } => {
            true
        }
        _ => false,
    }
}

/// Common subexpression elimination
fn opt_cse(instrs: &[IR]) -> Vec<IR> {
    let mut r = Vec::new();
    let mut seen: BTreeMap<RValue, Reg> = BTreeMap::new();
    let mut substs: BTreeMap<Reg, Reg> = BTreeMap::new();

    for ir in instrs {
        match ir {
            Assign { rd, rval } => {
                let rval = apply_substitutions(rval, &substs);
                if let Some(old) = seen.get(&rval) {
                    if is_load(&rval) {
                        seen.insert(rval, *rd);
                        r.push(Assign { rd: *rd, rval });
                    } else {
                        // skip this instruction, substituting the earlier value in
                        // future expressions.
                        substs.insert(*rd, *old);
                    }
                } else {
                    seen.insert(rval, *rd);
                    r.push(Assign { rd: *rd, rval });
                }
            }
            Sb { rs1, rs2 } => r.push(Sb {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sh { rs1, rs2 } => r.push(Sh {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sw { rs1, rs2 } => r.push(Sw {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sd { rs1, rs2 } => r.push(Sd {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            _ => {
                r.push(*ir);
            }
        }
    }

    r
}

//--------------------------------

/// Examines an rval and returns Some(rs) if it is a no op that could be
/// replaced with a simple reference to rs
fn is_noop(rval: &RValue) -> Option<Reg> {
    let check = |t: bool, rs: &Reg| -> Option<Reg> {
        if t {
            Some(*rs)
        } else {
            None
        }
    };

    match rval {
        Gbase => None,
        Gtoh { .. } => None,
        Li { .. } => None,
        Test { .. } => None,
        Cond { rs1, rs2, .. } => check(rs1.0 == rs2.0, rs1),
        Ld { .. } => None,
        Lb { .. } => None,
        Lh { .. } => None,
        Lw { .. } => None,
        Lbu { .. } => None,
        Lhu { .. } => None,
        Lwu { .. } => None,
        Imm { op, rs, imm } => {
            // Many of these ops will sign extend an i32 result to i64, so
            // eg, 'addiw rs 0' is not a noop.
            match op {
                Addi => check(*imm == 0, rs),
                Addiw => None, // addiw 0 will sign extend
                Slti => None,
                Sltiu => None,
                Xori => None,
                Ori => check(*imm == 0, rs),
                Andi => check(*imm == -1i32, rs),
            }
        }
        Shift { op, rs, shamt } => match op {
            Slli => check(*shamt == 0, rs),
            Slliw => None,
            Srli => check(*shamt == 0, rs),
            Srliw => None,
            Sraiw => None,
            Srai => check(*shamt == 0, rs),
        },
        Bin { .. } => None,
    }
}

/// Remove Noops like addi rs,0
fn opt_noop(instrs: &[IR]) -> Vec<IR> {
    let mut r = Vec::new();
    let mut substs: BTreeMap<Reg, Reg> = BTreeMap::new();

    for ir in instrs {
        match ir {
            Assign { rd, rval } => {
                let rval = apply_substitutions(rval, &substs);
                if let Some(rs) = is_noop(&rval) {
                    // skip this instruction, substituting the rs in to
                    // future expressions.
                    substs.insert(*rd, rs);
                } else {
                    r.push(Assign { rd: *rd, rval });
                }
            }
            Sb { rs1, rs2 } => r.push(Sb {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sh { rs1, rs2 } => r.push(Sh {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sw { rs1, rs2 } => r.push(Sw {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sd { rs1, rs2 } => r.push(Sd {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            _ => {
                r.push(*ir);
            }
        }
    }

    r
}

//--------------------------------

fn simplify(rval: &RValue, defs: &mut BTreeMap<Reg, RValue>) -> RValue {
    match rval {
        Imm { op: Addi, rs, imm } => {
            let rval2 = defs.get(rs).unwrap();
            match rval2 {
                Imm {
                    op: Addi,
                    rs: rs2,
                    imm: imm2,
                } => Imm {
                    op: Addi,
                    rs: *rs2,
                    imm: *imm + *imm2,
                },
                _ => *rval,
            }
        }
        _ => *rval,
    }
}

/// Optimisation pass that tries to simplify expressions.  eg, many addi
/// instructions can be collapsed into a single one.
fn opt_simplify(instrs: &[IR]) -> Vec<IR> {
    let mut r = Vec::new();
    let mut defs = BTreeMap::new();
    for ir in instrs {
        match ir {
            Assign { rd, rval } => {
                let rval = simplify(rval, &mut defs);
                r.push(Assign { rd: *rd, rval });
                defs.insert(*rd, rval);
            }
            _ => {
                r.push(*ir);
            }
        }
    }
    r
}

//--------------------------------

// We assume that there is a gap between all memory mapped regions.  So if
// we can prove two gtoh calls are to adjacent guest addresses then we can
// make do with a single call with an extended range.  In fact, I'm pretty
// certain any gtoh where 'guest' is of the form: addi base offset, is ok.
//
// If this is called after we've done algebraic simplification then
// there's a good chance all the guest ptrs will consist of the same
// base register plus a constant.  It shouldn't be repeatedly called
// however since it inserts 'addi base, offset' instructions that are
// likely to be simplifiable themselves.

#[derive(Clone, Copy, Debug)]
struct GuestRange {
    base: Reg,
    offset: i32,
    len: u32,
    perms: u8,
}

enum Merge {
    Merge(GuestRange),
    NoMerge(GuestRange, GuestRange),
}

use Merge::*;

fn extract_range(
    guest: &Reg,
    len: u32,
    perms: u8,
    defs: &BTreeMap<Reg, RValue>,
) -> Option<GuestRange> {
    let rval = defs.get(guest).unwrap();

    match rval {
        Imm { op: Addi, rs, imm } => Some(GuestRange {
            base: *rs,
            offset: *imm,
            len,
            perms,
        }),
        _ => None,
    }
}

// This assumes r1.offset < r2.offset
fn merge_ranges(r1: GuestRange, r2: GuestRange) -> Merge {
    if r1.base != r2.base {
        return NoMerge(r1, r2);
    }

    Merge(GuestRange {
        base: r1.base,
        offset: r1.offset,
        len: ((r2.offset + r2.len as i32) - r1.offset) as u32,
        perms: r1.perms | r2.perms,
    })
}

fn opt_gtoh(instrs: &[IR]) -> Vec<IR> {
    let mut defs = BTreeMap::new();
    let mut highest_reg = 0;
    for i in instrs {
        match i {
            Assign { rd, rval } => {
                defs.insert(*rd, *rval);

                if rd.0 > highest_reg {
                    highest_reg = rd.0;
                }
            }
            _ => {}
        }
    }

    let mut ranges = Vec::new();
    for i in instrs {
        match i {
            Assign {
                rval: Gtoh { guest, len, perms },
                ..
            } => {
                if let Some(range) = extract_range(guest, *len, *perms, &defs) {
                    ranges.push(range);
                }
            }
            _ => {}
        }
    }

    /*
    debug!("ranges before merge:");
    for r in &ranges {
        debug!("    {:?}", r);
    }
    */

    ranges.sort_by_key(|r| (r.base.0, r.offset));
    let mut merged = Vec::new();
    let mut last: Option<GuestRange> = None;
    for r in &ranges {
        if let Some(gr) = last {
            match merge_ranges(gr, *r) {
                Merge(r) => {
                    last = Some(r);
                }
                NoMerge(r1, r2) => {
                    merged.push(r1);
                    last = Some(r2);
                }
            }
        } else {
            last = Some(*r);
        }
    }
    if let Some(last) = last {
        merged.push(last);
    }
    ranges = merged;

    /*
    debug!("ranges after merge:");
    for r in &ranges {
        debug!("    {:?}", r);
    }
    */

    // For each merged range we insert a large gtoh call just after it's base
    // register is defined.  Other existing gtoh calls are replaced with:
    //    addi new_base, offset

    // allocate new_base registers
    let mut by_base: BTreeMap<Reg, (Reg, Reg, GuestRange)> = BTreeMap::new();
    for r in &ranges {
        by_base.insert(
            r.base,
            (Reg(highest_reg, None), Reg(highest_reg + 1, None), *r),
        );
        highest_reg += 2;
    }

    let mut result = Vec::new();
    for i in instrs {
        match i {
            Assign { rd, rval } => {
                if let Some((new_guest, new_base, gr)) = by_base.get(rd) {
                    result.push(*i);
                    result.push(Assign {
                        rd: *new_guest,
                        rval: Imm {
                            op: Addi,
                            rs: gr.base,
                            imm: gr.offset,
                        },
                    });
                    result.push(Assign {
                        rd: *new_base,
                        rval: Gtoh {
                            guest: *new_guest,
                            len: gr.len,
                            perms: gr.perms,
                        },
                    });
                } else {
                    match rval {
                        Gtoh { guest, len, perms } => {
                            if let Some(range) = extract_range(guest, *len, *perms, &defs) {
                                // debug!("range.base = {}", range.base);
                                let (_, new_base, gr) = by_base.get(&range.base).unwrap();
                                result.push(Assign {
                                    rd: *rd,
                                    rval: Imm {
                                        op: Addi,
                                        rs: *new_base,
                                        imm: range.offset - gr.offset,
                                    },
                                });
                            } else {
                                result.push(*i);
                            }
                        }
                        _ => {
                            result.push(*i);
                        }
                    }
                }
            }
            _ => {
                result.push(*i);
            }
        }
    }

    result
}

//--------------------------------

// Remove store instructions of the form: Sx dest { Lx { dest } }
fn opt_redundant_stores(instrs: &[IR]) -> Vec<IR> {
    let mut defs = BTreeMap::new();
    for i in instrs {
        match i {
            Assign { rd, rval } => {
                defs.insert(*rd, *rval);
            }
            _ => {}
        }
    }

    let mut result = Vec::new();
    for i in instrs {
        match i {
            Sb { rs1, rs2 } => match defs.get(rs2).unwrap() {
                Lb { rs } => {
                    if rs != rs1 {
                        result.push(*i);
                    }
                }
                _ => {
                    result.push(*i);
                }
            },
            Sh { rs1, rs2 } => match defs.get(rs2).unwrap() {
                Lh { rs } => {
                    if rs != rs1 {
                        result.push(*i);
                    }
                }
                _ => {
                    result.push(*i);
                }
            },
            Sw { rs1, rs2 } => match defs.get(rs2).unwrap() {
                Lw { rs } => {
                    if rs != rs1 {
                        result.push(*i);
                    }
                }
                _ => {
                    result.push(*i);
                }
            },
            Sd { rs1, rs2 } => match defs.get(rs2).unwrap() {
                Ld { rs } => {
                    if rs != rs1 {
                        result.push(*i);
                    }
                }
                _ => {
                    result.push(*i);
                }
            },
            _ => {
                result.push(*i);
            }
        }
    }

    result
}

//--------------------------------

fn emit(r: &mut Vec<IR>, reg: &Reg, defs: &BTreeMap<Reg, RValue>, seen: &mut BTreeSet<Reg>) {
    if seen.contains(reg) {
        return;
    }

    let rval = defs.get(reg).unwrap();
    match rval {
        Gbase => {}
        Gtoh { guest, .. } => emit(r, guest, defs, seen),
        Li { .. } => {}
        Test { rs1, rs2, .. } => {
            emit(r, rs1, defs, seen);
            emit(r, rs2, defs, seen);
        }
        Cond { t, rs1, rs2 } => {
            emit(r, t, defs, seen);
            emit(r, rs1, defs, seen);
            emit(r, rs2, defs, seen);
        }
        Ld { rs } => {
            emit(r, rs, defs, seen);
        }
        Lb { rs } => {
            emit(r, rs, defs, seen);
        }
        Lh { rs } => {
            emit(r, rs, defs, seen);
        }
        Lw { rs } => {
            emit(r, rs, defs, seen);
        }
        Lbu { rs } => {
            emit(r, rs, defs, seen);
        }
        Lhu { rs } => {
            emit(r, rs, defs, seen);
        }
        Lwu { rs } => {
            emit(r, rs, defs, seen);
        }

        Imm { rs, .. } => {
            emit(r, rs, defs, seen);
        }
        Shift { rs, .. } => {
            emit(r, rs, defs, seen);
        }
        Bin { rs1, rs2, .. } => {
            emit(r, rs1, defs, seen);
            emit(r, rs2, defs, seen);
        }
    }
    r.push(Assign {
        rd: *reg,
        rval: *rval,
    });
    seen.insert(*reg);
}

/// Reorders instructions to try and keep assignments close to their use.  Also
/// has the effect of removing dead code.
fn reorder(instrs: &[IR]) -> Vec<IR> {
    let mut r = Vec::new();
    let mut defs: BTreeMap<Reg, RValue> = BTreeMap::new();

    for ir in instrs {
        match ir {
            Assign { rd, rval } => {
                defs.insert(*rd, *rval);
            }
            _ => {
                // do nothing
            }
        }
    }

    let mut seen = BTreeSet::new();
    for ir in instrs {
        match ir {
            Assign { .. } => {
                // do nothing
            }
            Sb { rs1, rs2 } => {
                emit(&mut r, rs1, &defs, &mut seen);
                emit(&mut r, rs2, &defs, &mut seen);
                r.push(Sb {
                    rs1: *rs1,
                    rs2: *rs2,
                });
            }
            Sh { rs1, rs2 } => {
                emit(&mut r, rs1, &defs, &mut seen);
                emit(&mut r, rs2, &defs, &mut seen);
                r.push(Sh {
                    rs1: *rs1,
                    rs2: *rs2,
                });
            }
            Sw { rs1, rs2 } => {
                emit(&mut r, rs1, &defs, &mut seen);
                emit(&mut r, rs2, &defs, &mut seen);
                r.push(Sw {
                    rs1: *rs1,
                    rs2: *rs2,
                });
            }
            Sd { rs1, rs2 } => {
                emit(&mut r, rs1, &defs, &mut seen);
                emit(&mut r, rs2, &defs, &mut seen);
                r.push(Sd {
                    rs1: *rs1,
                    rs2: *rs2,
                });
            }
            Ecall => r.push(Ecall),
            Ebreak => r.push(Ebreak),
        }
    }

    r
}

//--------------------------------

fn optimise_(instrs: &[IR]) -> Vec<IR> {
    let new_instrs = opt_cse(instrs);
    let new_instrs = opt_noop(&new_instrs);
    let new_instrs = opt_simplify(&new_instrs);
    let new_instrs = opt_redundant_stores(&new_instrs);

    if new_instrs.len() == instrs.len() {
        new_instrs
    } else {
        optimise_(&new_instrs)
    }
}

fn optimise(instrs: &[IR]) -> Vec<IR> {
    let new_instrs = opt_cse(instrs);
    let new_instrs = opt_noop(&new_instrs);
    let new_instrs = opt_simplify(&new_instrs);
    let new_instrs = opt_gtoh(&new_instrs);

    // Loop around some of the passes
    reorder(&optimise_(&new_instrs))
}

//--------------------------------

pub fn to_ir(insts: &[(Inst, u8)], opt: bool) -> Vec<IR> {
    let mut b = Builder::default();
    riscv_to_ir(&mut b, insts);
    if opt {
        let ir = b.buffer;
        optimise(&ir)
    } else {
        b.buffer
    }
}

//--------------------------------

// Renumbers all the registers used in IR into ascending
// order.  Only useful if you're printing the instructions.
pub fn renumber(instrs: &[IR]) -> Vec<IR> {
    // let mut defs: BTreeMap<Reg, RValue> = BTreeMap::new();
    let mut substs: BTreeMap<Reg, Reg> = BTreeMap::new();
    let mut next_reg = 0;

    let mut r = Vec::new();
    for ir in instrs {
        match ir {
            Assign { rd, rval } => {
                let rval = apply_substitutions(rval, &substs);
                let new_reg = Reg(next_reg, rd.1);
                next_reg += 1;
                substs.insert(*rd, new_reg);
                r.push(Assign { rd: new_reg, rval });
            }
            Sb { rs1, rs2 } => r.push(Sb {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sh { rs1, rs2 } => r.push(Sh {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sw { rs1, rs2 } => r.push(Sw {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            Sd { rs1, rs2 } => r.push(Sd {
                rs1: subst_reg(*rs1, &substs),
                rs2: subst_reg(*rs2, &substs),
            }),
            _ => {
                r.push(*ir);
            }
        }
    }

    r
}

//--------------------------------
