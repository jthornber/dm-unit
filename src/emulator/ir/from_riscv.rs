use std::collections::BTreeMap;

use crate::emulator::ir::ir::*;
use crate::emulator::memory::*;
use crate::emulator::riscv::{self, *};

use BinOp::*;
use ImmOp::*;
use RValue::*;
use ShiftOp::*;
use IR::*;

//------------------------------------------------

#[derive(Default)]
struct Builder {
    buffer: Vec<IR>,
    current_reg: u32,
    guest_regs: BTreeMap<riscv::Reg, IReg>,
}

impl Builder {
    fn buffer(self) -> Vec<IR> {
        self.buffer
    }

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
    fn def_greg(&mut self, greg: &riscv::Reg) -> IReg {
        let reg = IReg(self.current_reg, Some(*greg));
        self.current_reg += 1;
        self.guest_regs.insert(*greg, reg);
        reg
    }

    /// Returns the IR register that contains the guest reg
    fn ref_greg(&self, greg: &riscv::Reg) -> IReg {
        *self.guest_regs.get(greg).unwrap()
    }

    /// Call this when you want to mutate the value of a guest register.
    /// It returns (old, new)
    fn mut_greg(&mut self, greg: &riscv::Reg) -> (IReg, IReg) {
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

    fn next_reg(&mut self) -> IReg {
        let r = self.current_reg;
        self.current_reg += 1;
        IReg(r, None)
    }

    /// Pushes a new assignment operation
    fn assign(&mut self, rd: IReg, rval: RValue) {
        self.push(IR::Assign { rd, rval });
    }

    /// Generates a new register, and pushes an assignment to it.
    fn assign_next(&mut self, rval: RValue) -> IReg {
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

    fn load<F: FnOnce(IReg) -> RValue>(
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

    fn store<F: FnOnce(IReg, IReg) -> IR>(
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

fn riscv_to_ir_(b: &mut Builder, insts: &[(Inst, u8)]) {
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

pub fn riscv_to_ir(insts: &[(Inst, u8)]) -> Vec<IR> {
    let mut b = Builder::default();
    riscv_to_ir_(&mut b, insts);
    b.buffer()
}

//----------------------------------
