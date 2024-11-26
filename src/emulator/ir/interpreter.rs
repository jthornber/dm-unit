use crate::emulator::ir::ir::*;
use crate::emulator::memory::*;

use BinOp::*;
use ImmOp::*;
use RValue::*;
use ShiftOp::*;
use TestOp::*;
use IR::*;

//----------------------------------------------------------------

fn single_instr(
    instr: &IR,
    ir_regs: &mut [u64],
    registers: &mut [u64],
    mem: &mut Memory,
) -> Result<()> {
    let reg = |r: &IReg| ir_regs[r.0 as usize];
    let to_bool = |b| if b { 1 } else { 0 };

    match instr {
        Assign { rd, rval } => {
            // Implement the assignment operations
            ir_regs[rd.0 as usize] = match rval {
                Gbase => {
                    // Gbase returns a pointer to the guest register file (registers).
                    // Since we're simulating, we'll represent this as a pointer (address)
                    // to the `registers` array.
                    registers.as_mut_ptr() as u64
                }
                Gtoh { guest, len, perms } => {
                    // Convert guest address to host address.
                    let guest_addr = reg(guest);
                    mem.guest_to_host(Addr(guest_addr), Addr(guest_addr + *len as u64), *perms)?
                }
                Li { imm } => {
                    // Load immediate value
                    *imm as u64
                }
                Test { op, rs1, rs2 } => match op {
                    Eq => to_bool(reg(rs1) == reg(rs2)),
                    Ne => to_bool(reg(rs1) != reg(rs2)),
                    Lt => to_bool((reg(rs1) as i64) < (reg(rs2) as i64)),
                    Ge => to_bool((reg(rs1) as i64) >= (reg(rs2) as i64)),
                    Ltu => to_bool(reg(rs1) < reg(rs2)),
                    Geu => to_bool(reg(rs1) >= reg(rs2)),
                },
                Cond { t, rs1, rs2 } => {
                    let t = reg(t) != 0;
                    if t {
                        reg(rs1)
                    } else {
                        reg(rs2)
                    }
                }
                // FIXME: factor out common L* code
                Ld { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut i64) };
                    value as u64
                }
                Lb { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut i8) };
                    value as i64 as u64
                }
                Lh { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut i16) };
                    value as i64 as u64
                }
                Lw { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut i32) };
                    value as i64 as u64
                }
                Lbu { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut u8) };
                    value as u64
                }
                Lhu { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut u16) };
                    value as u64
                }
                Lwu { rs } => {
                    let addr = reg(rs);
                    let value = unsafe { *(addr as *mut u32) };
                    value as u64
                }
                Imm { op, rs, imm } => match op {
                    Addi => reg(rs).wrapping_add(*imm as i64 as u64),
                    Addiw => reg(rs).wrapping_add(*imm as u32 as u64) as i32 as i64 as u64,
                    Slti => to_bool((reg(rs) as i64) < (*imm as i64)),
                    Sltiu => to_bool(reg(rs) < (*imm as u64)),
                    Xori => reg(rs) ^ (*imm as i64 as u64),
                    Ori => reg(rs) | (*imm as i64 as u64),
                    Andi => reg(rs) & (*imm as i64 as u64),
                },
                Shift { op, rs, shamt } => match op {
                    Slli => reg(rs) << shamt,
                    Slliw => {
                        let rs = reg(rs) as i32;
                        (rs << shamt) as i64 as u64
                    }
                    Srli => reg(rs) >> shamt,
                    Srliw => {
                        let rs = reg(rs) as u32;
                        (rs >> shamt) as i32 as i64 as u64
                    }
                    Sraiw => {
                        let rs = reg(rs) as i32;
                        (rs >> shamt) as i64 as u64
                    }
                    Srai => ((reg(rs) as i64) >> shamt) as u64,
                },
                Bin { op, rs1, rs2 } => match op {
                    Add => reg(rs1).wrapping_add(reg(rs2)),
                    Addw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        rs1.wrapping_add(rs2) as i32 as i64 as u64
                    }
                    Sub => reg(rs1).wrapping_sub(reg(rs2)),
                    Subw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        rs1.wrapping_sub(rs2) as i32 as i64 as u64
                    }
                    Sll => {
                        let shamt = reg(rs2) & 0b111111;
                        reg(rs1) << shamt
                    }
                    Sllw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        let shamt = rs2 & 0b11111;
                        (rs1 << shamt) as i32 as i64 as u64
                    }
                    Srlw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        let shamt = rs2 & 0b11111;
                        (rs1 >> shamt) as i32 as i64 as u64
                    }
                    Sraw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        let shamt = rs2 & 0b11111;
                        ((rs1 as i32) >> shamt) as i64 as u64
                    }
                    Slt => to_bool((reg(rs1) as i64) < (reg(rs2) as i64)),
                    Sltu => to_bool(reg(rs1) < reg(rs2)),
                    Xor => reg(rs1) ^ reg(rs2),
                    Srl => {
                        let shamt = reg(rs2) & 0b111111;
                        reg(rs1) >> shamt
                    }
                    Sra => {
                        let shamt = reg(rs2) & 0b111111;
                        ((reg(rs1) as i64) >> shamt) as u64
                    }
                    Or => reg(rs1) | reg(rs2),
                    And => reg(rs1) & reg(rs2),
                    Mul => reg(rs1).wrapping_mul(reg(rs2)),
                    Mulh => {
                        let rs1 = reg(rs1) as i64 as u128;
                        let rs2 = reg(rs2) as i64 as u128;
                        (rs1.wrapping_mul(rs2) >> 64) as u64
                    }
                    Mulhsu => {
                        let rs1 = reg(rs1) as i64 as u128;
                        let rs2 = reg(rs2) as u128;
                        (rs1.wrapping_mul(rs2) >> 64) as u64
                    }
                    Mulhu => {
                        let rs1 = reg(rs1) as u128;
                        let rs2 = reg(rs2) as u128;
                        (rs1.wrapping_mul(rs2) >> 64) as u64
                    }
                    Mulw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        let v = rs1.wrapping_mul(rs2);
                        v as i32 as u64
                    }
                    Div => {
                        let rs1 = reg(rs1) as i64;
                        let rs2 = reg(rs2) as i64;
                        let v = if rs2 == 0 { -1 } else { rs1.wrapping_div(rs2) };
                        v as u64
                    }
                    Divu => {
                        let rs1 = reg(rs1);
                        let rs2 = reg(rs2);
                        if rs2 == 0 {
                            u64::MAX
                        } else {
                            rs1.wrapping_div(rs2)
                        }
                    }
                    Divw => {
                        let rs1 = reg(rs1) as i32;
                        let rs2 = reg(rs2) as i32;
                        let v = if rs2 == 0 { -1 } else { rs1.wrapping_div(rs2) };
                        v as u64
                    }
                    Divuw => {
                        let rs1 = reg(rs1) as u32;
                        let rs2 = reg(rs2) as u32;
                        let v = if rs2 == 0 {
                            u32::MAX
                        } else {
                            rs1.wrapping_div(rs2)
                        };
                        v as i32 as u64
                    }
                    Rem => {
                        let rs1 = reg(rs1) as i64;
                        let rs2 = reg(rs2) as i64;
                        let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                        v as u64
                    }
                    Remu => {
                        let rs1 = reg(rs1);
                        let rs2 = reg(rs2);
                        if rs2 == 0 {
                            rs1
                        } else {
                            rs1.wrapping_rem(rs2)
                        }
                    }
                    Remw => {
                        let rs1 = reg(rs1) as i32;
                        let rs2 = reg(rs2) as i32;
                        let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                        v as u64
                    }
                    Remuw => {
                        let rs1 = reg(rs1);
                        let rs2 = reg(rs2);
                        let v = if rs2 == 0 { rs1 } else { rs1.wrapping_rem(rs2) };
                        v as i32 as u64
                    }
                },
            }
        }
        Sb { rs1, rs2 } => {
            // `rs1` is the host address, `rs2` is the value to store (byte)
            let addr = reg(rs1);
            let value = reg(rs2) as u8;

            unsafe {
                // Write the byte value to the host memory address.
                let ptr = addr as *mut u8;
                *ptr = value;
            }
        }
        Sh { rs1, rs2 } => {
            // Similar to Sb, but for half-word (16 bits)
            let addr = reg(rs1);
            let value = reg(rs2) as u16;

            unsafe {
                let ptr = addr as *mut u16;
                *ptr = value;
            }
        }
        Sw { rs1, rs2 } => {
            // Store word (32 bits)
            let addr = reg(rs1);
            let value = reg(rs2) as u32;

            unsafe {
                let ptr = addr as *mut u32;
                *ptr = value;
            }
        }
        Sd { rs1, rs2 } => {
            // Store double word (64 bits)
            let addr = ir_regs[rs1.0 as usize];
            let value = ir_regs[rs2.0 as usize];

            unsafe {
                let ptr = addr as *mut u64;
                *ptr = value;
            }
        }
        Ecall => todo!(),
        Ebreak => todo!(),
    }
    Ok(())
}

pub fn interpret(code: &[IR], registers: &mut [u64], mem: &mut Memory) -> Result<()> {
    // Determine the number of IR registers used
    let max_reg = code
        .iter()
        .flat_map(|instr| match instr {
            Assign { rd, rval } => {
                let mut regs = vec![rd.0];
                match rval {
                    RValue::Gtoh { guest, .. } => regs.push(guest.0),
                    RValue::Test { rs1, rs2, .. } => {
                        regs.push(rs1.0);
                        regs.push(rs2.0);
                    }
                    RValue::Cond { t, rs1, rs2 } => {
                        regs.push(t.0);
                        regs.push(rs1.0);
                        regs.push(rs2.0);
                    }
                    RValue::Ld { rs }
                    | RValue::Lb { rs }
                    | RValue::Lh { rs }
                    | RValue::Lw { rs }
                    | RValue::Lbu { rs }
                    | RValue::Lhu { rs }
                    | RValue::Lwu { rs } => {
                        regs.push(rs.0);
                    }
                    RValue::Imm { rs, .. } | RValue::Shift { rs, .. } => {
                        regs.push(rs.0);
                    }
                    RValue::Bin { rs1, rs2, .. } => {
                        regs.push(rs1.0);
                        regs.push(rs2.0);
                    }
                    _ => {}
                }
                regs
            }
            Sb { rs1, rs2 } | Sh { rs1, rs2 } | Sw { rs1, rs2 } | Sd { rs1, rs2 } => {
                vec![rs1.0, rs2.0]
            }
            _ => vec![],
        })
        .max()
        .unwrap_or(0);

    // Initialize IR register file
    let mut ir_regs = vec![0u64; (max_reg + 1) as usize];

    for instr in code {
        single_instr(instr, &mut ir_regs, registers, mem)?;
    }

    Ok(())
}

//----------------------------------------------------------------
