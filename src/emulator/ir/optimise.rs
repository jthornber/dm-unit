use std::collections::{BTreeMap, BTreeSet};

use crate::emulator::ir::ir::*;

use ImmOp::*;
use RValue::*;
use ShiftOp::*;
use IR::*;

//----------------------------------------------------------------

fn subst_reg(r: IReg, substs: &BTreeMap<IReg, IReg>) -> IReg {
    if let Some(old) = substs.get(&r) {
        *old
    } else {
        r
    }
}

fn apply_substitutions(rval: &RValue, substs: &BTreeMap<IReg, IReg>) -> RValue {
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
    let mut seen: BTreeMap<RValue, IReg> = BTreeMap::new();
    let mut substs: BTreeMap<IReg, IReg> = BTreeMap::new();

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
fn is_noop(rval: &RValue) -> Option<IReg> {
    let check = |t: bool, rs: &IReg| -> Option<IReg> {
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
    let mut substs: BTreeMap<IReg, IReg> = BTreeMap::new();

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

fn simplify(rval: &RValue, defs: &BTreeMap<IReg, RValue>) -> RValue {
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
                let rval = simplify(rval, &defs);
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
    base: IReg,
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
    guest: &IReg,
    len: u32,
    perms: u8,
    defs: &BTreeMap<IReg, RValue>,
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
        if let Assign { rd, rval } = i {
            defs.insert(*rd, *rval);

            if rd.0 > highest_reg {
                highest_reg = rd.0;
            }
        }
    }

    let mut ranges = Vec::new();
    for i in instrs {
        if let Assign {
                rval: Gtoh { guest, len, perms },
                ..
            } = i {
            if let Some(range) = extract_range(guest, *len, *perms, &defs) {
                ranges.push(range);
            }
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
    let mut by_base: BTreeMap<IReg, (IReg, IReg, GuestRange)> = BTreeMap::new();
    for r in &ranges {
        by_base.insert(
            r.base,
            (IReg(highest_reg, None), IReg(highest_reg + 1, None), *r),
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
        if let Assign { rd, rval } = i {
            defs.insert(*rd, *rval);
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

fn emit(r: &mut Vec<IR>, reg: &IReg, defs: &BTreeMap<IReg, RValue>, seen: &mut BTreeSet<IReg>) {
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
    let mut defs: BTreeMap<IReg, RValue> = BTreeMap::new();

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

pub fn optimise(instrs: &[IR]) -> Vec<IR> {
    let new_instrs = opt_cse(instrs);
    let new_instrs = opt_noop(&new_instrs);
    let new_instrs = opt_simplify(&new_instrs);
    let new_instrs = opt_gtoh(&new_instrs);

    // Loop around some of the passes
    reorder(&optimise_(&new_instrs))
}

// Renumbers all the registers used in IR into ascending
// order.  Only useful if you're printing the instructions.
pub fn renumber(instrs: &[IR]) -> Vec<IR> {
    // let mut defs: BTreeMap<Reg, RValue> = BTreeMap::new();
    let mut substs: BTreeMap<IReg, IReg> = BTreeMap::new();
    let mut next_reg = 0;

    let mut r = Vec::new();
    for ir in instrs {
        match ir {
            Assign { rd, rval } => {
                let rval = apply_substitutions(rval, &substs);
                let new_reg = IReg(next_reg, rd.1);
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

//----------------------------------------------------------------
