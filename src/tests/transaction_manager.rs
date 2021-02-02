use crate::decode::*;
use crate::memory::*;
use crate::tests::fixture::*;

use anyhow::{Result};

use Reg::*;

//-------------------------------

fn tm_func(fix: &mut Fixture, tm_func: &str, tm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.call_with_errno(tm_func)
}

// Returns (tm, sm) pair.
pub fn dm_tm_create(fix: &mut Fixture, bm: Addr, sb_loc: u64) -> Result<(Addr, Addr)> {
    fix.vm.set_reg(A0, bm.0);
    fix.vm.set_reg(A1, sb_loc);
    let (mut fix, tm_result) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A2, tm_result.0);
    let (mut fix, sm_result) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A3, sm_result.0);
    fix.call_with_errno("dm_tm_create_with_sm")?;

    let tm = fix.vm.mem.read_into::<u64>(tm_result, PERM_READ)?;
    let sm = fix.vm.mem.read_into::<u64>(sm_result, PERM_READ)?;

    Ok((Addr(tm), Addr(sm)))
}

pub fn dm_tm_destroy(fix: &mut Fixture, tm: Addr) -> Result<()> {
    tm_func(fix, "dm_tm_destroy", tm)
}

pub fn dm_tm_pre_commit(fix: &mut Fixture, tm: Addr) -> Result<()> {
    tm_func(fix, "dm_tm_pre_commit", tm)
}

pub fn dm_tm_commit(fix: &mut Fixture, tm: Addr) -> Result<()> {
    tm_func(fix, "dm_tm_commit", tm)
}

pub fn dm_tm_new_block(fix: &mut Fixture, tm: Addr, validator: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, validator.0);

    let (mut fix, ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A2, ptr.0);
    fix.call_with_errno("dm_tm_new_block")?;
    let r = fix.vm.mem.read_into::<u64>(ptr, PERM_READ)?;
    Ok(Addr(r))
}

// Returns (block, inc_children)
pub fn dm_tm_shadow_block(fix: &mut Fixture, tm: Addr, orig: u64, validator: Addr) -> Result<(Addr, bool)> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, orig);
    fix.vm.set_reg(A2, validator.0);

    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A3, result_ptr.0);
    let (mut fix, inc_children) = auto_alloc(&mut *fix, 4)?;
    fix.vm.set_reg(A4, inc_children.0);

    fix.call_with_errno("dm_tm_shadow_block")?;

    let block = Addr(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?);
    let inc_children = fix.vm.mem.read_into::<i32>(inc_children, PERM_READ)?;
    Ok((block, inc_children != 0))
}

pub fn dm_tm_read_lock(fix: &mut Fixture, tm: Addr, b: u64, validator: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, validator.0);

    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A3, result_ptr.0);

    fix.call_with_errno("dm_tm_read_lock")?;

    let block = Addr(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?);
    Ok(block)
}

pub fn dm_tm_unlock(fix: &mut Fixture, tm: Addr, b: Addr) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, b.0);
    fix.call("dm_tm_unlock")?;
    Ok(())
}

pub fn dm_tm_inc(fix: &mut Fixture, tm: Addr, b: u64) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, b);
    fix.call("dm_tm_inc")?;
    Ok(())
}

pub fn dm_tm_dec(fix: &mut Fixture, tm: Addr, b: u64) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, b);
    fix.call("dm_tm_dec")?;
    Ok(())
}

pub fn dm_tm_ref(fix: &mut Fixture, tm: Addr, b: u64) -> Result<u32> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, b);

    let (mut fix, result_ptr) = auto_alloc(fix, 4)?;
    fix.vm.set_reg(A2, result_ptr.0);

    fix.call_with_errno("dm_tm_ref")?;

    let count = fix.vm.mem.read_into::<u32>(result_ptr, PERM_READ)?;
    Ok(count)
}

//-------------------------------
