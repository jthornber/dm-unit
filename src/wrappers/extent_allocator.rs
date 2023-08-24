use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;

use anyhow::{anyhow, Result};
use libc::ENOSPC;
use roaring::RoaringBitmap;
use std::sync::{Arc, Mutex};
use Reg::*;

//-------------------------------

pub fn extent_allocator_create(fix: &mut Fixture, nr_blocks: u64) -> Result<Addr> {
    fix.vm.set_reg(A0, nr_blocks);
    fix.call("dm_extent_allocator_create")?;
    let r = fix.vm.reg(A0);
    if r == 0 {
        return Err(anyhow!("dm_extent_allocator_create failed"));
    }
    Ok(Addr(r))
}

pub fn extent_allocator_destroy(fix: &mut Fixture, ea_addr: Addr) -> Result<()> {
    fix.vm.set_reg(A0, ea_addr.0);
    fix.call("dm_extent_allocator_destroy")?;
    Ok(())
}

pub fn extent_allocator_reset(fix: &mut Fixture, ea_addr: Addr) -> Result<()> {
    fix.vm.set_reg(A0, ea_addr.0);
    fix.call("dm_extent_allocator_reset")?;
    Ok(())
}

pub fn extent_allocator_resize(fix: &mut Fixture, ea_addr: Addr, nr_blocks: u64) -> Result<()> {
    fix.vm.set_reg(A0, ea_addr.0);
    fix.vm.set_reg(A1, nr_blocks);
    fix.call("dm_extent_allocator_resize")?;
    Ok(())
}

pub fn extent_allocator_dump(fix: &mut Fixture, ea_addr: Addr) -> Result<()> {
    fix.vm.set_reg(A0, ea_addr.0);
    fix.call("dm_extent_allocator_dump")?;
    Ok(())
}

pub fn alloc_context_get(fix: &mut Fixture, ea_addr: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, ea_addr.0);
    let (mut fix, result_ptr) = auto_alloc(fix, 48)?;
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call("dm_alloc_context_get")?;
    Ok(fix.take())
}

pub fn alloc_context_put(fix: &mut Fixture, ac_addr: Addr) -> Result<()> {
    fix.vm.set_reg(A0, ac_addr.0);
    fix.call("dm_alloc_context_put")?;
    fix.vm.mem.free(ac_addr)?;
    Ok(())
}

fn alloc_callback(fix: &mut Fixture) -> Result<()> {
    let context = Addr(fix.vm.reg(A0));
    let mut allocated = fix
        .contexts
        .get::<Arc<Mutex<RoaringBitmap>>>(&context)
        .unwrap()
        .lock()
        .unwrap();

    let b = fix.vm.reg(A1);
    let e = fix.vm.reg(A2);
    let result = Addr(fix.vm.reg(A3));

    for b in b..e {
        if allocated.contains(b as u32) {
            continue;
        }

        allocated.insert(b as u32);

        // Write b to the result ptr
        fix.vm.mem.write_out(b, result, PERM_WRITE)?;
        fix.vm.ret(0);
        return Ok(());
    }

    // Out of space
    fix.vm.ret(-ENOSPC as u64);
    Ok(())
}

pub fn alloc_context_alloc(
    fix: &mut Fixture,
    ac_addr: Addr,
    allocated: &Arc<Mutex<RoaringBitmap>>,
) -> Result<Option<u64>> {
    fix.contexts.insert(ac_addr, allocated.clone());
    let (mut fix, callback_ptr) = auto_ebreak(fix)?;
    fix.bp_at_addr(callback_ptr, Box::new(alloc_callback));

    fix.vm.set_reg(A0, ac_addr.0);
    fix.vm.set_reg(A1, callback_ptr.0);
    fix.vm.set_reg(A2, ac_addr.0);

    let (mut fix, result_ptr) = auto_alloc(&mut fix, 8)?;
    fix.vm.set_reg(A3, result_ptr.0);

    fix.call("dm_alloc_context_alloc")?;

    fix.bp_rm(callback_ptr);
    fix.contexts.remove::<Arc<Mutex<RoaringBitmap>>>(&ac_addr);

    let errno = fix.vm.reg(A0) as i32;
    if errno == 0 {
        let r = fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?;
        Ok(Some(r))
    } else if errno == -ENOSPC {
        Ok(None)
    } else {
        Err(anyhow!("dm_alloc_context_alloc() failed"))
    }
}
