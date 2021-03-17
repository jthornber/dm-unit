use crate::fixture::*;
use crate::memory::*;
use crate::decode::*;

use anyhow::Result;
use log::info;

pub mod block_device;
pub mod block_manager;
pub mod rw_semaphore;

use Reg::*;

//-------------------------------

pub fn printk(fix: &mut Fixture) -> Result<()> {
    let msg = fix.vm.mem.read_string(Addr(fix.vm.reg(A0)))?;
    info!(
        "printk(\"{}\", 0x{:x}, 0x{:x}, 0x{:x}, 0x{:x})",
        &msg[2..],
        fix.vm.reg(A1),
        fix.vm.reg(A2),
        fix.vm.reg(A3),
        fix.vm.reg(A4)
    );
    fix.vm.ret(0);
    Ok(())
}

pub fn memcpy(fix: &mut Fixture) -> Result<()> {
    let dest = Addr(fix.vm.reg(A0));
    let src = Addr(fix.vm.reg(A1));
    let len = fix.vm.reg(A2);

    // Let's check the bounds before allocating the intermediate buffer.
    fix.vm.mem.check_perms(src, Addr(src.0 + len), PERM_READ)?;
    fix.vm
        .mem
        .check_perms(dest, Addr(dest.0 + len), PERM_WRITE)?;

    let mut bytes = vec![0u8; len as usize];
    fix.vm.mem.read(src, &mut bytes, PERM_READ)?;
    fix.vm.mem.write(dest, &bytes, PERM_WRITE)?;
    fix.vm.ret(dest.0);

    // The vm instr count should reflect this expensive operation.
    fix.vm.stats.instrs += (len * 3) / 8;
    Ok(())
}

pub fn kmalloc(fix: &mut Fixture) -> Result<()> {
    let len = fix.vm.reg(Reg::A0);
    let ptr = fix.vm.mem.alloc(len as usize)?;
    fix.vm.ret(ptr.0);
    Ok(())
}

pub fn kfree(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(Reg::A0));
    fix.vm.mem.free(ptr)?;
    fix.vm.ret(0);
    Ok(())
}

pub fn memset(fix: &mut Fixture) -> Result<()> {
    let base = Addr(fix.vm.reg(A0));
    let v = fix.vm.reg(A1) as u8;
    let len = fix.vm.reg(A2) as usize;
    let mut bytes = vec![0u8; len];
    for b in &mut bytes {
        *b = v;
    }
    fix.vm.mem.write(base, &bytes, PERM_WRITE)?;
    fix.vm.ret(0);
    Ok(())
}

//-------------------------------

/// Attaches a standard set of global implementations.
/// eg, kmalloc, kfree, block_manager etc.
pub fn standard_globals(fix: &mut Fixture) -> Result<()> {
    use crate::stubs::block_manager::*;

    fix.stub("__list_add_valid", 1)?;
    fix.stub("__list_del_entry_valid", 1)?;

    fix.stub("__raw_spin_lock_init", 0)?;
    fix.stub("_raw_spin_lock", 0)?;
    fix.stub("_raw_spin_unlock", 0)?;
    fix.stub("__mutex_init", 0)?;
    fix.stub("___ratelimit", 0)?;

    fix.at_func("dm_block_data", Box::new(bm_block_data))?;
    fix.at_func("dm_block_location", Box::new(bm_block_location))?;
    fix.at_func("dm_block_manager_create", Box::new(bm_create))?;
    fix.at_func("dm_block_manager_destroy", Box::new(bm_destroy))?;
    fix.at_func("dm_bm_block_size", Box::new(bm_block_size))?;
    fix.at_func("dm_bm_checksum", Box::new(bm_checksum))?;
    fix.at_func("dm_bm_flush", Box::new(bm_flush))?;
    fix.at_func("dm_bm_is_read_only", Box::new(bm_is_read_only))?;
    fix.at_func("dm_bm_nr_blocks", Box::new(bm_nr_blocks))?;
    fix.at_func("dm_bm_prefetch", Box::new(bm_prefetch))?;
    fix.at_func("dm_bm_read_lock", Box::new(bm_read_lock))?;
    fix.at_func("dm_bm_read_try_lock", Box::new(bm_read_lock))?;
    fix.at_func("dm_bm_set_read_only", Box::new(bm_set_read_only))?;
    fix.at_func("dm_bm_set_read_write", Box::new(bm_set_read_write))?;
    fix.at_func("dm_bm_unlock", Box::new(bm_unlock))?;
    fix.at_func("dm_bm_write_lock", Box::new(bm_write_lock))?;
    fix.at_func("dm_bm_write_lock_zero", Box::new(bm_write_lock_zero))?;
    fix.at_func("kfree", Box::new(kfree))?;
    fix.at_func("__kmalloc", Box::new(kmalloc))?;
    fix.at_func("kmalloc_order", Box::new(kmalloc))?;
    fix.at_func("memcpy", Box::new(memcpy))?;
    fix.at_func("memmove", Box::new(memcpy))?;
    fix.at_func("memset", Box::new(memset))?;
    fix.at_func("printk", Box::new(printk))?;

    rw_semaphore::rw_sem_stubs(fix)?;
    Ok(())
}
