use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::emulator::memory::*;

use anyhow::Result;
use log::*;

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

pub fn memcmp(fix: &mut Fixture) -> Result<()> {
    let s1 = Addr(fix.vm.reg(A0));
    let s2 = Addr(fix.vm.reg(A1));
    let len = fix.vm.reg(A2) as usize;

    let mut b1 = vec![0u8; len];
    fix.vm.mem.read(s1, &mut b1, PERM_READ)?;

    let mut b2 = vec![0u8; len];
    fix.vm.mem.read(s2, &mut b2, PERM_READ)?;

    let mut r: i64 = 0;
    
    for i in 0..len {
        if b1[i] < b2[i] {
            r = -1;
            break;
        } else if b1[i] > b2[i] {
            r = 1;
            break;
        }
    }

    fix.vm.ret(r as u64);
    fix.vm.stats.instrs += (len as u64 * 3) / 8;
    Ok(())
}

pub fn kmalloc(fix: &mut Fixture) -> Result<()> {
    let len = fix.vm.reg(Reg::A0);
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0u8; len as usize], PERM_READ | PERM_WRITE)?;
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

pub fn strncpy(fix: &mut Fixture) -> Result<()> {
    let dest = Addr(fix.vm.reg(A0));
    let src = Addr(fix.vm.reg(A1));
    let n = fix.vm.reg(A2);

    let mut buffer = Vec::new();
    fix.vm.mem.read_some(src, PERM_READ, |bytes| {
        for i in 0..usize::min(bytes.len(), n as usize) {
            if bytes[i] == 0 {
                break;
            }

            buffer.push(bytes[i]);
        }
    })?;

    // null terminate the string
    buffer.push(0);

    // write to the dest
    fix.vm.mem.write(dest, &buffer, PERM_WRITE)?;

    fix.vm.stats.instrs += ((buffer.len() * 3) / 8) as u64;
    fix.vm.ret(0);
    Ok(())
}

//-------------------------------

/// Attaches a standard set of global implementations.
/// eg, kmalloc, kfree, block_manager etc.
pub fn standard_globals(fix: &mut Fixture) -> Result<()> {
    use crate::stubs::block_manager::*;

    // Ignore any failures here, since what needs stubbing varies with
    // different modules.

    let _ = fix.stub("__list_add_valid", 1);
    let _ = fix.stub("__list_del_entry_valid", 1);

    let _ = fix.stub("__raw_spin_lock_init", 0);
    let _ = fix.stub("_raw_spin_lock", 0);
    let _ = fix.stub("_raw_spin_unlock", 0);
    let _ = fix.stub("__mutex_init", 0);
    let _ = fix.stub("mutex_lock", 0);
    let _ = fix.stub("mutex_unlock", 0);
    let _ = fix.stub("___ratelimit", 0);

    let _ = fix.at_func("dm_block_data", Box::new(bm_block_data));
    let _ = fix.at_func("dm_block_location", Box::new(bm_block_location));
    let _ = fix.at_func("dm_block_manager_create", Box::new(bm_create));
    let _ = fix.at_func("dm_block_manager_destroy", Box::new(bm_destroy));
    let _ = fix.at_func("dm_bm_block_size", Box::new(bm_block_size));
    let _ = fix.at_func("dm_bm_checksum", Box::new(bm_checksum));
    let _ = fix.at_func("dm_bm_flush", Box::new(bm_flush));
    let _ = fix.at_func("dm_bm_is_read_only", Box::new(bm_is_read_only));
    let _ = fix.at_func("dm_bm_nr_blocks", Box::new(bm_nr_blocks));
    let _ = fix.at_func("dm_bm_prefetch", Box::new(bm_prefetch));
    let _ = fix.at_func("dm_bm_forget", Box::new(bm_forget));
    let _ = fix.at_func("dm_bm_unlock_move", Box::new(bm_unlock_move));
    let _ = fix.at_func("dm_bm_read_lock", Box::new(bm_read_lock));
    let _ = fix.at_func("dm_bm_read_try_lock", Box::new(bm_read_lock));
    let _ = fix.at_func("dm_bm_set_read_only", Box::new(bm_set_read_only));
    let _ = fix.at_func("dm_bm_set_read_write", Box::new(bm_set_read_write));
    let _ = fix.at_func("dm_bm_unlock", Box::new(bm_unlock));
    let _ = fix.at_func("dm_bm_write_lock", Box::new(bm_write_lock));
    let _ = fix.at_func("dm_bm_write_lock_zero", Box::new(bm_write_lock_zero));
    let _ = fix.at_func("kfree", Box::new(kfree));
    let _ = fix.at_func("__kmalloc", Box::new(kmalloc));
    let _ = fix.at_func("kmalloc_order", Box::new(kmalloc));
    let _ = fix.at_func("memcpy", Box::new(memcpy));
    let _ = fix.at_func("memmove", Box::new(memcpy));
    let _ = fix.at_func("memcmp", Box::new(memcmp));
    let _ = fix.at_func("memset", Box::new(memset));
    let _ = fix.at_func("printk", Box::new(printk));
    let _ = fix.at_func("strncpy", Box::new(strncpy));

    rw_semaphore::rw_sem_stubs(fix)?;
    Ok(())
}
