use crate::block_manager::*;
use crate::emulator::memory::{Addr, PERM_READ, PERM_WRITE};
use crate::emulator::riscv::Reg;
use crate::fixture::*;
use crate::guest::*;
use crate::stubs::block_device::*;

use anyhow::{anyhow, Result};
use crc32c::crc32c;
use log::*;
use std::sync::Arc;
use thinp::io_engine::*;

use Reg::*;

//-------------------------------

pub fn bm_create(fix: &mut Fixture) -> Result<()> {
    let bdev_ptr = Addr(fix.vm.reg(A0));
    let bdev = read_guest::<BlockDevice>(&fix.vm.mem, bdev_ptr)?;

    debug!("inode address: {:?}", bdev.inode);
    let inode = read_guest::<INode>(&fix.vm.mem, bdev.inode)?;
    let block_size = fix.vm.reg(A1);
    let _max_held_per_thread = fix.vm.reg(A2);

    let nr_blocks = inode.nr_sectors / (block_size / 512);

    let guest_addr = fix
        .vm
        .mem
        .alloc_bytes(vec![0u8; 4], PERM_READ | PERM_WRITE)?;
    let bm = Arc::new(BlockManager::new(nr_blocks, guest_addr));
    fix.contexts.insert(guest_addr, bm);
    fix.vm.ret(guest_addr.0);
    Ok(())
}

pub fn bm_destroy(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm: Box<Arc<BlockManager>> = fix.contexts.remove(&bm_ptr);

    if bm.get_nr_held_blocks() > 0 {
        return Err(anyhow!(
            "dm_block_manager_destroy() called with blocks still held"
        ));
    }

    fix.vm.mem.free(bm_ptr)?;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_block_size(fix: &mut Fixture) -> Result<()> {
    fix.vm.ret(4096);
    Ok(())
}

pub fn bm_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm(fix, bm_ptr);
    let nr_blocks = bm.get_nr_blocks();
    fix.vm.ret(nr_blocks);
    Ok(())
}

pub fn get_bm(fix: &Fixture, bm_ptr: Addr) -> Arc<BlockManager> {
    fix.contexts
        .get::<Arc<BlockManager>>(&bm_ptr)
        .unwrap()
        .clone()
}

pub fn bm_read_lock(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let loc = fix.vm.reg(A1);
    let v_ptr = Addr(fix.vm.reg(A2));
    let result_ptr = fix.vm.reg(A3);
    let bm = get_bm(fix, bm_ptr);
    let guest_ptr = bm.read_lock(&mut fix.vm.mem, loc, v_ptr)?;

    // fill out result ptr
    fix.vm
        .mem
        .write_out::<u64>(guest_ptr.0, Addr(result_ptr), PERM_WRITE)?;

    // return success
    fix.vm.ret(0);
    Ok(())
}

fn write_lock_(fix: &mut Fixture, zero: bool) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let loc = fix.vm.reg(A1);
    let v_ptr = Addr(fix.vm.reg(A2));
    let result_ptr = fix.vm.reg(A3);
    let bm = get_bm(fix, bm_ptr);
    let guest_addr = if zero {
        bm.write_lock_zero(&mut fix.vm.mem, loc, v_ptr)?
    } else {
        bm.write_lock(&mut fix.vm.mem, loc, v_ptr)?
    };

    // fill out result ptr
    fix.vm
        .mem
        .write_out::<u64>(guest_addr.0, Addr(result_ptr), PERM_WRITE)?;

    // return success
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_write_lock(fix: &mut Fixture) -> Result<()> {
    write_lock_(fix, false)
}

pub fn bm_write_lock_zero(fix: &mut Fixture) -> Result<()> {
    write_lock_(fix, true)
}

pub fn bm_unlock(fix: &mut Fixture) -> Result<()> {
    let gb_ptr = Addr(fix.vm.reg(A0));
    let gb = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)?;
    let bm = get_bm(fix, gb.bm_ptr);
    bm.unlock(fix, gb_ptr)?;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_block_location(fix: &mut Fixture) -> Result<()> {
    let gb_ptr = fix.vm.reg(A0);
    let gb = read_guest::<GBlock>(&fix.vm.mem, Addr(gb_ptr))?;
    fix.vm.ret(gb.loc);
    Ok(())
}

pub fn bm_block_data(fix: &mut Fixture) -> Result<()> {
    let gb_ptr = fix.vm.reg(A0);
    let gb = read_guest::<GBlock>(&fix.vm.mem, Addr(gb_ptr))?;
    fix.vm.ret(gb.data.0);
    Ok(())
}

pub fn bm_flush(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm(fix, bm_ptr);
    bm.flush(fix)?;

    fix.vm.ret(0);
    Ok(())
}

// Our prefetch does nothing
pub fn bm_prefetch(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_forget(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let b = fix.vm.reg(A1);
    let bm = get_bm(fix, bm_ptr);
    bm.forget(b)?;

    fix.vm.ret(0);
    Ok(())
}

pub fn bm_unlock_move(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let gb_ptr = Addr(fix.vm.reg(A1));
    let new_location = fix.vm.reg(A2);
    let bm = get_bm(fix, bm_ptr);
    bm.unlock_move(fix, gb_ptr, new_location)?;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_is_read_only(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm(fix, bm_ptr);
    let result = if bm.is_read_only() { 1 } else { 0 };
    fix.vm.ret(result);
    Ok(())
}

pub fn bm_set_read_only(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm(fix, bm_ptr);
    bm.set_read_only(true);
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_set_read_write(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm(fix, bm_ptr);
    bm.set_read_only(false);
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_checksum(fix: &mut Fixture) -> Result<()> {
    let data = Addr(fix.vm.reg(A0));
    let len = fix.vm.reg(A1);
    let init_xor = fix.vm.reg(A2) as u32;

    let calc_csum = |bytes: &[u8]| {
        let mut csum = crc32c(&bytes[0..len as usize]) ^ 0xffffffff;
        csum ^= init_xor;
        csum
    };

    let csum = fix.vm.mem.read_some(data, PERM_READ, calc_csum)?;
    fix.vm.ret(csum as u64);

    fix.vm.stats.instrs += (len * 3) / 8;
    Ok(())
}

//-------------------------------
