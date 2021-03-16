use crate::block_manager::*;
use crate::decode::Reg;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::{Addr, PERM_READ, PERM_WRITE};
use crate::stubs::block_device::*;

use anyhow::{anyhow, Result};
use crc32c::crc32c;
use log::*;
use std::sync::Arc;
use thinp::io_engine::*;

use Reg::*;

//-------------------------------

// We only support a single bm atm.
static mut BLOCK_MANAGER: Option<(Addr, Arc<BlockManager>)> = None;

pub fn get_bm() -> Result<Arc<BlockManager>> {
    unsafe {
        match &BLOCK_MANAGER {
            None => Err(anyhow!("no block manager created")),
            Some((_, bm)) => Ok(bm.clone()),
        }
    }
}

pub fn set_bm(gptr: Addr, bm: Arc<BlockManager>) -> Result<()> {
    unsafe {
        BLOCK_MANAGER = Some((gptr, bm));
        Ok(())
    }
}

pub fn clear_bm() {
    unsafe {
        BLOCK_MANAGER = None;
    }
}

pub fn bm_create(fix: &mut Fixture) -> Result<()> {
    let bdev_ptr = Addr(fix.vm.reg(A0));
    let bdev = read_guest::<BlockDevice>(&fix.vm.mem, bdev_ptr)?;

    debug!("inode address: {:?}", bdev.inode);
    let inode = read_guest::<INode>(&fix.vm.mem, bdev.inode)?;
    let block_size = fix.vm.reg(A1);
    let _max_held_per_thread = fix.vm.reg(A2);

    let nr_blocks = inode.nr_sectors / (block_size / 512);

    let bm = Arc::new(BlockManager::new(nr_blocks));
    let guest_addr = fix.vm.mem.alloc(4)?;
    set_bm(guest_addr, bm)?;

    fix.vm.ret(guest_addr.0);
    Ok(())
}

pub fn bm_destroy(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm()?;

    if bm.get_nr_held_blocks() > 0 {
        return Err(anyhow!(
            "dm_block_manager_destroy() called with blocks still held"
        ));
    }

    clear_bm();
    fix.vm.mem.free(bm_ptr)?;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_block_size(fix: &mut Fixture) -> Result<()> {
    fix.vm.ret(4096);
    Ok(())
}

pub fn bm_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm()?;
    let nr_blocks = bm.get_nr_blocks();
    fix.vm.ret(nr_blocks);
    Ok(())
}

pub fn bm_read_lock(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let loc = fix.vm.reg(A1);
    let v_ptr = Addr(fix.vm.reg(A2));
    let result_ptr = fix.vm.reg(A3);
    let bm = get_bm()?;
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
    let _bm_ptr = fix.vm.reg(A0);
    let loc = fix.vm.reg(A1);
    let v_ptr = Addr(fix.vm.reg(A2));
    let result_ptr = fix.vm.reg(A3);
    let bm = get_bm()?;
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
    let bm = get_bm()?;
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
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm()?;
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

pub fn bm_is_read_only(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm()?;
    let result = if bm.is_read_only() { 1 } else { 0 };
    fix.vm.ret(result);
    Ok(())
}

pub fn bm_set_read_only(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm()?;
    bm.set_read_only(true);
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_set_read_write(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm()?;
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
    Ok(())
}

//-------------------------------
