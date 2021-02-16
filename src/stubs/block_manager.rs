use crate::block_manager::*;
use crate::decode::Reg;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::{Addr, PERM_READ, PERM_WRITE};

use anyhow::{anyhow, Result};
use crc32c::crc32c;
use log::{info, warn};
use thinp::io_engine::IoEngine;

use Reg::*;

//-------------------------------

// We only support a single bm atm.
static mut BLOCK_MANAGER: Option<(Addr, BlockManager)> = None;

fn get_bm<'a>() -> Result<&'a BlockManager> {
    unsafe {
        if BLOCK_MANAGER.is_none() {
            Err(anyhow!("no block manager created"))
        } else {
            Ok(&BLOCK_MANAGER.as_ref().unwrap().1)
        }
    }
}

fn get_bm_mut<'a>() -> Result<&'a mut BlockManager> {
    unsafe {
        if BLOCK_MANAGER.is_none() {
            return Err(anyhow!("no block manager created"));
        }

        /*
        if block_manager.unwrap().0 != gptr {
            return Err(anyhow!("bm has mismatched guest ptr"));
        }
        */

        Ok(&mut BLOCK_MANAGER.as_mut().unwrap().1)
    }
}

fn set_bm(gptr: Addr, bm: BlockManager) -> Result<()> {
    unsafe {
        /*
        if BLOCK_MANAGER.is_some() {
            Err(anyhow!("dm-unit only supports a single block manager"))
        } else {
            */
            BLOCK_MANAGER = Some((gptr, bm));
            Ok(())
        //}
    }
}

fn clear_bm() {
    unsafe {
        BLOCK_MANAGER = None;
    }
}

pub fn bm_create(fix: &mut Fixture) -> Result<()> {
    let bdev_ptr = fix.vm.reg(A0);
    let _block_size = fix.vm.reg(A1);
    let _max_held_per_thread = fix.vm.reg(A2);

    let nr_blocks = fix.vm.mem.read_into::<u64>(Addr(bdev_ptr), PERM_READ)?;

    let engine = CoreEngine::new(nr_blocks);
    let bm = BlockManager::new(engine);
    let guest_addr = fix.vm.mem.alloc(4)?;
    set_bm(guest_addr, bm)?;

    fix.vm.ret(guest_addr.0);
    Ok(())
}

pub fn bm_destroy(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm_mut()?;

    info!(
        "bm: nr_blocks = {}, nr_read_locks = {}, nr_write_locks = {}",
        bm.engine.residency(),
        bm.nr_read_locks,
        bm.nr_write_locks,
    );

    let mut held = false;
    for key in bm.locks.keys() {
        warn!("Block {} still held", key);
        held = true;
    }

    if held {
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
    let nr_blocks = bm.engine.get_nr_blocks();
    fix.vm.ret(nr_blocks);
    Ok(())
}

pub fn bm_read_lock(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let loc = fix.vm.reg(A1);
    let v_ptr = Addr(fix.vm.reg(A2));
    let result_ptr = fix.vm.reg(A3);
    let bm = get_bm_mut()?;
    let guest_ptr = bm.read_lock(&mut fix.vm.mem, loc, v_ptr)?;

    // fill out result ptr
    fix.vm
        .mem
        .write(Addr(result_ptr), &guest_ptr.0.to_le_bytes(), PERM_WRITE)?;

    // return success
    fix.vm.ret(0);
    Ok(())
}

fn write_lock_(fix: &mut Fixture, zero: bool) -> Result<()> {
    let _bm_ptr = fix.vm.reg(A0);
    let loc = fix.vm.reg(A1);
    let v_ptr = Addr(fix.vm.reg(A2));
    let result_ptr = fix.vm.reg(A3);
    let bm = get_bm_mut()?;
    let guest_addr = if zero {
        bm.write_lock_zero(&mut fix.vm.mem, loc, v_ptr)?
    } else {
        bm.write_lock(&mut fix.vm.mem, loc, v_ptr)?
    };

    // fill out result ptr
    fix.vm
        .mem
        .write(Addr(result_ptr), &guest_addr.0.to_le_bytes(), PERM_WRITE)?;

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

    let bm = get_bm_mut()?;
    if bm.unlock(&mut fix.vm.mem, gb_ptr)? {
        // unregister gb_ptr
    }

    fix.vm.ret(0);
    Ok(())
}

pub fn bm_block_location(fix: &mut Fixture) -> Result<()> {
    let gb_ptr = fix.vm.reg(A0);
    // FIXME: this needlessly copies the data across, just read the header.
    let gb = read_guest::<GBlock>(&mut fix.vm.mem, Addr(gb_ptr))?;
    fix.vm.ret(gb.loc);
    Ok(())
}

pub fn bm_block_data(fix: &mut Fixture) -> Result<()> {
    let gb_ptr = fix.vm.reg(A0);
    fix.vm.ret(gb_ptr + 8);
    Ok(())
}

pub fn bm_flush(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm_mut()?;
    bm.flush();

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
    let bm = get_bm_mut()?;
    let result = if bm.is_read_only() { 1 } else { 0 };
    fix.vm.ret(result);
    Ok(())
}

pub fn bm_set_read_only(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm_mut()?;
    bm.set_read_only(true);
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_set_read_write(fix: &mut Fixture) -> Result<()> {
    let _bm_ptr = Addr(fix.vm.reg(A0));
    let bm = get_bm_mut()?;
    bm.set_read_only(false);
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_checksum(fix: &mut Fixture) -> Result<()> {
    let data = Addr(fix.vm.reg(A0));
    let len = fix.vm.reg(A1);
    let init_xor = fix.vm.reg(A2) as u32;

    let mut buf = vec![0u8; len as usize];
    fix.vm.mem.read(data, &mut buf, PERM_READ)?;
    let mut csum = crc32c(&buf) ^ 0xffffffff;
    csum ^= init_xor;

    fix.vm.ret(csum as u64);
    Ok(())
}

//-------------------------------
