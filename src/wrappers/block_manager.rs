use crate::decode::*;
use crate::memory::*;
use crate::fixture::*;
use crate::stubs::block_device::*;

use anyhow::{anyhow, Result};

use Reg::*;

//-------------------------------

pub fn dm_bm_create(fix: &mut Fixture, nr_blocks: u64) -> Result<Addr> {
    let block_size = 8;
    let nr_sectors = nr_blocks * block_size;
    let bdev_ptr = mk_block_device(&mut fix.vm.mem, 0, nr_sectors)?;

    fix.vm.set_reg(A0, bdev_ptr.0);
    fix.vm.set_reg(A1, block_size * 512); 	// block size
    fix.vm.set_reg(A2, 16); 			// max held per thread
    fix.call("dm_block_manager_create")?;
    Ok(Addr(fix.vm.reg(A0)))
}

pub fn dm_bm_destroy(fix: &mut Fixture, bm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, bm.0);
    fix.call("dm_block_manager_destroy")?;
    Ok(())
}

pub fn dm_bm_block_size(fix: &mut Fixture, bm: Addr) -> Result<u64> {
    fix.vm.set_reg(A0, bm.0);
    fix.call("dm_bm_block_size")?;
    Ok(fix.vm.reg(A0))
}

pub fn dm_bm_nr_blocks(fix: &mut Fixture, bm: Addr) -> Result<u64> {
    fix.vm.set_reg(A0, bm.0);
    fix.call("dm_bm_nr_blocks")?;
    Ok(fix.vm.reg(A0))
}

fn lock_(fix: &mut Fixture, lock_fn: &str, bm: Addr, b: u64, validator: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, bm.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, validator.0);

    let result = fix.vm.mem.alloc(8)?;
    fix.vm.set_reg(A3, result.0);

    fix.call(lock_fn)?;

    let r = fix.vm.reg(A0);
    if r != 0 {
        return Err(anyhow!("{} failed: {}", lock_fn, r));
    }
    let block = fix.vm.mem.read_into::<u64>(result, PERM_READ)?;
    fix.vm.mem.free(result)?;
    Ok(Addr(block))
}

pub fn dm_bm_read_lock(fix: &mut Fixture, bm: Addr, b: u64, validator: Addr) -> Result<Addr> {
    lock_(fix, "dm_bm_read_lock", bm, b, validator)
}

pub fn dm_bm_write_lock(fix: &mut Fixture, bm: Addr, b: u64, validator: Addr) -> Result<Addr> {
    lock_(fix, "dm_bm_write_lock", bm, b, validator)
}

pub fn dm_bm_write_lock_zero(fix: &mut Fixture, bm: Addr, b: u64, validator: Addr) -> Result<Addr> {
    lock_(fix, "dm_bm_write_lock_zero", bm, b, validator)
}

pub fn dm_bm_unlock(fix: &mut Fixture, block: Addr) -> Result<()> {
    fix.vm.set_reg(A0, block.0);
    fix.call("dm_bm_unlock")?;
    Ok(())
}

pub fn dm_block_location(fix: &mut Fixture, block: Addr) -> Result<u64> {
    fix.vm.set_reg(A0, block.0);
    fix.call("dm_block_location")?;
    Ok(fix.vm.reg(A0))
}

pub fn dm_block_data(fix: &mut Fixture, block: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, block.0);
    fix.call("dm_block_data")?;
    Ok(Addr(fix.vm.reg(A0)))
}

//-------------------------------
