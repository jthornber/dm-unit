use crate::decode::*;
use crate::memory::*;
use crate::test_runner::*;
use crate::tests::fixture::*;

use anyhow::{anyhow, ensure, Result};
use libc::ENOMEM;
use log::{info};

use Reg::*;

//-------------------------------

fn kmalloc_nomem(fix: &mut Fixture) -> Result<()> {
    fix.vm.ret(0);
    Ok(())
}

pub fn dm_bm_create(fix: &mut Fixture, nr_blocks: u64) -> Result<Addr> {
    // We'll just allocate a word to act as the bdev, we don't examine the contents.
    let bdev = fix.vm.mem.alloc(8)?;

    // We write the nr blocks into the guest memory
    fix.vm
        .mem
        .write(bdev, &nr_blocks.to_le_bytes(), PERM_WRITE)?;

    fix.vm.set_reg(A0, bdev.0);
    fix.vm.set_reg(A1, 4096); // block size
    fix.vm.set_reg(A2, 16); // max held per thread
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

fn test_create_nomem(fix: &mut Fixture) -> Result<()> {
    fix.at_func("__kmalloc", Box::new(kmalloc_nomem))?;
    fix.call("dm_block_manager_create")?;
    assert!(fix.vm.reg(A0) as i32 == -ENOMEM);
    Ok(())
}

fn test_create_success(fix: &mut Fixture) -> Result<()> {
    fix.standard_globals()?;
    let bm = dm_bm_create(fix, 128)?;
    dm_bm_destroy(fix, bm)?;
    Ok(())
}

fn test_block_size(fix: &mut Fixture) -> Result<()> {
    fix.standard_globals()?;
    let bm = dm_bm_create(fix, 1024)?;
    let bs = dm_bm_block_size(fix, bm)?;
    assert!(bs == 4096);
    Ok(())
}

fn test_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1234u64;

    fix.standard_globals()?;
    let bm = dm_bm_create(fix, nr_blocks)?;
    let nr_blocks = dm_bm_nr_blocks(fix, bm)?;
    assert!(nr_blocks == dm_bm_nr_blocks(fix, bm)?);
    Ok(())
}

fn test_read_lock(fix: &mut Fixture) -> Result<()> {
    fix.standard_globals()?;
    let bm = dm_bm_create(fix, 16)?;
    let validator = Addr(0); // Just passing NULL for now
    let b1 = dm_bm_read_lock(fix, bm, 0, validator)?;
    let data1 = dm_block_data(fix, b1)?;

    // confirm we can read from the data
    let mut buf = vec![0u8; 4096];
    fix.vm.mem.read(data1, &mut buf, PERM_READ)?;

    // confirm we can't write to the data
    ensure!(fix.vm.mem.write(data1, &mut buf, PERM_WRITE).is_err());
    fix.vm.mem.read(data1, &mut buf, PERM_READ)?;

    // We should be able to lock again.
    let b2 = dm_bm_read_lock(fix, bm, 0, validator)?;
    let data2 = dm_block_data(fix, b2)?;
    ensure!(data1 == data2);

    // confirm we can read from the data
    fix.vm.mem.read(data2, &mut buf, PERM_READ)?;

    // confirm we can't write to the data
    ensure!(fix.vm.mem.write(data2, &mut buf, PERM_WRITE).is_err());

    dm_bm_unlock(fix, b1)?;
    dm_bm_unlock(fix, b2)?;

    // confirm we can't read from the data
    ensure!(fix.vm.mem.read(data1, &mut buf, PERM_READ).is_err());

    Ok(())
}

fn test_write_lock(fix: &mut Fixture) -> Result<()> {
    fix.standard_globals()?;
    let bm = dm_bm_create(fix, 16)?;
    let validator = Addr(0); // Just passing NULL for now
    let b = dm_bm_write_lock(fix, bm, 0, validator)?;
    let data = dm_block_data(fix, b)?;
    let mut buf = vec![0u8; 4096];

    // We should be able to read ...
    fix.vm.mem.read(data, &mut buf, PERM_READ)?;

    // ... and write
    fix.vm.mem.write(data, &buf, PERM_WRITE)?;

    // We shouldn't be able to lock twice
    ensure!(dm_bm_write_lock(fix, bm, 0, validator).is_err());

    dm_bm_unlock(fix, b)?;

    // Now we shouldn't be able to read or write
    ensure!(fix.vm.mem.read(data, &mut buf, PERM_READ).is_err());
    ensure!(fix.vm.mem.write(data, &buf, PERM_WRITE).is_err());

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    runner.register(
        "/pdata/block-manager/create/nomem",
        Box::new(test_create_nomem),
    );
    runner.register(
        "/pdata/block-manager/create/success",
        Box::new(test_create_success),
    );
    runner.register("/pdata/block-manager/block-size", Box::new(test_block_size));
    runner.register("/pdata/block-manager/nr-blocks", Box::new(test_nr_blocks));
    runner.register("/pdata/block-manager/read-lock", Box::new(test_read_lock));
    runner.register("/pdata/block-manager/write-lock", Box::new(test_write_lock));

    info!("registered /pdata/block-manager tests");
    Ok(())
}

//-------------------------------
