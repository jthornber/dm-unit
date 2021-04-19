use crate::emulator::decode::*;
use crate::fixture::*;
use crate::emulator::memory::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;

use anyhow::{ensure, Result};
use libc::ENOMEM;

use Reg::*;

//-------------------------------

fn kmalloc_nomem(fix: &mut Fixture) -> Result<()> {
    fix.vm.ret(0);
    Ok(())
}

//-------------------------------

fn test_create_nomem(fix: &mut Fixture) -> Result<()> {
    fix.at_func("__kmalloc", Box::new(kmalloc_nomem))?;
    fix.call("dm_block_manager_create")?;
    assert!(fix.vm.reg(A0) as i32 == -ENOMEM);
    Ok(())
}

fn test_create_success(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bm = dm_bm_create(fix, 128)?;
    dm_bm_destroy(fix, bm)?;
    Ok(())
}

fn test_block_size(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bm = dm_bm_create(fix, 1024)?;
    let bs = dm_bm_block_size(fix, bm)?;
    assert!(bs == 4096);
    Ok(())
}

fn test_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1234u64;

    standard_globals(fix)?;
    let bm = dm_bm_create(fix, nr_blocks)?;
    let nr_blocks = dm_bm_nr_blocks(fix, bm)?;
    assert!(nr_blocks == dm_bm_nr_blocks(fix, bm)?);
    Ok(())
}

fn test_read_lock(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bm = dm_bm_create(fix, 16)?;
    let validator = Addr(0); // Just passing NULL for now
    let b1 = dm_bm_read_lock(fix, bm, 0, validator)?;
    let data1 = dm_block_data(fix, b1)?;

    // confirm we can read from the data
    let mut buf = vec![0u8; 4096];
    fix.vm.mem.read(data1, &mut buf, PERM_READ)?;

    // confirm we can't write to the data
    ensure!(fix.vm.mem.write(data1, &buf, PERM_WRITE).is_err());
    fix.vm.mem.read(data1, &mut buf, PERM_READ)?;

    // We should be able to lock again.
    let b2 = dm_bm_read_lock(fix, bm, 0, validator)?;
    let data2 = dm_block_data(fix, b2)?;
    ensure!(data1 == data2);

    // confirm we can read from the data
    fix.vm.mem.read(data2, &mut buf, PERM_READ)?;

    // confirm we can't write to the data
    ensure!(fix.vm.mem.write(data2, &buf, PERM_WRITE).is_err());

    dm_bm_unlock(fix, b1)?;
    dm_bm_unlock(fix, b2)?;

    // confirm we can't read from the data
    ensure!(fix.vm.mem.read(data1, &mut buf, PERM_READ).is_err());

    Ok(())
}

fn test_write_lock(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
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
    let mut reg = move |path, func| {
        let mut p = "/pdata/block-manager/".to_string();
        p.push_str(path);
        runner.register(&p, func);
    };

    reg("create/nomem", Box::new(test_create_nomem));
    reg("create/success", Box::new(test_create_success));
    reg("block-size", Box::new(test_block_size));
    reg("nr-blocks", Box::new(test_nr_blocks));
    reg("read-lock", Box::new(test_read_lock));
    reg("write-lock", Box::new(test_write_lock));

    Ok(())
}

//-------------------------------
