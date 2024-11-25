use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::stubs::block_device::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;

use anyhow::{ensure, Result};
use libc::ENOMEM;

use Reg::*;

//-------------------------------

const MAX_ERRNO: i64 = 4095;

fn is_err(ptr: u64) -> bool {
    ptr >= (-MAX_ERRNO as i64) as u64
}

fn ptr_err(ptr: u64) -> i64 {
    ptr as i64
}

fn kmalloc_nomem(fix: &mut Fixture) -> Result<()> {
    eprintln!("kmalloc_nomem called");
    fix.vm.ret(0);
    Ok(())
}

//-------------------------------

fn test_create_nomem(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let block_size = 8;
    let nr_blocks = 1024;
    let nr_sectors = nr_blocks * block_size;
    let bdev_ptr = mk_block_device(&mut fix.vm.mem, 0, nr_sectors)?;

    fix.vm.set_reg(A0, bdev_ptr.0);
    fix.vm.set_reg(A1, block_size * 512); // block size
    fix.vm.set_reg(A2, 16); // max held per thread

    fix.at_func("__kmalloc_noprof", Box::new(kmalloc_nomem))?;
    fix.call("dm_block_manager_create")?;

    let ret = fix.vm.reg(A0);
    if is_err(ret) {
        let err = ptr_err(ret);
        eprintln!("err = {}, ENOMEM = {}", err, -ENOMEM);
        ensure!(err == -ENOMEM as i64, "should fail with -ENOMEM");
    } else {
        ensure!(false, "Expected an error, but got success");
    }

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
    dm_bm_destroy(fix, bm)?;
    assert!(bs == 4096);
    Ok(())
}

fn test_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1234u64;

    standard_globals(fix)?;
    let bm = dm_bm_create(fix, nr_blocks)?;
    let reported_nr_blocks = dm_bm_nr_blocks(fix, bm)?;
    assert!(nr_blocks == reported_nr_blocks);
    dm_bm_destroy(fix, bm)?;
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
    ensure!(
        fix.vm.mem.write(data1, &buf, PERM_WRITE).is_err(),
        "shouldn't be able to write to data"
    );
    fix.vm.mem.read(data1, &mut buf, PERM_READ)?;

    // We should be able to lock again.
    let b2 = dm_bm_read_lock(fix, bm, 0, validator)?;
    let data2 = dm_block_data(fix, b2)?;
    ensure!(data1 == data2, "data changed");

    // confirm we can read from the data
    fix.vm.mem.read(data2, &mut buf, PERM_READ)?;

    // confirm we can't write to the data
    ensure!(
        fix.vm.mem.write(data2, &buf, PERM_WRITE).is_err(),
        "shouldn't be able to write to data"
    );

    dm_bm_unlock(fix, b1)?;
    dm_bm_unlock(fix, b2)?;
    dm_bm_destroy(fix, bm)?;

    // confirm we can't read from the data
    ensure!(
        fix.vm.mem.read(data1, &mut buf, PERM_READ).is_err(),
        "shouldn't be able to read from data"
    );

    Ok(())
}

fn test_write_lock(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bm = dm_bm_create(fix, 16)?;
    let validator = Addr(0); // Just passing NULL for now

    let b = dm_bm_write_lock_zero(fix, bm, 0, validator)?;
    let data = dm_block_data(fix, b)?;
    let mut buf = vec![0u8; 4096];

    // We should be able to read ...
    fix.vm.mem.read(data, &mut buf, PERM_READ)?;

    // ... and write
    fix.vm.mem.write(data, &buf, PERM_WRITE)?;

    // We shouldn't be able to lock twice
    ensure!(
        dm_bm_write_lock(fix, bm, 0, validator).is_err(),
        "shouldn't be able to write lock twice"
    );

    dm_bm_unlock(fix, b)?;
    ensure!(
        dm_bm_unlock(fix, b).is_err(),
        "shouldn't be able to write unlock twice"
    );

    // Now we shouldn't be able to read or write
    ensure!(
        fix.vm.mem.read(data, &mut buf, PERM_READ).is_err(),
        "shouldn't be able to read"
    );
    ensure!(
        fix.vm.mem.write(data, &buf, PERM_WRITE).is_err(),
        "shouldn't be able to write"
    );

    dm_bm_destroy(fix, bm)?;

    Ok(())
}

//-------------------------------

pub fn register_tests(tests: &mut TestSet) -> Result<()> {
    let kmodules = vec![PDATA_MOD];

    tests.register(
        "/pdata/block-manager/create/nomem",
        Test::new(kmodules.clone(), Box::new(test_create_nomem)),
    );
    tests.register(
        "/pdata/block-manager/create/success",
        Test::new(kmodules.clone(), Box::new(test_create_success)),
    );
    tests.register(
        "/pdata/block-manager/block-size",
        Test::new(kmodules.clone(), Box::new(test_block_size)),
    );
    tests.register(
        "/pdata/block-manager/nr-blocks",
        Test::new(kmodules.clone(), Box::new(test_nr_blocks)),
    );
    tests.register(
        "/pdata/block-manager/read-lock",
        Test::new(kmodules.clone(), Box::new(test_read_lock)),
    );
    tests.register(
        "/pdata/block-manager/write-lock",
        Test::new(kmodules, Box::new(test_write_lock)),
    );

    Ok(())
}

//-------------------------------
