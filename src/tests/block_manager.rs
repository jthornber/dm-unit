use crate::decode::*;
use crate::test_runner::*;
use crate::tests::fixture::*;
use crate::memory::*;

use anyhow::Result;
use libc::ENOMEM;
use log::{debug, info};

use Reg::*;

//-------------------------------

fn kmalloc_nomem(fix: &mut Fixture) -> Result<()> {
    fix.vm.ret(0);
    Ok(())
}

fn dm_block_manager_create(fix: &mut Fixture) -> Result<Addr> {
    // We'll just allocate a word to act as the bdev, we don't examine the contents. 
    let bdev = fix.alloc(4)?;
    fix.vm.set_reg(A0, bdev.0);
    fix.vm.set_reg(A1, 4096); // block size
    fix.vm.set_reg(A2, 16); // max held per thread
    fix.call("dm_block_manager_create")?;
    Ok(Addr(fix.vm.reg(A0)))
}

fn dm_block_manager_destroy(fix: &mut Fixture, bm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, bm.0);
    fix.call("dm_block_manager_destroy")?;
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
    fix.standard_globals()?;
    let bm = dm_block_manager_create(fix)?;
    dm_block_manager_destroy(fix, bm)?;
    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    runner.register("/pdata/block-manager/create/nomem", Box::new(test_create_nomem));
    runner.register("/pdata/block-manager/create/success", Box::new(test_create_success));
    info!("registered /pdata/block-manager tests");
    Ok(())
}

//-------------------------------
