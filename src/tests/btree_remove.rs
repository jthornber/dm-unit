use crate::decode::Reg;
use crate::test_runner::*;
use crate::tests::fixture::*;

use anyhow::Result;
use log::info;

//-------------------------------

// pretend tests
fn test1(fix: &mut Fixture) -> Result<()> {
    fix.stub("crc32c", 123)?;
    fix.call("test1")?;
    assert!(fix.vm.reg(Reg::A0) == 123);
    Ok(())
}


fn test2(fix: &mut Fixture) -> Result<()> {
    fix.at_func("__kmalloc", Box::new(kmalloc))?;
    fix.at_func("memset", Box::new(memset))?;
    fix.at_func("kfree", Box::new(kfree))?;
    fix.call("test2")?;
    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    info!("registered /pdata/btree/remove tests");

    runner.register_test("/pdata/btree/remove/test1", Box::new(test1));
    runner.register_test("/pdata/btree/remove/test2", Box::new(test2));

    Ok(())
}

//-------------------------------
