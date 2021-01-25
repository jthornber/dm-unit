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

    runner.register("/pdata/btree/remove/test1", Box::new(test1));
    runner.register("/pdata/btree/remove/test2", Box::new(test2));

    // registering lots of fake tests to test formatting of paths
    runner.register("/pdata/btree/remove/test3", Box::new(test2));
    runner.register("/pdata/btree/remove/test4", Box::new(test2));
    runner.register("/pdata/block-manager/create", Box::new(test2));
    runner.register("/pdata/block-manager/get", Box::new(test2));
    runner.register("/pdata/block-manager/dirty", Box::new(test2));
    runner.register("/pdata/space-map/metadata/thing1", Box::new(test2));
    runner.register("/pdata/space-map/metadata/thing2", Box::new(test2));
    runner.register("/pdata/space-map/data/thing1", Box::new(test2));
    runner.register("/pdata/space-map/data/thin2", Box::new(test2));
    runner.register("/pdata/space-map/data/thing3", Box::new(test2));

    Ok(())
}

//-------------------------------
