use crate::decode::Reg;
use crate::test_runner::*;
use crate::tests::fixture::*;

use anyhow::Result;
use log::info;
use std::path::PathBuf;

//-------------------------------

// pretend tests
struct Test1 {}

impl Test for Test1 {
    fn exec(&self, kernel_dir: &PathBuf) -> Result<()> {
        let mut fix = Fixture::new(kernel_dir)?;
        fix.stub("crc32c", 123)?;
        fix.call("test1")?;
        assert!(fix.vm.reg(Reg::A0) == 123);
        Ok(())
    }
}

struct Test2 {}

impl Test for Test2 {
    fn exec(&self, kernel_dir: &PathBuf) -> Result<()> {
        let mut fix = Fixture::new(kernel_dir)?;
        fix.at_func("__kmalloc", Box::new(kmalloc))?;
        fix.at_func("memset", Box::new(memset))?;
        fix.at_func("kfree", Box::new(kfree))?;
        fix.call("test2")?;
        Ok(())
    }
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    info!("registered /pdata/btree/remove tests");

    runner.register_test("/pdata/btree/remove/test1", Box::new(Test1 {}));
    runner.register_test("/pdata/btree/remove/test2", Box::new(Test2 {}));

    Ok(())
}

//-------------------------------
