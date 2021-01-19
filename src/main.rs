extern crate dm_unit;
extern crate log;

use dm_unit::breakpoint::Stub;
use dm_unit::decode::Reg;
use dm_unit::loader::*;
use dm_unit::memory::{Addr, Heap, PERM_EXEC};
use dm_unit::test_runner::*;
use dm_unit::tests::btree_remove;
use dm_unit::vm::*;

use anyhow::{anyhow, Result};
use clap::{App, Arg};
use log::{debug, info};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//-------------------------------

fn main() -> Result<()> {
    env_logger::init();

    let parser = App::new("dm-unit")
        .version("0")
        .about("Unit test framework for device mapper kernel modules")
        .arg(
            Arg::with_name("KERNEL_SOURCE_DIR")
                .help("Location of kernel source that contains built kernel modules to be tested.")
                .required(true)
                .index(1),
        );

    let matches = parser.get_matches();
    let module = Path::new(matches.value_of("KERNEL_SOURCE_DIR").unwrap());
    let mut runner = TestRunner::new(module);

    btree_remove::register_tests(&mut runner)?;
    let (pass, fail) = runner.exec();

    if fail == 0 {
        println!("All tests passed: {}", pass);
    } else {
        println!(
            "There were failures.\nTotal tests: {}, Pass: {}, Fail: {}",
            pass + fail,
            pass,
            fail
        );
    }

    Ok(())
}

//-------------------------------
