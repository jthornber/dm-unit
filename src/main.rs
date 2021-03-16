extern crate dm_unit;
extern crate log;

use dm_unit::test_runner::*;
use dm_unit::tests::block_manager;
use dm_unit::tests::btree;
use dm_unit::tests::space_map;
use dm_unit::tests::space_map_disk;
use dm_unit::tests::thinp;

use anyhow::Result;
use clap::{App, Arg};
use regex::Regex;
use std::path::Path;

//-------------------------------

fn register_tests(runner: &mut TestRunner) -> Result<()> {
    block_manager::register_tests(runner)?;
    btree::register_tests(runner)?;
    space_map_disk::register_tests(runner)?;
    space_map::register_tests(runner)?;
    thinp::register_tests(runner)?;

    Ok(())
}

fn main() -> Result<()> {
    env_logger::init();

    let parser = App::new("dm-unit")
        .version("0")
        .about("Unit test framework for device mapper kernel modules")
        .arg(
            Arg::with_name("KERNEL_DIR")
                .short("k")
                .long("kernel-dir")
                .help("Location of kernel source that contains built kernel modules to be tested.")
                .required(true)
                .value_name("KERNEL_DIR"),
        )
        .arg(
            Arg::with_name("GDB")
                .long("gdb")
                .help("Listen on a socket for a gdb connection"),
        )
        .arg(
            Arg::with_name("FILTER")
                .short("t")
                .help("regex filter to select which tests to run")
                .value_name("FILTER"),
        );

    let matches = parser.get_matches();
    let kernel_dir = Path::new(matches.value_of("KERNEL_DIR").unwrap());

    let mut runner = TestRunner::new(kernel_dir);
    if let Some(pattern) = matches.value_of("FILTER") {
        let rx = Regex::new(pattern)?;
        runner.set_filter(rx);
    }

    if matches.is_present("GDB") {
        runner.enable_gdb();
    }

    register_tests(&mut runner)?;

    let (pass, fail) = runner.exec()?;

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
