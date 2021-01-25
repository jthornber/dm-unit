extern crate dm_unit;
extern crate log;

use dm_unit::test_runner::*;
use dm_unit::tests::btree_remove;

use anyhow::Result;
use clap::{App, Arg};
use regex::Regex;
use std::path::Path;

//-------------------------------

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

    btree_remove::register_tests(&mut runner)?;
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
