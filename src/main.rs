extern crate dm_unit;
extern crate log;

use dm_unit::test_runner::*;
use dm_unit::tests::block_manager;
use dm_unit::tests::btree;
use dm_unit::tests::bufio;
use dm_unit::tests::cache;
use dm_unit::tests::extent_allocator;
use dm_unit::tests::space_map_disk;
use dm_unit::tests::space_map_metadata;
use dm_unit::tests::thinp;

use anyhow::Result;
use clap::{arg, value_parser, Arg, ArgAction, Command};
use regex::Regex;
use std::path::Path;

//-------------------------------

fn register_tests(runner: &mut TestRunner) -> Result<()> {
    bufio::register_tests(runner)?;
    block_manager::register_tests(runner)?;
    btree::register_tests(runner)?;
    cache::register_tests(runner)?;
    extent_allocator::register_tests(runner)?;
    space_map_disk::register_tests(runner)?;
    space_map_metadata::register_tests(runner)?;
    thinp::register_tests(runner)?;

    Ok(())
}

fn main() -> Result<()> {
    env_logger::init();

    let parser = Command::new("dm-unit")
        .version("0")
        .about("Unit test framework for device mapper kernel modules")
        .arg(
            arg!(-k --"kernel-dir" <KERNEL_DIR>)
                .help("Location of kernel source that contains built kernel modules to be tested.")
                .required(true),
        )
        .arg(
            arg!(-j <JOBS>)
                .value_parser(value_parser!(usize))
                .help("Number of tests to run concurrently.")
                .required(false),
        )
        .arg(arg!(-t <FILTER>).help("regex filter to select which tests to run"))
        .arg(
            Arg::new("JIT")
                .long("jit")
                .action(ArgAction::SetTrue)
                .help("Turn on the experimental jit compiler"),
        );

    let matches = parser.get_matches();
    let kernel_dir = Path::new(matches.get_one::<String>("kernel-dir").unwrap());

    let mut runner = TestRunner::new(kernel_dir)?;

    let empty_pattern = "".to_string();
    let pattern = matches
        .get_one::<String>("FILTER")
        .unwrap_or(&empty_pattern);
    let rx = Regex::new(pattern)?;
    runner.set_filter(rx);
    let rx = Regex::new(pattern)?;
    runner.set_filter(rx);

    if let Some(jobs) = matches.get_one::<usize>("JOBS") {
        runner.set_jobs(*jobs);
    }

    // See if the jit flag is present
    if *matches.get_one::<bool>("JIT").unwrap_or(&false) {
        runner.set_jit();
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
