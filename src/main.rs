extern crate dm_unit;
extern crate log;

use dm_unit::test_runner::*;
use dm_unit::tests::block_manager;
use dm_unit::tests::btree;
use dm_unit::tests::bufio;
use dm_unit::tests::cache;
use dm_unit::tests::space_map_disk;
use dm_unit::tests::space_map_metadata;
use dm_unit::tests::thinp;

use anyhow::Result;
use clap::{App, Arg};
use regex::Regex;
use std::path::Path;

//-------------------------------

fn register_tests(runner: &mut TestRunner) -> Result<()> {
    bufio::register_tests(runner)?;
    block_manager::register_tests(runner)?;
    btree::register_tests(runner)?;
    cache::register_tests(runner)?;
    space_map_disk::register_tests(runner)?;
    space_map_metadata::register_tests(runner)?;
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
            Arg::with_name("JOBS")
                .short("j")
                .help("Number of tests to run concurrently.")
                .required(false)
                .value_name("JOBS"),
        )
        .arg(
            Arg::with_name("FILTER")
                .short("t")
                .help("regex filter to select which tests to run")
                .value_name("FILTER"),
        )
        .arg(
            Arg::with_name("JIT")
                .long("jit")
                .help("Turn on the experimental jit compiler"),
        );

    let matches = parser.get_matches();
    let kernel_dir = Path::new(matches.value_of("KERNEL_DIR").unwrap());

    let mut runner = TestRunner::new(kernel_dir)?;

    if let Some(pattern) = matches.value_of("FILTER") {
        let rx = Regex::new(pattern)?;
        runner.set_filter(rx);
    }

    if let Some(job_str) = matches.value_of("JOBS") {
        let jobs = job_str
            .to_string()
            .parse::<usize>()
            .expect("couldn't parse jobs");
        runner.set_jobs(jobs);
    }

    if matches.is_present("JIT") {
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
