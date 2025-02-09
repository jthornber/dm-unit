extern crate dm_unit;

use dm_unit::bench;
use dm_unit::capture_log::*;
use dm_unit::path_formatter::*;
use dm_unit::test_runner::*;
use dm_unit::tests::array;
use dm_unit::tests::array_cursor;
use dm_unit::tests::block_manager;
use dm_unit::tests::btree;
use dm_unit::tests::btree_cursor;
use dm_unit::tests::bufio;
use dm_unit::tests::cache;
use dm_unit::tests::extent_allocator;
use dm_unit::tests::space_map_disk;
use dm_unit::tests::space_map_metadata;
use dm_unit::tests::thinp;

use anyhow::Result;
use clap::{arg, Arg, ArgAction, ArgMatches, Command};
use log::Level;
use regex::Regex;
use std::path::Path;
use std::sync::{Arc, Mutex};

//-------------------------------

fn all_tests() -> Result<TestSet> {
    let mut tests = TestSet::default();

    array::register_tests(&mut tests)?;
    array_cursor::register_tests(&mut tests)?;
    bufio::register_tests(&mut tests)?;
    block_manager::register_tests(&mut tests)?;
    btree::register_tests(&mut tests)?;
    btree_cursor::register_tests(&mut tests)?;
    cache::register_tests(&mut tests)?;
    extent_allocator::register_tests(&mut tests)?;
    space_map_disk::register_tests(&mut tests)?;
    space_map_metadata::register_tests(&mut tests)?;
    thinp::register_tests(&mut tests)?;

    Ok(tests)
}

fn benchmark_tests() -> Result<TestSet> {
    let mut tests = TestSet::default();

    bench::btree::register_bench(&mut tests)?;

    Ok(tests)
}

const DB_PATH: &str = "test_results.db";

/// Read the result set from the environment var DM_UNIT_RESULT_SET
fn get_result_set() -> Result<String> {
    match std::env::var("DM_UNIT_RESULT_SET") {
        Ok(s) => {
            if s.is_empty() {
                Err(anyhow::anyhow!("DM_UNIT_RESULT_SET is empty"))
            } else {
                Ok(s)
            }
        }
        Err(e) => Err(anyhow::anyhow!("DM_UNIT_RESULT_SET not set: {}", e)),
    }
}

fn get_rx(matches: &ArgMatches) -> Result<Regex> {
    let empty_pattern = "".to_string();
    let pattern = matches
        .get_one::<String>("FILTER")
        .unwrap_or(&empty_pattern);
    let rx = Regex::new(pattern)?;
    Ok(rx)
}

fn log_(matches: &ArgMatches) -> Result<()> {
    let result_set = get_result_set()?;
    let db = dm_unit::db::TestResults::new(DB_PATH)?;
    let results = db.get_test_results(&result_set)?;

    let rx = get_rx(matches)?;

    for (p, result) in &results {
        if !rx.is_match(p) {
            continue;
        }

        println!("{}: {}", p, if result.pass { "PASS" } else { "FAIL" });

        let log = result.log.trim_end().trim_start();
        if log.is_empty() {
            continue;
        }

        println!("--- LOG START ---");
        println!("{}", result.log.trim_end());
        println!("--- LOG END ---");
    }

    Ok(())
}

fn list(matches: &ArgMatches) -> Result<()> {
    let result_set = get_result_set()?;
    let db = dm_unit::db::TestResults::new(DB_PATH)?;
    let results = db.get_test_results(&result_set)?;

    let rx = get_rx(matches)?;

    let mut tests = all_tests()?;
    tests.filter(&rx);

    let mut pf = PathFormatter::new();
    for (p, _) in tests.into_inner() {
        // Do we only want to list failures?
        if *matches.get_one::<bool>("FAILURES").unwrap_or(&false) {
            if let Some(r) = results.get(&p) {
                if r.pass {
                    continue;
                }
            } else {
                continue;
            }
        }
        pf.print(&p);
        if let Some(r) = results.get(&p) {
            println!(" {}", if r.pass { "PASS" } else { "FAIL" });
        } else {
            println!(" -");
        }
    }

    Ok(())
}

fn run(matches: &ArgMatches, log_lines: Arc<Mutex<LogInner>>) -> Result<()> {
    let result_set = get_result_set()?;
    let mut db = dm_unit::db::TestResults::new(DB_PATH)?;
    let kernel_dir = Path::new(matches.get_one::<String>("kernel-dir").unwrap());

    let mut tests = if *matches.get_one::<bool>("BENCH").unwrap_or(&false) {
        benchmark_tests()?
    } else {
        all_tests()?
    };

    let rx = get_rx(matches)?;
    tests.filter(&rx);

    let mut runner = TestRunner::new(kernel_dir, tests)?;

    runner.set_filter(rx);

    /*
    if let Some(jobs) = matches.get_one::<usize>("JOBS") {
        runner.set_jobs(*jobs);
    }
    */

    // See if the jit flag is present
    if *matches.get_one::<bool>("JIT").unwrap_or(&false) {
        runner.set_jit();
    }

    if let Some(args) = matches.get_many::<String>("ARGS") {
        for arg in args {
            runner.append_arg(arg);
        }
    }

    let results = runner.exec(log_lines.clone());

    let mut pf = PathFormatter::new();
    let mut pass = 0;
    let mut fail = 0;

    for (p, r) in results {
        pf.print(&p);
        if r.pass {
            println!(" PASS");
            pass += 1;
        } else {
            println!(" FAIL");
            fail += 1;
        }

        db.insert_test_result(&result_set, &p, &r)?;
    }

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

fn main() -> Result<()> {
    let (new_log, inner) = CaptureLogger::new(Level::Debug);
    log::set_boxed_logger(Box::new(new_log))?;
    log::set_max_level(log::LevelFilter::Debug);

    let parser = Command::new("dm-unit")
    .version("0")
    .about("Unit test framework for device mapper kernel modules")
    .subcommand(
        Command::new("result-sets")
            .about("List result sets")
    )
    .subcommand(
        Command::new("list")
            .about("List available tests")
                .arg(Arg::new("FILTER")
                .index(1)
                .required(false)
                .help("regex filter to select which tests to run"))
                .arg(Arg::new("FAILURES")
                    .required(false)
                    .long("failures")
                    .action(ArgAction::SetTrue)
                    .help("select failing tests"))

    )
    .subcommand(
        Command::new("log")
            .about("Show logs from a result set")
                        .arg(Arg::new("FILTER")
                .index(1)
                .required(false)
                .help("regex filter to select which tests to run"))
    )
    .subcommand(
        Command::new("run")
            .about("Run tests")
            .arg(
                arg!(-k --"kernel-dir" <KERNEL_DIR>)
                    .help("Location of kernel source that contains built kernel modules to be tested.")
                    .required(true),
            )
                    .arg(
            Arg::new("BENCH")
                .long("bench")
                .action(ArgAction::SetTrue)
                .help("Run benchmarks"),
        )

            .arg(Arg::new("FILTER")
                .index(1)
                .required(false)
                .help("regex filter to select which tests to run"))
            .arg(
                Arg::new("JIT")
                    .long("jit")
                    .action(ArgAction::SetTrue)
                    .help("Turn on the experimental jit compiler"),
            )
            .arg(
                Arg::new("ARGS")
                    .long("args")
                    .action(ArgAction::Append)
                    .value_name("ARGS")
                    .help("Optional arguments for tests"),
            ),
    );

    let matches = parser.get_matches();
    match matches.subcommand() {
        Some(("list", sub_matches)) => {
            list(sub_matches)?;
        }
        Some(("log", sub_matches)) => {
            log_(sub_matches)?;
        }
        Some(("result-sets", _)) => {
            let db = dm_unit::db::TestResults::new(DB_PATH)?;
            let result_sets = db.get_result_sets()?;
            for rs in result_sets {
                println!("{}", rs);
            }
        }
        Some(("run", sub_matches)) => {
            run(sub_matches, inner)?;
        }
        _ => unreachable!("Exhausted list of subcommands and subcommand_required prevents 'None'"),
    }

    Ok(())
}

//-------------------------------
