use crate::fixture::*;
use crate::stats::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::btree::*;

use anyhow::Result;
use rand::prelude::*;
use rand::SeedableRng;
use std::fs::File;
use std::io::Write;

//-------------------------------

fn do_insert_bench_(
    fix: &mut Fixture,
    keys: &[u64],
    commit_interval: usize,
    track_insertion: bool,
    print_layout: bool,
) -> Result<()> {
    standard_globals(fix)?;
    let mut btree = BTreeTest::new(fix)?;

    let mut csv = File::create("./btree.csv")?;
    writeln!(
        csv,
        "inserts, nr_leaves, nr_entries, residency, instructions, read_locks, write_locks"
    )?;

    let mut insert_tracker = CostTracker::new("./btree-insert.csv")?;
    let bm = btree.get_bm();

    let mut total = 0;
    for chunk in keys.chunks(commit_interval) {
        btree.stats_start();

        btree.begin()?;
        for k in chunk {
            insert_tracker.begin(btree.fix, &bm);
            btree.insert(*k)?;
            if track_insertion {
                insert_tracker.end(btree.fix, &bm)?;
            }
        }
        btree.commit()?;

        let delta = btree.stats_delta()?;
        let stats = btree.get_tree_stats()?;

        total += chunk.len();
        writeln!(
            csv,
            "{}, {}, {}, {}, {}, {}, {}",
            total,
            stats.nr_leaves,
            stats.nr_entries,
            residency::<Value64>(&stats)?,
            delta.instrs / chunk.len() as u64,
            delta.read_locks / chunk.len() as u64,
            delta.write_locks / chunk.len() as u64,
        )?;

        if print_layout {
            btree.print_layout()?;
        }
    }

    Ok(())
}

fn do_lookup_bench_(fix: &mut Fixture, keys: &[u64], commit_interval: usize) -> Result<()> {
    standard_globals(fix)?;
    let mut btree = BTreeTest::new(fix)?;

    let mut csv = File::create("./btree.csv")?;
    writeln!(
        csv,
        "nr_inserted, nr_leaves, nr_entries, residency, instructions, read_locks, write_locks"
    )?;

    let mut total = 0;
    for chunk in keys.chunks(commit_interval) {
        btree.begin()?;
        for k in chunk {
            btree.insert(*k)?;
        }
        btree.commit()?;

        btree.stats_start();
        for k in chunk {
            btree.lookup(*k)?;
        }
        let delta = btree.stats_delta()?;
        let stats = btree.get_tree_stats()?;

        total += chunk.len();
        writeln!(
            csv,
            "{}, {}, {}, {}, {}, {}, {}",
            total,
            stats.nr_leaves,
            stats.nr_entries,
            residency::<Value64>(&stats)?,
            delta.instrs / chunk.len() as u64,
            delta.read_locks / chunk.len() as u64,
            delta.write_locks / chunk.len() as u64,
        )?;
    }

    Ok(())
}

fn bench_insert_random(fix: &mut Fixture) -> Result<()> {
    let mut keys: Vec<u64> = (0..200000).rev().collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    keys.shuffle(&mut rng);
    do_insert_bench_(fix, &keys, 100, false, false)
}

fn bench_insert_random_with_layout(fix: &mut Fixture) -> Result<()> {
    let mut keys: Vec<u64> = (0..200000).rev().collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    keys.shuffle(&mut rng);
    do_insert_bench_(fix, &keys, 100, false, true)
}

fn bench_insert_ascending(fix: &mut Fixture) -> Result<()> {
    let keys: Vec<u64> = (0..5000).collect();
    do_insert_bench_(fix, &keys, 100, true, false)
}

fn bench_insert_ascending_with_layout(fix: &mut Fixture) -> Result<()> {
    let keys: Vec<u64> = (0..5000).collect();
    do_insert_bench_(fix, &keys, 100, true, true)
}

fn bench_lookup_random(fix: &mut Fixture) -> Result<()> {
    let mut keys: Vec<u64> = (0..200000).rev().collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    keys.shuffle(&mut rng);
    do_lookup_bench_(fix, &keys, 100)
}

//-------------------------------

pub fn register_bench(tests: &mut TestSet) -> Result<()> {
    let kmodules = vec![PDATA_MOD];
    let mut prefix: Vec<&'static str> = Vec::new();

    macro_rules! test_section {
        ($path:expr, $($s:stmt)*) => {{
            prefix.push($path);
            $($s)*
            prefix.pop().unwrap();
        }}
    }

    macro_rules! test {
        ($path:expr, $func:expr) => {{
            prefix.push($path);
            let p = prefix.concat();
            prefix.pop().unwrap();
            tests.register(&p, Test::new(kmodules.clone(), Box::new($func)));
        }};
    }

    test_section! {
        "/pdata/btree/",

        test_section! {
            "insert/",
            test!("random", bench_insert_random)
        }

        test_section! {
            "insert/",
            test!("random_layout", bench_insert_random_with_layout)
        }

        test_section! {
            "insert/",
            test!("ascending", bench_insert_ascending)
        }

        test_section! {
            "insert/",
            test!("ascending_layout", bench_insert_ascending_with_layout)
        }

        test_section! {
            "lookup/",
            test!("random", bench_lookup_random)
        }
    };

    Ok(())
}

//-------------------------------
