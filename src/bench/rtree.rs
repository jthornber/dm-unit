use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::rtree::*;
use crate::tools::pdata::rtree::*;

use anyhow::Result;
use rand::prelude::*;
use rand::SeedableRng;
use std::fs::File;
use std::io::Write;

//-------------------------------

fn disable_data_sm(fix: &mut Fixture) -> Result<()> {
    fix.stub("sm_disk_inc_blocks", 0)?;
    fix.stub("sm_disk_dec_blocks", 0)?;
    fix.stub("sm_disk_new_block", 0)?;
    fix.stub("sm_disk_set_count", 0)?;
    Ok(())
}

fn bench_insert_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    disable_data_sm(fix)?; // test the rtree only

    const COUNT: u64 = 200000;
    const COMMIT_INTERVAL: usize = 100;
    let mut rtree = RTreeTest::new(fix, 2048)?;
    rtree.check()?;

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: i + 1234,
            len: 1,
            time: 0,
        })
        .collect();

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    mappings.shuffle(&mut rng);

    let mut csv = File::create("./rtree.csv")?;
    writeln!(
        csv,
        "inserts, nr_internal, nr_leaves, nr_entries, residency, instructions, read_locks, write_locks"
    )?;

    rtree.stats_start();

    let mut total = 0;
    for chunk in mappings.chunks(COMMIT_INTERVAL) {
        println!("=== round {} to {} ===", total, total + chunk.len());

        for m in chunk {
            let _nr_inserted = rtree.insert(m)?;
        }

        let (actions, tree_stats) = rtree.load_internal_stats()?;
        println!("{:?} {:?}", actions, tree_stats);

        let stats = rtree.check()?; // implicitly commit
        let residency = (stats.nr_entries * 100) / (stats.nr_leaves * MAX_LEAF_ENTRIES as u64);

        let delta = rtree.stats_delta()?;
        rtree.stats_start();
        total += chunk.len();
        writeln!(
            csv,
            "{}, {}, {}, {}, {}, {}, {:.1}, {:.1}",
            total,
            stats.nr_internal,
            stats.nr_leaves,
            stats.nr_entries,
            residency,
            delta.instrs / chunk.len() as u64,
            delta.read_locks as f64 / chunk.len() as f64,
            delta.write_locks as f64 / chunk.len() as f64,
        )?;
    }

    rtree.del()?;

    Ok(())
}

fn bench_insert_ascending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    disable_data_sm(fix)?; // test the rtree only

    const COUNT: u64 = 200000;
    const COMMIT_INTERVAL: usize = 100;
    let mut rtree = RTreeTest::new(fix, 1024)?;
    rtree.check()?;

    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i * 2, // keep the entries not merged
            data_begin: i + 1234,
            len: 1,
            time: 0,
        })
        .collect();

    let mut csv = File::create("./rtree_ascending.csv")?;
    writeln!(
        csv,
        "inserts, nr_internal, nr_leaves, nr_entries, residency, instructions, read_locks, write_locks"
    )?;

    rtree.stats_start();

    let mut total = 0;
    for chunk in mappings.chunks(COMMIT_INTERVAL) {
        for m in chunk {
            let _nr_inserted = rtree.insert(m)?;
        }

        let stats = rtree.check()?; // implicitly commit
        let residency = (stats.nr_entries * 100) / (stats.nr_leaves * MAX_LEAF_ENTRIES as u64);

        let delta = rtree.stats_delta()?;
        rtree.stats_start();

        total += chunk.len();
        writeln!(
            csv,
            "{}, {}, {}, {}, {}, {}, {}, {}",
            total,
            stats.nr_internal,
            stats.nr_leaves,
            stats.nr_entries,
            residency,
            delta.instrs / chunk.len() as u64,
            delta.read_locks / chunk.len() as u64,
            delta.write_locks / chunk.len() as u64,
        )?;
    }

    rtree.del()?;

    Ok(())
}

fn bench_lookup_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    disable_data_sm(fix)?; // test the rtree only

    const COUNT: u64 = 200000;
    const COMMIT_INTERVAL: usize = 100;
    let mut rtree = RTreeTest::new(fix, 1024)?;
    rtree.check()?;

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: i + 1234,
            len: 1,
            time: 0,
        })
        .collect();

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    mappings.shuffle(&mut rng);

    let mut csv = File::create("./rtree.csv")?;
    writeln!(
        csv,
        "nr_inserted, nr_internal, nr_leaves, nr_entries, residency, instructions, read_locks, write_locks"
    )?;

    let mut total = 0;
    for chunk in mappings.chunks(COMMIT_INTERVAL) {
        for m in chunk {
            let _nr_inserted = rtree.insert(m)?;
        }

        let stats = rtree.check()?; // implicitly commit

        rtree.stats_start();
        for m in chunk {
            rtree.lookup(m.thin_begin)?;
        }
        let delta = rtree.stats_delta()?;

        total += chunk.len();
        let residency = (stats.nr_entries * 100) / (stats.nr_leaves * MAX_LEAF_ENTRIES as u64);
        writeln!(
            csv,
            "{}, {}, {}, {}, {}, {}, {:.1}, {:.1}",
            total,
            stats.nr_internal,
            stats.nr_leaves,
            stats.nr_entries,
            residency,
            delta.instrs / chunk.len() as u64,
            delta.read_locks as f64 / chunk.len() as f64,
            delta.write_locks as f64 / chunk.len() as f64,
        )?;
    }

    rtree.del()?;

    Ok(())
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
        "/pdata/rtree/",

        test_section! {
            "insert/",
            test!("random", bench_insert_random)
        }

        test_section! {
            "insert/",
            test!("ascending", bench_insert_ascending)
        }

        test_section! {
            "lookup/",
            test!("random", bench_lookup_random)
        }
    };

    Ok(())
}

//-------------------------------
