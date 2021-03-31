use anyhow::Result;
use log::*;
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::BTreeSet;

use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::block_device::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::thinp_metadata::*;

//-------------------------------

#[allow(dead_code)]
struct ThinPool {
    nr_metadata_blocks: u64,
    pmd: Addr,
    baseline: Stats,
}

struct ThinDev {
    td: Addr,
}

impl ThinPool {
    fn new(
        fix: &mut Fixture,
        nr_metadata_blocks: u64,
        data_block_size: u64,
        nr_data_blocks: u64,
    ) -> Result<Self> {
        let bdev_ptr = mk_block_device(&mut fix.vm.mem, 0, 8 * nr_metadata_blocks)?;
        let pmd = dm_pool_metadata_open(fix, bdev_ptr, data_block_size, true)?;
        dm_pool_resize_data_dev(fix, pmd, nr_data_blocks)?;
        let baseline = Stats::collect_stats(fix);

        Ok(ThinPool {
            nr_metadata_blocks,
            pmd,
            baseline,
        })
    }

    fn stats_start(&mut self, fix: &mut Fixture) {
        self.baseline = Stats::collect_stats(fix);
    }

    fn stats_report(&mut self, fix: &mut Fixture, desc: &str, count: u64) -> Result<()> {
        let delta = self.baseline.delta(fix);
        info!(
            "{}: instrs = {}, read_locks = {:.1}, write_locks = {:.1}, metadata = {}/{}",
            desc,
            delta.instrs / count,
            delta.read_locks as f64 / count as f64,
            delta.write_locks as f64 / count as f64,
            self.nr_metadata_blocks - self.free_metadata_blocks(fix)?,
            self.nr_metadata_blocks,
        );
        Ok(())
    }

    fn create_thin(&mut self, fix: &mut Fixture, thin_id: ThinId) -> Result<()> {
        dm_pool_create_thin(fix, self.pmd, thin_id)
    }

    fn create_snap(&mut self, fix: &mut Fixture, origin_id: ThinId, snap_id: ThinId) -> Result<()> {
        dm_pool_create_snap(fix, self.pmd, origin_id, snap_id)
    }

    fn delete_thin(&mut self, fix: &mut Fixture, thin_id: ThinId) -> Result<()> {
        dm_pool_delete_thin_device(fix, self.pmd, thin_id)
    }

    fn commit(&mut self, fix: &mut Fixture) -> Result<()> {
        dm_pool_commit_metadata(fix, self.pmd)
    }

    fn open_thin(&mut self, fix: &mut Fixture, thin_id: ThinId) -> Result<ThinDev> {
        let td = dm_pool_open_thin_device(fix, self.pmd, thin_id)?;
        Ok(ThinDev { td })
    }

    fn close_thin(&mut self, fix: &mut Fixture, td: ThinDev) -> Result<()> {
        dm_pool_close_thin_device(fix, td.td)
    }

    fn alloc_data_block(&mut self, fix: &mut Fixture) -> Result<u64> {
        dm_pool_alloc_data_block(fix, self.pmd)
    }

    fn insert_block(
        &mut self,
        fix: &mut Fixture,
        td: &ThinDev,
        thin_b: u64,
        data_b: u64,
    ) -> Result<()> {
        dm_thin_insert_block(fix, td.td, thin_b, data_b)
    }

    fn free_metadata_blocks(&mut self, fix: &mut Fixture) -> Result<u64> {
        dm_pool_get_free_metadata_block_count(fix, self.pmd)
    }
}

//-------------------------------

fn test_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let _t = ThinPool::new(fix, 1024, 64, 102400)?;
    Ok(())
}

fn test_create_many_thins(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut t = ThinPool::new(fix, 10240, 64, 102400)?;
    for tid in 0..1000 {
        t.create_thin(fix, tid)?;
    }

    t.commit(fix)?;

    for tid in 0..1000 {
        t.delete_thin(fix, tid)?;
    }

    Ok(())
}

fn test_create_rolling_snaps(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count = 1000;
    let mut t = ThinPool::new(fix, 10240, 64, 102400)?;
    t.create_thin(fix, 0)?;

    for snap in 1..count {
        t.create_snap(fix, snap, snap - 1)?;
    }

    // A commit is needed, otherwise delete will not work (not sure why,
    // or if this is a feature).
    t.commit(fix)?;

    for tid in 0..count {
        t.delete_thin(fix, tid)?;
    }

    t.commit(fix)?;

    Ok(())
}

fn do_provision_single_thin(fix: &mut Fixture, thin_blocks: &[u64]) -> Result<()> {
    let commit_interval = 1000;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, 102400)?;
    pool.create_thin(fix, 0)?;
    let td = pool.open_thin(fix, 0)?;

    let mut insert_count = 0;
    pool.stats_start(fix);
    for thin_b in thin_blocks {
        let data_b = pool.alloc_data_block(fix)?;
        pool.insert_block(fix, &td, *thin_b, data_b)?;
        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            pool.stats_report(fix, "provision", commit_interval)?;
            pool.stats_start(fix);
            insert_count = 0;
        }
    }

    // A commit is needed, otherwise delete will not work (not sure why,
    // or if this is a feature).
    pool.commit(fix)?;
    pool.close_thin(fix, td)?;

    Ok(())
}

const PROVISION_SINGLE_COUNT: u64 = 100000;

fn test_provision_single_thin_linear(fix: &mut Fixture) -> Result<()> {
    let thin_blocks: Vec<u64> = (0..PROVISION_SINGLE_COUNT).into_iter().collect();
    do_provision_single_thin(fix, &thin_blocks)
}

fn test_provision_single_thin_random(fix: &mut Fixture) -> Result<()> {
    let mut thin_blocks: Vec<u64> = (0..PROVISION_SINGLE_COUNT).into_iter().collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    thin_blocks.shuffle(&mut rng);
    do_provision_single_thin(fix, &thin_blocks)
}

fn generate_runs(nr_blocks: u64, average_run_length: u64) -> Vec<u64> {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    let nr_runs = nr_blocks / average_run_length;
    for _ in 0..nr_runs {
        endpoints.insert(rng.gen_range(0..nr_blocks));
    }
    endpoints.insert(nr_blocks);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }
    ranges.shuffle(&mut rng);

    let mut thin_blocks = Vec::new();
    for r in ranges {
        for k in r {
            thin_blocks.push(k);
        }
    }

    thin_blocks
}

fn test_provision_single_thin_runs(fix: &mut Fixture) -> Result<()> {
    let thin_blocks = generate_runs(PROVISION_SINGLE_COUNT, 20);
    do_provision_single_thin(fix, &thin_blocks)
}

//-------------------------------

// FIXME: no overwrites in this test
fn do_provision_recursive_snap(fix: &mut Fixture, thin_blocks: &[u64]) -> Result<()> {
    let commit_interval = 1000;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, thin_blocks.len() as u64)?;
    let mut thin_id = 0;
    pool.create_thin(fix, 0)?;
    let mut td = pool.open_thin(fix, 0)?;

    let mut insert_count = 0;
    pool.stats_start(fix);
    for thin_b in thin_blocks {
        let data_b = pool.alloc_data_block(fix)?;
        pool.insert_block(fix, &td, *thin_b, data_b)?;
        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            pool.stats_report(fix, "provision", commit_interval)?;

            pool.close_thin(fix, td)?;
            pool.create_snap(fix, thin_id + 1, thin_id)?;
            thin_id += 1;
            if thin_id >= 10 {
                pool.delete_thin(fix, thin_id - 10)?;
            }
            pool.commit(fix)?;
            td = pool.open_thin(fix, thin_id)?;

            pool.stats_start(fix);
            insert_count = 0;
        }
    }

    pool.close_thin(fix, td)?;

    Ok(())
}

// This test blows up, with massive amounts of instrs, read/write locks per insert.
// Probably the fault of the space maps.
fn test_provision_recursive_snaps(fix: &mut Fixture) -> Result<()> {
    let thin_blocks = generate_runs(20_000, 20);
    do_provision_recursive_snap(fix, &thin_blocks)
}

//-------------------------------

// FIXME: no overwrites in this test
fn do_provision_rolling_snap(fix: &mut Fixture, thin_blocks: &[u64]) -> Result<()> {
    let commit_interval = 1000;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, thin_blocks.len() as u64)?;
    let mut thin_id = 0;
    pool.create_thin(fix, 0)?;
    let td = pool.open_thin(fix, 0)?;

    let mut alloc_tracker = CostTracker::new("alloc-block.csv")?;
    let mut insert_tracker = CostTracker::new("insert-block.csv")?;
    let mut delete_tracker = CostTracker::new("delete-thin.csv")?;
    let mut insert_count = 0;
    pool.stats_start(fix);
    for thin_b in thin_blocks {
        alloc_tracker.begin(fix);
        let data_b = pool.alloc_data_block(fix)?;
        alloc_tracker.end(fix)?;

        insert_tracker.begin(fix);
        pool.insert_block(fix, &td, *thin_b, data_b)?;
        insert_tracker.end(fix)?;

        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            pool.stats_report(fix, "provision", commit_interval)?;

            pool.create_snap(fix, thin_id + 1, 0)?;
            thin_id += 1;
            if thin_id > 10 {
                delete_tracker.begin(fix);
                pool.delete_thin(fix, thin_id - 10)?;
                delete_tracker.end(fix)?;
            }
            pool.commit(fix)?;

            pool.stats_start(fix);
            insert_count = 0;
        }
    }

    pool.close_thin(fix, td)?;
    fix.log_func_calls("disk_ll_save_ie")?;
    fix.log_func_calls("sm_ll_inc")?;

    // FIXME: run thin_check

    Ok(())
}

// This test blows up, with massive amounts of instrs, read/write locks per insert.
// Probably the fault of the space maps.
fn test_provision_rolling_snaps(fix: &mut Fixture) -> Result<()> {
    let thin_blocks = generate_runs(20_000, 20);
    do_provision_rolling_snap(fix, &thin_blocks)
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
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
            runner.register(&p, Box::new($func));
        }};
    }

    test_section! {
        "/thinp/",
        test!("create", test_create)
        test!("create-delete-many-thins", test_create_many_thins)
        test!("create-rolling-snaps", test_create_rolling_snaps)
        test!("provision-single-thin/linear", test_provision_single_thin_linear)
        test!("provision-single-thin/random", test_provision_single_thin_random)
        test!("provision-single-thin/runs", test_provision_single_thin_runs)
        test!("snaps/recursive", test_provision_recursive_snaps)
        test!("snaps/rolling", test_provision_rolling_snaps)
    }

    Ok(())
}

//-------------------------------
