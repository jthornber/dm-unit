use anyhow::{ensure, Result};
use log::*;
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use thinp::io_engine::*;
use thinp::pdata::btree_error::KeyRange;
use thinp::pdata::btree_walker::*;
use thinp::pdata::space_map::common::{IndexEntry, SMRoot};
use thinp::pdata::unpack::*;
use thinp::report::*;
use thinp::thin::block_time::*;
use thinp::thin::check::*;
use thinp::thin::superblock::*;

use crate::emulator::memory::*;
use crate::fixture::*;
use crate::stats::*;
use crate::stubs::block_device::*;
use crate::stubs::block_manager::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::btree::*;
use crate::tests::rtree::{self, *};
use crate::wrappers::thinp_metadata::*;

//-------------------------------

#[allow(dead_code)]
struct ThinPool {
    nr_metadata_blocks: u64,
    bm_ptr: Addr,
    pmd: Addr,
    baseline: Stats,
}

struct ThinDev {
    td: Addr,
}

impl ThinDev {
    fn alloc_data_block(&mut self, fix: &mut Fixture) -> Result<u64> {
        dm_thin_alloc_data_block(fix, self.td)
    }

    fn insert_block(&mut self, fix: &mut Fixture, thin_b: u64, data_b: u64) -> Result<()> {
        dm_thin_insert_block(fix, self.td, thin_b, data_b)
    }
}

struct DebugReportInner {}

impl ReportInner for DebugReportInner {
    fn set_title(&mut self, txt: &str) {
        debug!("report title: {}", txt);
    }

    fn set_sub_title(&mut self, txt: &str) {
        debug!("report sub title: {}", txt);
    }

    fn set_level(&mut self, _level: LogLevel) {}

    fn progress(&mut self, _percent: u8) {}

    fn log(&mut self, txt: &str, _level: LogLevel) {
        debug!("report: {}", txt);
    }

    fn to_stdout(&mut self, txt: &str) {
        println!("{}", txt);
    }

    fn complete(&mut self) {}

    fn get_prompt_input(&mut self, prompt: &str) -> std::io::Result<String> {
        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("get_prompt_input: {}", prompt),
        ))
    }
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
        let bm_ptr = dm_pool_get_block_manager(fix, pmd)?;
        let bm = get_bm(fix, bm_ptr);
        let baseline = Stats::collect_stats(fix, &bm);

        Ok(ThinPool {
            nr_metadata_blocks,
            bm_ptr,
            pmd,
            baseline,
        })
    }

    fn stats_start(&mut self, fix: &mut Fixture) {
        let bm = get_bm(fix, self.bm_ptr);
        self.baseline = Stats::collect_stats(fix, &bm);
    }

    fn stats_report(&mut self, fix: &mut Fixture, desc: &str, count: u64) -> Result<()> {
        let bm = get_bm(fix, self.bm_ptr);
        let delta = self.baseline.delta(fix, &bm);
        info!(
            "{}: instrs = {}, read_locks = {:.1}, write_locks = {:.1}, disk_reads = {:2}, metadata = {}/{}",
            desc,
            delta.instrs / count,
            delta.read_locks as f64 / count as f64,
            delta.write_locks as f64 / count as f64,
            delta.disk_reads as f64 / count as f64,
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

    fn remove_range(&mut self, fix: &mut Fixture, td: &ThinDev, b: u64, e: u64) -> Result<()> {
        dm_thin_remove_range(fix, td.td, b, e)
    }

    fn free_metadata_blocks(&mut self, fix: &mut Fixture) -> Result<u64> {
        // thinp subtracts wiggle room of 0x400 from the free count as
        // transaction overhead.  I add it back in here because I want
        // this number to agree with that from thin_check.
        dm_pool_get_free_metadata_block_count(fix, self.pmd).map(|n| n + 0x400)
    }

    fn free_data_blocks(&mut self, fix: &mut Fixture) -> Result<u64> {
        dm_pool_get_free_block_count(fix, self.pmd)
    }

    fn _check(&mut self, fix: &Fixture) -> Result<()> {
        // let report = std::sync::Arc::new(Report::new(Box::new(DebugReportInner {})));
        let report = std::sync::Arc::new(mk_quiet_report());
        let engine = get_bm(fix, self.bm_ptr);
        let space_maps = check_with_maps(engine, report)?;
        let metadata_sm = space_maps.metadata_sm.lock().unwrap();
        debug!(
            "metadata: {}/{} allocated",
            metadata_sm.get_nr_allocated()?,
            metadata_sm.get_nr_blocks()?
        );

        /*
        // We discard unused blocks to save memory.
        // FIXME: only discard blocks that were allocated last transaction.
        let bm = get_bm()?.clone();
        for b in 0..metadata_sm.get_nr_blocks()? {
            if metadata_sm.get(b)? == 0 {
                bm.forget(b)?;
            }
        }
        */

        let data_sm = space_maps.data_sm.lock().unwrap();
        debug!(
            "data: {}/{} allocated",
            data_sm.get_nr_allocated()?,
            data_sm.get_nr_blocks()?
        );

        Ok(())
    }

    fn check_rtree(&self, fix: &Fixture) -> Result<()> {
        let bm = get_bm(fix, self.bm_ptr);
        let sb = read_superblock(bm.as_ref(), 0)?;

        let mut path = Vec::new();
        let roots = btree_to_map(&mut path, bm.clone(), false, sb.mapping_root)?;
        for (thin_id, root) in roots {
            let mut stats = rtree::TreeStats::default();
            let kr = KeyRange::new();
            rtree_check(&*bm, root, &kr, &mut stats)?;
            println!("thin id {}, stats {:?}", thin_id, stats);
        }

        Ok(())
    }

    fn _show_mapping_residency(&self, fix: &Fixture) -> Result<()> {
        let bm = get_bm(fix, self.bm_ptr);
        let engine: Arc<dyn IoEngine + Send + Sync> = get_bm(fix, self.bm_ptr);
        let sb = read_superblock(engine.as_ref(), 0)?;

        let mut path = Vec::new();
        let roots = btree_to_map(&mut path, engine.clone(), false, sb.mapping_root)?;
        for (thin_id, root) in roots {
            debug!(
                "residency of thin {} = {}",
                thin_id,
                calc_residency::<Value64>(&bm, root)?
            );
        }

        let root = unpack::<SMRoot>(&sb.data_sm_root[0..])?;
        debug!(
            "residency of data sm index entries: {}",
            calc_residency::<IndexEntry>(&bm, root.bitmap_root)?
        );
        debug!(
            "residency of data sm overflow: {}",
            calc_residency::<Value32>(&bm, root.ref_count_root)?
        );

        let root = unpack::<SMRoot>(&sb.metadata_sm_root[0..])?;
        debug!(
            "residency of metadata sm overflow: {}",
            calc_residency::<Value32>(&bm, root.ref_count_root)?
        );
        Ok(())
    }

    fn build_run_histogram(&self, fix: &Fixture) -> Result<BTreeMap<usize, usize>> {
        let engine: Arc<dyn IoEngine + Send + Sync> = get_bm(fix, self.bm_ptr).clone();
        let sb = read_superblock(engine.as_ref(), 0)?;

        let mut path = Vec::new();
        let roots = btree_to_map(&mut path, engine.clone(), false, sb.mapping_root)?;

        let mut histogram = BTreeMap::new();
        for (_thin_id, root) in roots {
            let blocks: BTreeMap<u64, BlockTime> =
                btree_to_map(&mut path, engine.clone(), false, root)?;

            // Build a histogram of run lengths
            let mut last_entry: Option<(u64, BlockTime)> = None;
            let mut run_length = 0;

            for (k, v) in &blocks {
                match last_entry {
                    Some((last_key, last_value))
                        if last_key + 1 == *k && last_value.block + 1 == v.block =>
                    {
                        // Blocks and keys are both adjacent, increment run length
                        run_length += 1;
                    }
                    _ => {
                        // Blocks or keys are not adjacent or this is the first entry,
                        // count the run length and start a new run
                        if let Some(_last) = last_entry {
                            *histogram.entry(run_length).or_insert(0) += 1;
                        }
                        run_length = 1;
                    }
                }
                last_entry = Some((*k, v.clone()));
            }

            // Record the last run
            if let Some(_last) = last_entry {
                *histogram.entry(run_length).or_insert(0) += 1;
            }
        }

        Ok(histogram)
    }

    fn show_fragmentation(&self, histogram: &BTreeMap<usize, usize>) -> Result<()> {
        // Print the histogram
        for (run_length, count) in histogram {
            debug!("run length {}: {}", run_length, count);
        }

        Ok(())
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
    let mut td = pool.open_thin(fix, 0)?;

    let mut alloc_tracker = CostTracker::new("single-alloc-block.csv")?;
    let mut insert_tracker = CostTracker::new("single-insert-block.csv")?;
    let mut overall_tracker = CostTracker::new("single-provision.csv")?;
    let mut insert_count = 0;
    let bm = get_bm(fix, pool.bm_ptr);
    overall_tracker.begin(fix, &bm);
    pool.stats_start(fix);
    for thin_b in thin_blocks {
        alloc_tracker.begin(fix, &bm);
        let data_b = td.alloc_data_block(fix)?;
        alloc_tracker.end(fix, &bm)?;

        insert_tracker.begin(fix, &bm);
        td.insert_block(fix, *thin_b, data_b)?;
        insert_tracker.end(fix, &bm)?;

        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            pool.stats_report(fix, "provision", commit_interval)?;
            pool.stats_start(fix);
            pool.check_rtree(fix)?;
            overall_tracker.end_in_iterations(fix, &bm, commit_interval)?;
            overall_tracker.begin(fix, &bm);
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
    let thin_blocks: Vec<u64> = (0..PROVISION_SINGLE_COUNT).collect();
    do_provision_single_thin(fix, &thin_blocks)
}

fn test_provision_single_thin_random(fix: &mut Fixture) -> Result<()> {
    let mut thin_blocks: Vec<u64> = (0..PROVISION_SINGLE_COUNT).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    thin_blocks.shuffle(&mut rng);
    do_provision_single_thin(fix, &thin_blocks)
}

fn generate_ranges(nr_blocks: u64, average_run_length: u64) -> Vec<std::ops::Range<u64>> {
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
    ranges
}

fn generate_runs(nr_blocks: u64, average_run_length: u64) -> Vec<u64> {
    let ranges = generate_ranges(nr_blocks, average_run_length);
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
        let data_b = td.alloc_data_block(fix)?;
        td.insert_block(fix, *thin_b, data_b)?;
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
    let mut td = pool.open_thin(fix, 0)?;

    let mut alloc_tracker = CostTracker::new("alloc-block.csv")?;
    let mut insert_tracker = CostTracker::new("insert-block.csv")?;
    let mut delete_tracker = CostTracker::new("delete-thin.csv")?;
    let mut insert_count = 0;
    let bm = get_bm(fix, pool.bm_ptr);
    pool.stats_start(fix);
    for thin_b in thin_blocks {
        alloc_tracker.begin(fix, &bm);
        let data_b = td.alloc_data_block(fix)?;
        alloc_tracker.end(fix, &bm)?;

        insert_tracker.begin(fix, &bm);
        td.insert_block(fix, *thin_b, data_b)?;
        insert_tracker.end(fix, &bm)?;

        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            pool.stats_report(fix, "provision", commit_interval)?;

            pool.create_snap(fix, thin_id + 1, 0)?;
            thin_id += 1;
            if thin_id > 10 {
                delete_tracker.begin(fix, &bm);
                pool.delete_thin(fix, thin_id - 10)?;
                delete_tracker.end(fix, &bm)?;
            }
            pool.commit(fix)?;
            //pool.stats_report(fix, "provision", commit_interval)?;
            pool.check_rtree(fix)?;

            pool.stats_start(fix);
            insert_count = 0;
        }
    }

    pool.close_thin(fix, td)?;
    //pool.show_mapping_residency(fix)?; // TODO: rtree version
    // get_bm()?.write_to_disk(Path::new("thinp-metadata.bin"))?;

    Ok(())
}

// This test blows up, with massive amounts of instrs, read/write locks per insert.
// Probably the fault of the space maps.
fn test_provision_rolling_snaps(fix: &mut Fixture) -> Result<()> {
    let thin_blocks = generate_runs(20_000, 20);
    do_provision_rolling_snap(fix, &thin_blocks)
}

//-------------------------------

const DISCARD_SINGLE_COUNT: u64 = 100000;

fn test_discard_single_thin(fix: &mut Fixture) -> Result<()> {
    let commit_interval = 100;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, 102400)?;
    pool.create_thin(fix, 0)?;
    let mut td = pool.open_thin(fix, 0)?;

    // Fully provision the thin
    info!("provisioning thin");
    for b in 0..DISCARD_SINGLE_COUNT {
        let data_b = td.alloc_data_block(fix)?;
        td.insert_block(fix, b, data_b)?;
    }
    pool.commit(fix)?;
    info!("provisioned");

    let mut discard_tracker = CostTracker::new("discard-blocks.csv")?;

    let thin_blocks = generate_ranges(20_000, 20);
    let bm = get_bm(fix, pool.bm_ptr);
    pool.stats_start(fix);
    let mut discard_count = 0;
    for std::ops::Range { start, end } in thin_blocks {
        discard_count += 1;

        discard_tracker.begin(fix, &bm);
        pool.remove_range(fix, &td, start, end)?;
        discard_tracker.end(fix, &bm)?;

        if discard_count == commit_interval {
            pool.commit(fix)?;
            pool.stats_report(fix, "discard", commit_interval)?;
            pool.check_rtree(fix)?;
            pool.stats_start(fix);
            discard_count = 0;
        }
    }

    pool.commit(fix)?;
    pool.close_thin(fix, td)?;

    Ok(())
}

//-------------------------------

// Exactly the same as the provision rolling snap test, except we delete snaps
// with a single, large discard.
fn do_discard_rolling_snap(fix: &mut Fixture, thin_blocks: &[u64], nr_blocks: u64) -> Result<()> {
    let commit_interval = 1000;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, thin_blocks.len() as u64)?;
    let mut thin_id = 0;
    let bm = get_bm(fix, pool.bm_ptr);
    pool.create_thin(fix, 0)?;
    let mut td = pool.open_thin(fix, 0)?;

    let mut discard_tracker = CostTracker::new("discard-whole-thin.csv")?;
    let mut insert_count = 0;
    for thin_b in thin_blocks {
        let data_b = td.alloc_data_block(fix)?;
        td.insert_block(fix, *thin_b, data_b)?;

        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;

            pool.create_snap(fix, thin_id + 1, 0)?;
            thin_id += 1;
            if thin_id > 10 {
                let old_snap = pool.open_thin(fix, thin_id - 10)?;

                discard_tracker.begin(fix, &bm);
                pool.remove_range(fix, &old_snap, 0, nr_blocks)?;
                discard_tracker.end(fix, &bm)?;

                pool.close_thin(fix, old_snap)?;
                pool.delete_thin(fix, thin_id - 10)?;
            }
            pool.commit(fix)?;
            pool.check_rtree(fix)?;

            insert_count = 0;
        }
    }

    pool.close_thin(fix, td)?;
    //pool.show_mapping_residency(fix)?; // TODO: rtree version
    // get_bm()?.write_to_disk(Path::new("thinp-metadata.bin"))?;

    Ok(())
}

// This test blows up, with massive amounts of instrs, read/write locks per insert.
// Probably the fault of the space maps.
fn test_discard_rolling_snaps(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 20_000;
    let thin_blocks = generate_runs(nr_blocks, 20);
    do_discard_rolling_snap(fix, &thin_blocks, nr_blocks)
}

//-------------------------------

fn test_delete_frees_blocks(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_blocks = 20_000;
    let nr_thins = 4;
    let commit_interval = 1000;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, nr_blocks * nr_thins as u64)?;

    let mut td = create_separate_thins(fix, &mut pool, nr_thins)?;

    let mut insert_count = 0;
    for thin_b in 0..nr_blocks {
        for i in 0..nr_thins {
            let data_b = td[i as usize].as_mut().unwrap().alloc_data_block(fix)?;
            td[i as usize]
                .as_mut()
                .unwrap()
                .insert_block(fix, thin_b, data_b)?;
        }

        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            insert_count = 0;
        }
    }

    pool.commit(fix)?;

    // We should have used up all space now
    debug!("nr free = {}", pool.free_data_blocks(fix)?);
    ensure!(pool.free_data_blocks(fix)? == 0, "expected no free blocks");

    // Allocation should fail
    pool.create_thin(fix, nr_thins)?;
    let mut thin = pool.open_thin(fix, nr_thins)?;
    ensure!(
        thin.alloc_data_block(fix).is_err(),
        "expected alloc to fail"
    );

    // Now delete one of the devices
    let old_thin = td[0].take().unwrap();
    pool.close_thin(fix, old_thin)?;
    pool.delete_thin(fix, 0)?;
    pool.commit(fix)?;

    // and allocation should succeed
    ensure!(
        thin.alloc_data_block(fix).is_ok(),
        "expected alloc to succeed"
    );

    Ok(())
}

//-------------------------------

fn create_separate_thins(
    fix: &mut Fixture,
    pool: &mut ThinPool,
    nr_thins: u32,
) -> Result<Vec<Option<ThinDev>>> {
    let mut td = vec![];
    for i in 0..nr_thins {
        pool.create_thin(fix, i)?;
        td.push(Some(pool.open_thin(fix, i)?));
    }
    Ok(td)
}

fn create_recursive_snaps(
    fix: &mut Fixture,
    pool: &mut ThinPool,
    nr_thins: u32,
) -> Result<Vec<Option<ThinDev>>> {
    let mut td = vec![];
    for i in 0..nr_thins {
        if i == 0 {
            pool.create_thin(fix, 0)?;
        } else {
            pool.create_snap(fix, i, i - 1)?;
        }
        td.push(Some(pool.open_thin(fix, i)?));
    }
    Ok(td)
}

fn do_fragment_test<F>(fix: &mut Fixture, func: F) -> Result<()>
where
    F: FnOnce(&mut Fixture, &mut ThinPool, u32) -> Result<Vec<Option<ThinDev>>>,
{
    let nr_blocks = 20_000;
    let nr_thins = 4;
    let commit_interval = 1000;

    standard_globals(fix)?;

    let mut pool = ThinPool::new(fix, 10240, 64, nr_blocks * nr_thins as u64)?;

    let mut td = func(fix, &mut pool, nr_thins)?;

    let mut insert_count = 0;
    for thin_b in 0..nr_blocks {
        for i in 0..nr_thins {
            let data_b = td[i as usize].as_mut().unwrap().alloc_data_block(fix)?;
            td[i as usize]
                .as_mut()
                .unwrap()
                .insert_block(fix, thin_b, data_b)?;
        }

        insert_count += 1;

        if insert_count == commit_interval {
            pool.commit(fix)?;
            insert_count = 0;
        }
    }

    for i in 0..nr_thins {
        let td = td[i as usize].take();
        pool.close_thin(fix, td.unwrap())?;
    }

    let histogram = pool.build_run_histogram(fix)?;
    pool.show_fragmentation(&histogram)?;
    ensure!(
        histogram.len() == 1,
        "expected a single run length in histogram"
    );
    ensure!(
        *histogram.get(&(nr_blocks as usize)).unwrap() == nr_thins as usize,
        "expected all blocks to be in a single run"
    );

    Ok(())
}

fn test_fragment_thins(fix: &mut Fixture) -> Result<()> {
    do_fragment_test(fix, create_separate_thins)
}

fn test_fragment_snapshots(fix: &mut Fixture) -> Result<()> {
    do_fragment_test(fix, create_recursive_snaps)
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![PDATA_MOD, THIN_MOD];
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
            runner.register(&p, Test::new(kmodules.clone(), Box::new($func)));
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
        test!("discard/runs", test_discard_single_thin)
        test!("discard/rolling", test_discard_rolling_snaps)
        test!("delete-frees-blocks", test_delete_frees_blocks)
        test!("fragmentation/thins", test_fragment_thins)
        test!("fragmentation/snapshots", test_fragment_snapshots)
    }

    Ok(())
}

//-------------------------------
