use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::space_map_disk::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{ensure, Result};
use log::*;

//-------------------------------

fn stats_report(fix: &Fixture, baseline: &Stats, desc: &str, count: u64) {
    let delta = baseline.delta(fix);
    info!(
        "{}: instrs = {}, read_locks = {:.1}, write_locks = {:.1}",
        desc,
        delta.instrs / count,
        delta.read_locks as f64 / count as f64,
        delta.write_locks as f64 / count as f64
    );
}

fn test_boundary_size(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_data_blocks = ENTRIES_PER_BLOCK as u64;
    let bm = dm_bm_create(fix, 1000)?;
    let (tm, sm_meta) = dm_tm_create(fix, bm, 0)?;
    let sm_disk = dm_sm_disk_create(fix, tm, nr_data_blocks)?;
    let sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    ensure!(nr_data_blocks == sm_get_nr_blocks(fix, sm_disk)?);
    ensure!(nr_data_blocks == sm_get_nr_free(fix, sm_disk)?);
    let nr_meta_free = sm_get_nr_free(fix, sm_meta)?;

    for _ in 0..nr_data_blocks {
        let _b = sm_new_block(fix, sm_disk)?;
    }

    sm_commit(fix, sm_disk)?;
    dm_tm_pre_commit(fix, tm)?;
    dm_tm_commit(fix, tm, sb)?;
    dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    ensure!(nr_data_blocks == sm_get_nr_blocks(fix, sm_disk)?);
    ensure!(0 == sm_get_nr_free(fix, sm_disk)?);
    ensure!(nr_meta_free == sm_get_nr_free(fix, sm_meta)?);

    Ok(())
}

fn test_commit_cost(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_data_blocks = 20000;
    let bm = dm_bm_create(fix, 1000)?;
    let (tm, _sm_meta) = dm_tm_create(fix, bm, 0)?;
    let sm_disk = dm_sm_disk_create(fix, tm, nr_data_blocks)?;
    let mut sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    let commit_interval = 1000;

    let mut baseline = Stats::collect_stats(fix);
    let mut commit_count = commit_interval;
    for _ in 0..nr_data_blocks {
        let _b = sm_new_block(fix, sm_disk)?;
        if commit_count == commit_interval {
            // This was the first new_block after the commmit
            stats_report(fix, &baseline, "new_block", 1);
        }

        commit_count -= 1;

        if commit_count == 0 {
            sm_commit(fix, sm_disk)?;
            dm_tm_pre_commit(fix, tm)?;
            dm_tm_commit(fix, tm, sb)?;
            sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;
            commit_count = commit_interval;
            baseline = Stats::collect_stats(fix);
        }
    }

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    runner.register("/pdata/sm-disk/boundary-size", Box::new(test_boundary_size));
    runner.register("/pdata/sm-disk/commit-cost", Box::new(test_commit_cost));
    Ok(())
}

//-------------------------------
