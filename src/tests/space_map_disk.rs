use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::space_map_disk::*;
use crate::wrappers::transaction_manager::*;

use anyhow::Result;
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

fn test_commit_cost(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_metadata_blocks = 1;
    let nr_data_blocks = 16320;
    let bm = dm_bm_create(fix, nr_metadata_blocks + 1000)?;
    let (tm, sm_meta) = dm_tm_create(fix, bm, 0)?;
    let sm_disk = dm_sm_disk_create(fix, tm, nr_data_blocks)?;
    let mut sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    let nr_blocks = sm_get_nr_blocks(fix, sm_disk)?;
    let nr_free = sm_get_nr_free(fix, sm_disk)?;
    info!("smdisk initial status: nr_blocks={}, nr_free={}", nr_blocks, nr_free);

    let nr_blocks = sm_get_nr_blocks(fix, sm_meta)?;
    let nr_free = sm_get_nr_free(fix, sm_meta)?;
    info!("sm_metadata initial status: nr_blocks={}, nr_free={}", nr_blocks, nr_free);

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

            let nr_blocks = sm_get_nr_blocks(fix, sm_disk)?;
            let nr_free = sm_get_nr_free(fix, sm_disk)?;
            info!("sm_disk nr_blocks={}, nr_free={}", nr_blocks, nr_free);

            let nr_blocks = sm_get_nr_blocks(fix, sm_meta)?;
            let nr_free = sm_get_nr_free(fix, sm_meta)?;
            info!("sm_meta nr_blocks={}, nr_free={}", nr_blocks, nr_free);

            baseline = Stats::collect_stats(fix);
        }
    }

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    runner.register("/pdata/sm-disk/commit-cost", Box::new(test_commit_cost));
    Ok(())
}

//-------------------------------
