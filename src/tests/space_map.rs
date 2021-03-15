use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{anyhow, ensure, Result};
use log::*;
use std::collections::VecDeque;

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

fn alloc_blocks(fix: &mut Fixture, sm: Addr, nr_blocks: u64,
                commit_begin: u64, mut alloc_begin: u64,
                allocated: &mut VecDeque<(u64, u64)>) -> Result<u64> {
    let sm_nr_blocks = sm_get_nr_blocks(fix, sm)?;

    for _ in 0..nr_blocks {
        let b = sm_new_block(fix, sm)?;

        if alloc_begin >= commit_begin {
            // Wrapping around might happen if all the blocks behind the alloc_begin
            // were occupied by shadowing.
            ensure!(b >= alloc_begin || b < commit_begin);
        } else {
            // Ensure there's no more wrapping around within this transaction,
            // if it has happened.
            ensure!(b >= alloc_begin && b < commit_begin);
        }

        if let Some(last) = allocated.back_mut() {
            if b == last.1 {
                last.1 += 1;
            } else {
                allocated.push_back((b, b + 1));
            }
        } else {
            allocated.push_back((b, b + 1));
        }

        if b == sm_nr_blocks - 1 {
            alloc_begin = 0;
        } else {
            alloc_begin = b + 1;
        }
    }

    Ok(alloc_begin)
}

fn free_blocks(fix: &mut Fixture, sm: Addr, mut nr_blocks: u64,
               allocated: &mut VecDeque<(u64, u64)>) -> Result<()> {
    while nr_blocks > 0 {
        if let Some(range) = allocated.front() {
            let end = u64::min(range.1, range.0 + nr_blocks);

            for b in range.0..end {
                sm_dec_block(fix, sm, b)?;
            }

            let nr_freed = end - range.0;

            if end == range.1 {
                allocated.pop_front();
            } else {
                allocated.front_mut().unwrap().0 = end;
            }

            nr_blocks -= nr_freed;
        } else {
            break;
        }
    }

    if nr_blocks > 0 {
        return Err(anyhow!("insufficient number of blocks: {} more required", nr_blocks))
    }

    Ok(())
}

//-------------------------------

fn test_boundary_size(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_meta_blocks = ENTRIES_PER_BLOCK as u64;
    let bm = dm_bm_create(fix, nr_meta_blocks)?;
    let (tm, sm_meta) = dm_tm_create(fix, bm, 0)?;
    let sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    ensure!(nr_meta_blocks == sm_get_nr_blocks(fix, sm_meta)?);

    let nr_free = sm_get_nr_free(fix, sm_meta)?;
    for _ in 0..nr_free {
        let _b = sm_new_block(fix, sm_meta)?;
    }

    dm_tm_pre_commit(fix, tm)?;
    dm_tm_commit(fix, tm, sb)?;
    dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    ensure!(nr_meta_blocks == sm_get_nr_blocks(fix, sm_meta)?);
    ensure!(0 == sm_get_nr_free(fix, sm_meta)?);

    Ok(())
}

fn test_commit_cost(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count = 10000;
    let bm = dm_bm_create(fix, count + 1000)?;
    let (tm, sm) = dm_tm_create(fix, bm, 0)?;
    let mut sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    let commit_interval = 1000;

    let mut baseline = Stats::collect_stats(fix);
    let mut commit_count = commit_interval;
    for _ in 0..count {
        let _b = sm_new_block(fix, sm)?;
        if commit_count == commit_interval {
            // This was the first new_block after the commmit
            stats_report(fix, &baseline, "new_block", 1);
        }

        commit_count -= 1;

        if commit_count == 0 {
            dm_tm_pre_commit(fix, tm)?;
            dm_tm_commit(fix, tm, sb)?;
            sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;
            commit_count = commit_interval;
            baseline = Stats::collect_stats(fix);
        }
    }

    Ok(())
}

fn test_wrapping_around(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let bm = dm_bm_create(fix, (ENTRIES_PER_BLOCK * 2) as u64)?;
    let (tm, sm) = dm_tm_create(fix, bm, 0)?;
    let mut sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    let batch_size = 1000;
    let mut commit_begin = 0;
    let mut alloc_begin = 0;
    let mut allocated = VecDeque::<(u64, u64)>::new();

    // Test wrapping around by continuously allocating blocks.
    // Also do allocate and free interleavedly, to verify that the search position
    // won't be changed by any free operations.
    for _ in 0..20 {
        info!("alloc_begin={}", alloc_begin);
        alloc_begin = alloc_blocks(fix, sm, batch_size, commit_begin, alloc_begin, &mut allocated)?;
        free_blocks(fix, sm, batch_size, &mut allocated)?;
        alloc_begin = alloc_blocks(fix, sm, batch_size, commit_begin, alloc_begin, &mut allocated)?;
        free_blocks(fix, sm, batch_size, &mut allocated)?;

        dm_tm_pre_commit(fix, tm)?;
        dm_tm_commit(fix, tm, sb)?;
        sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;
        commit_begin = alloc_begin;
    }

    Ok(())
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
        "/pdata/space-map/",
        test!("boundary-size", test_boundary_size)
        test!("commit-cost", test_commit_cost)
        test!("wrapping-around", test_wrapping_around)
    };

    Ok(())
}

//-------------------------------
