use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::wrappers::space_map::*;

use anyhow::{anyhow, ensure, Result};
use log::*;
use std::collections::VecDeque;


//-------------------------------

fn stats_report(stats: &Stats, desc: &str, count: u64) {
    info!(
        "{}: instrs = {}, read_locks = {:.1}, write_locks = {:.1}",
        desc,
        stats.instrs / count,
        stats.read_locks as f64 / count as f64,
        stats.write_locks as f64 / count as f64
    );
}

fn stats_compare(stats1: &Stats, stats2: &Stats, error_rate: f64) -> Result<()> {
    let max = u64::max(stats1.instrs, stats2.instrs);
    let min = u64::min(stats1.instrs, stats2.instrs);
    let e = (max - min) as f64 / max as f64;
    ensure!(e < error_rate);
    Ok(())
}

fn alloc_blocks(
    fix: &mut Fixture,
    sm: Addr,
    nr_blocks: u64,
    commit_begin: u64,
    mut alloc_begin: u64,
    allocated: &mut VecDeque<(u64, u64)>,
) -> Result<u64> {
    let sm_nr_blocks = sm_get_nr_blocks(fix, sm)?;

    let mut end: u64 = 0;
    if let Some(last) = allocated.back() {
        end = last.1;
    }

    for _ in 0..nr_blocks {
        let b = sm_new_block(fix, sm)?;

        // verify the allocated position
        if alloc_begin >= commit_begin {
            // Wrapping around might happen if all the blocks behind the alloc_begin
            // were occupied by shadowing.
            ensure!(b >= alloc_begin || b < commit_begin);
        } else {
            // Ensure there's no more wrapping around within this transaction,
            // if it has happened.
            ensure!(b >= alloc_begin && b < commit_begin);
        }

        // keep track of allocated blocks
        if b == end {
            end += 1;
        } else {
            if let Some(last) = allocated.back_mut() {
                last.1 = end;
            } else if end > 0 {
                allocated.push_back((0, end));
            }

            allocated.push_back((b, b + 1));
            end = b + 1;
        }

        if b == sm_nr_blocks - 1 {
            alloc_begin = 0;
        } else {
            alloc_begin = b + 1;
        }
    }

    if end > 0 {
        if let Some(last) = allocated.back_mut() {
            last.1 = end;
        } else {
            allocated.push_back((0, end));
        }
    }

    Ok(alloc_begin)
}

fn free_blocks(
    fix: &mut Fixture,
    sm: Addr,
    mut nr_blocks: u64,
    allocated: &mut VecDeque<(u64, u64)>,
) -> Result<()> {
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
        return Err(anyhow!(
            "insufficient number of blocks: {} more required",
            nr_blocks
        ));
    }

    Ok(())
}

//-------------------------------

pub trait SpaceMap {
    fn addr(&self) -> Addr;
    fn create(&mut self, fix: &mut Fixture, nr_blocks: u64) -> Result<()>;
    fn commit(&mut self, fix: &mut Fixture) -> Result<()>;
}

//-------------------------------

pub fn test_boundary_size(fix: &mut Fixture, sm: &mut dyn SpaceMap) -> Result<()> {
    let nr_blocks = ENTRIES_PER_BLOCK as u64;
    sm.create(fix, nr_blocks)?;
    ensure!(nr_blocks == sm_get_nr_blocks(fix, sm.addr())?);

    let nr_free = sm_get_nr_free(fix, sm.addr())?;
    for _ in 0..nr_free {
        let _b = sm_new_block(fix, sm.addr())?;
    }

    sm.commit(fix)?;
    ensure!(nr_blocks == sm_get_nr_blocks(fix, sm.addr())?);
    ensure!(0 == sm_get_nr_free(fix, sm.addr())?);

    Ok(())
}

pub fn test_commit_cost(fix: &mut Fixture, sm: &mut dyn SpaceMap) -> Result<()> {
    let count = 20000;
    sm.create(fix, count + 1000)?;
    sm.commit(fix)?;

    let commit_interval = 1000;

    let mut tracker = CostTracker::new("new-block.csv")?;
    let mut baseline = Stats::collect_stats(fix);
    let mut stats = Vec::<Stats>::new();
    let mut commit_count = commit_interval;
    for _ in 0..count {
        tracker.begin(fix);
        let _b = sm_new_block(fix, sm.addr())?;
        tracker.end(fix)?;
        if commit_count == commit_interval {
            // This was the first new_block after the commmit
            let delta = baseline.delta(fix);
            stats_report(&delta, "new_block", 1);
            stats.push(delta);
        }

        commit_count -= 1;

        if commit_count == 0 {
            sm.commit(fix)?;
            commit_count = commit_interval;
            baseline = Stats::collect_stats(fix);
        }
    }

    // verify performance errors
    stats_compare(stats.first().unwrap(), stats.last().unwrap(), 0.01)?;

    Ok(())
}

pub fn test_inc_cost(fix: &mut Fixture, sm: &mut dyn SpaceMap) -> Result<()> {
    let count = 100;
    sm.create(fix, 1024)?;
    sm.commit(fix)?;

    let mut tracker = CostTracker::new("inc.csv")?;
    for _ in 0..10 {
        for b in 0..count {
            tracker.begin(fix);
            sm_inc_block(fix, sm.addr(), b)?;
            tracker.end(fix)?;
        }
        sm.commit(fix)?;
    }

    Ok(())
}

pub fn test_wrapping_around(fix: &mut Fixture, sm: &mut dyn SpaceMap) -> Result<()> {
    sm.create(fix, (ENTRIES_PER_BLOCK * 2) as u64)?;

    let batch_size = 1000;
    let mut commit_begin = 0;
    let mut alloc_begin = 0;
    let mut allocated = VecDeque::<(u64, u64)>::new();

    // Test wrapping around by continuously allocating blocks.
    // Also do allocate and free interleavedly, to verify that the search position
    // won't be changed by any free operations.
    for _ in 0..20 {
        info!("alloc_begin={}", alloc_begin);
        alloc_begin = alloc_blocks(
            fix,
            sm.addr(),
            batch_size,
            commit_begin,
            alloc_begin,
            &mut allocated,
        )?;
        free_blocks(fix, sm.addr(), batch_size, &mut allocated)?;
        alloc_begin = alloc_blocks(
            fix,
            sm.addr(),
            batch_size,
            commit_begin,
            alloc_begin,
            &mut allocated,
        )?;
        free_blocks(fix, sm.addr(), batch_size, &mut allocated)?;

        sm.commit(fix)?;
        commit_begin = alloc_begin;
    }

    Ok(())
}

//-------------------------------
