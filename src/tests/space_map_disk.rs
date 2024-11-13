use crate::emulator::memory::*;
use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::space_map::{self, *};
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::space_map_disk::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{anyhow, ensure, Result};
use fixedbitset::FixedBitSet;
use rand::Rng;

//-------------------------------

#[allow(dead_code)]
struct DiskSpaceMap {
    bm: Addr,
    tm: Addr,
    sm_meta: Addr,
    sm_disk: Addr,
    sb: Addr,
}

struct DiskSMBuilder;

impl SpaceMapBuilder for DiskSMBuilder {
    fn create(&self, fix: &mut Fixture, nr_blocks: u64) -> Result<Box<dyn space_map::SpaceMap>> {
        let bm = dm_bm_create(fix, u64::max(nr_blocks / ENTRIES_PER_BLOCK as u64, 1000))?;
        let (tm, sm_meta) = dm_tm_create(fix, bm, 0)?;
        let sm_disk = dm_sm_disk_create(fix, tm, nr_blocks)?;
        let sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

        Ok(Box::new(DiskSpaceMap {
            bm,
            tm,
            sm_meta,
            sm_disk,
            sb,
        }))
    }
}

impl space_map::SpaceMap for DiskSpaceMap {
    fn addr(&self) -> Addr {
        self.sm_disk
    }

    fn get_bm(&self) -> Addr {
        self.bm
    }

    fn commit(&mut self, fix: &mut Fixture) -> Result<()> {
        sm_commit(fix, self.sm_disk)?;
        dm_tm_pre_commit(fix, self.tm)?;
        dm_tm_commit(fix, self.tm, self.sb)?;
        self.sb = dm_bm_write_lock_zero(fix, self.bm, 0, Addr(0))?;

        Ok(())
    }

    fn destroy(&mut self, fix: &mut Fixture) -> Result<()> {
        dm_bm_unlock(fix, self.sb)?;
        dm_tm_destroy(fix, self.tm)?;
        sm_destroy(fix, self.sm_meta)?;
        sm_destroy(fix, self.sm_disk)?;
        dm_bm_destroy(fix, self.bm)?;

        Ok(())
    }
}

//-------------------------------

fn test_boundary_size_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let builder = DiskSMBuilder;
    test_boundary_size(fix, &builder)
}

fn test_commit_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let builder = DiskSMBuilder;
    test_commit_cost(fix, &builder)
}

fn test_inc_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let builder = DiskSMBuilder;
    test_inc_cost(fix, &builder)
}

fn test_wrapping_around_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let builder = DiskSMBuilder;
    test_wrapping_around(fix, &builder)
}

//-------------------------------

fn increment_blocks(fix: &mut Fixture, sm: Addr, bitset: &FixedBitSet) -> Result<()> {
    for index in bitset.ones() {
        sm_inc_block(fix, sm, index as u64, (index + 1) as u64)?;
    }
    Ok(())
}

fn verify_free_runs(original_bitset: &FixedBitSet, free_runs: &[(u64, u64)]) -> Result<()> {
    let nr_blocks = original_bitset.len();
    let mut reconstructed_bitset = FixedBitSet::with_capacity(nr_blocks);
    reconstructed_bitset.set_range(.., true); // Start with all blocks allocated

    // Mark free blocks based on the free runs
    for &(start, end) in free_runs {
        for i in start..end {
            if i as usize >= nr_blocks {
                return Err(anyhow!(
                    "Free run ({}, {}) exceeds bitset size {}",
                    start,
                    end,
                    nr_blocks
                ));
            }
            reconstructed_bitset.set(i as usize, false);
        }
    }

    // Compare the reconstructed bitset with the original
    for i in 0..nr_blocks {
        if original_bitset.contains(i) != reconstructed_bitset.contains(i) {
            return Err(anyhow!(
                "Mismatch at index {}: original = {}, reconstructed = {}",
                i,
                original_bitset.contains(i),
                reconstructed_bitset.contains(i)
            ));
        }
    }

    Ok(())
}

fn test_free_runs(fix: &mut Fixture, bitset: &FixedBitSet) -> Result<()> {
    let nr_blocks = bitset.len() as u64;
    let builder = DiskSMBuilder;
    let mut sm = builder.create(fix, nr_blocks)?;

    // Increment blocks based on the bitset
    increment_blocks(fix, sm.addr(), bitset)?;

    sm.commit(fix)?;

    // Use sm_next_free_run to find all free runs
    let mut free_runs = Vec::new();
    let mut begin = 0;
    while begin < nr_blocks {
        match sm_next_free_run(fix, sm.addr(), begin, nr_blocks)? {
            Some((run_begin, run_end)) => {
                if run_begin >= nr_blocks {
                    break;
                }
                free_runs.push((run_begin, run_end));
                begin = run_end;
            }
            None => break, // No more free runs found
        }
    }

    sm.destroy(fix)?;

    // Verify the free runs
    verify_free_runs(bitset, &free_runs)?;

    Ok(())
}

fn test_all_free(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bitset = FixedBitSet::with_capacity(100);
    test_free_runs(fix, &bitset)
}

fn test_all_allocated(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(100);
    bitset.set_range(.., true);
    test_free_runs(fix, &bitset)
}

fn test_alternating(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(100);
    for i in (0..100).step_by(2) {
        bitset.put(i);
    }
    test_free_runs(fix, &bitset)
}

fn test_large_all_free(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bitset = FixedBitSet::with_capacity(1_000_000);
    test_free_runs(fix, &bitset)
}

fn test_large_all_allocated(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(1_000_000);
    bitset.set_range(.., true);
    test_free_runs(fix, &bitset)
}

fn test_large_alternating(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(1_000_000);
    for i in (0..1_000_000).step_by(2) {
        bitset.put(i);
    }
    test_free_runs(fix, &bitset)
}

fn test_large_sparse_allocated(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(1_000_000);
    for i in (0..1_000_000).step_by(10000) {
        bitset.put(i);
    }
    test_free_runs(fix, &bitset)
}

fn test_large_sparse_free(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(1_000_000);
    bitset.set_range(.., true);
    for i in (0..1_000_000).step_by(10000) {
        bitset.set(i, false);
    }
    test_free_runs(fix, &bitset)
}

fn test_large_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut bitset = FixedBitSet::with_capacity(1_000_000);
    let mut rng = rand::thread_rng();
    for i in 0..1_000_000 {
        if rng.gen::<bool>() {
            bitset.put(i);
        }
    }
    test_free_runs(fix, &bitset)
}

//-------------------------------

pub fn test_nr_free_all(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let builder = DiskSMBuilder;
    let nr_blocks = 10 * 1024;

    let mut sm = builder.create(fix, nr_blocks)?;
    sm.commit(fix)?;

    ensure!(sm_get_nr_free(fix, sm.addr())? == nr_blocks);

    sm.destroy(fix)?;
    Ok(())
}

pub fn test_nr_free_none(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let builder = DiskSMBuilder;
    let nr_blocks = 10 * 1024;

    let mut sm = builder.create(fix, nr_blocks)?;

    sm_inc_block(fix, sm.addr(), 0, nr_blocks)?;

    sm.commit(fix)?;

    ensure!(sm_get_nr_free(fix, sm.addr())? == 0);

    sm.destroy(fix)?;
    Ok(())
}

pub fn test_nr_free_across_transactions(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let builder = DiskSMBuilder;
    let nr_blocks = 10 * 1024;

    let mut sm = builder.create(fix, nr_blocks)?;

    // Allocate half the blocks in the current transaction
    sm_inc_block(fix, sm.addr(), 0, nr_blocks / 2)?;

    // Commit the transaction
    sm.commit(fix)?;

    // half the blocks should be free
    ensure!(sm_get_nr_free(fix, sm.addr())? == nr_blocks / 2);

    sm_dec_block(fix, sm.addr(), 0, nr_blocks / 2)?;

    // The blocks will be reported as free, but they won't really be available
    // until after the next commit.
    ensure!(sm_get_nr_free(fix, sm.addr())? == nr_blocks);

    sm.commit(fix)?;

    // All should still be free after the commit
    ensure!(sm_get_nr_free(fix, sm.addr())? == nr_blocks);

    sm.destroy(fix)?;
    Ok(())
}

//-------------------------------

pub fn register_tests(tests: &mut TestSet) -> Result<()> {
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
        "/pdata/space-map/disk/",
        test!("boundary-size", test_boundary_size_)
        test!("commit-cost", test_commit_cost_)
        test!("inc-cost", test_inc_cost_)
        test!("wrapping-around", test_wrapping_around_)
    };

    test_section! {
        "/pdata/space-map/disk/free-runs/small/",
        test!("all-free", test_all_free)
        test!("all-allocated", test_all_allocated)
        test!("alternating", test_alternating)
    };

    test_section! {
        "/pdata/space-map/disk/free-runs/large/",
        test!("all-free", test_large_all_free)
        test!("all_allocated", test_large_all_allocated)
        test!("alternating", test_large_alternating)
        test!("sparse-allocated", test_large_sparse_allocated)
        test!("sparse-free", test_large_sparse_free)
        test!("sparse-random", test_large_random)
    };

    test_section! {
        "/pdata/space-map/disk/nr-free/",
        test!("all", test_nr_free_all)
        test!("none", test_nr_free_none)
        test!("across-transactions", test_nr_free_across_transactions)
    }

    Ok(())
}

//-------------------------------
