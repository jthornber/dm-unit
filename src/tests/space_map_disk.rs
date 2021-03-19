use crate::fixture::*;
use crate::memory::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::space_map::{self, *};
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::space_map_disk::*;
use crate::wrappers::transaction_manager::*;

use anyhow::Result;

//-------------------------------

#[allow(dead_code)]
pub struct DiskSpaceMap {
    bm: Addr,
    tm: Addr,
    sm_meta: Addr,
    sm_disk: Addr,
    sb: Addr,
}

impl DiskSpaceMap {
    fn new() -> DiskSpaceMap {
        DiskSpaceMap {bm: Addr(0), tm: Addr(0), sm_meta: Addr(0), sm_disk: Addr(0), sb: Addr(0)}
    }
}

impl space_map::SpaceMap for DiskSpaceMap {
    fn addr(&self) -> Addr {
        self.sm_disk
    }

    fn create(&mut self, fix: &mut Fixture, nr_blocks: u64) -> Result<()> {
        self.bm = dm_bm_create(fix, u64::max(nr_blocks / ENTRIES_PER_BLOCK as u64, 1000))?;
        let (tm, sm) = dm_tm_create(fix, self.bm, 0)?;
        self.tm = tm;
        self.sm_meta = sm;
        self.sm_disk = dm_sm_disk_create(fix, self.tm, nr_blocks)?;
        self.sb = dm_bm_write_lock_zero(fix, self.bm, 0, Addr(0))?;

        Ok(())
    }

    fn commit(&mut self, fix: &mut Fixture) -> Result<()> {
        sm_commit(fix, self.sm_disk)?;
        dm_tm_pre_commit(fix, self.tm)?;
        dm_tm_commit(fix, self.tm, self.sb)?;
        self.sb = dm_bm_write_lock_zero(fix, self.bm, 0, Addr(0))?;

        Ok(())
    }
}

//-------------------------------

fn test_boundary_size_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut sm = DiskSpaceMap::new();
    test_boundary_size(fix, &mut sm)
}

fn test_commit_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut sm = DiskSpaceMap::new();
    test_commit_cost(fix, &mut sm)
}

fn test_inc_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut sm = DiskSpaceMap::new();
    test_inc_cost(fix, &mut sm)
}

fn test_wrapping_around_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut sm = DiskSpaceMap::new();
    test_wrapping_around(fix, &mut sm)
}


//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    runner.register("/pdata/space-map/disk/boundary-size", Box::new(test_boundary_size_));
    runner.register("/pdata/space-map/disk/commit-cost", Box::new(test_commit_cost_));
    runner.register("/pdata/space-map/disk/inc-cost", Box::new(test_inc_cost_));
    runner.register("/pdata/space-map/disk/wrapping-around", Box::new(test_wrapping_around_));
    Ok(())
}

//-------------------------------
