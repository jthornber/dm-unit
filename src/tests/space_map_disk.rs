use crate::fixture::*;
use crate::emulator::memory::*;
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
}

//-------------------------------

fn test_boundary_size_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut builder = DiskSMBuilder;
    test_boundary_size(fix, &mut builder)
}

fn test_commit_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut builder = DiskSMBuilder;
    test_commit_cost(fix, &mut builder)
}

fn test_inc_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut builder = DiskSMBuilder;
    test_inc_cost(fix, &mut builder)
}

fn test_wrapping_around_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut builder = DiskSMBuilder;
    test_wrapping_around(fix, &mut builder)
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![PDATA_MOD];

    runner.register(
        "/pdata/space-map/disk/boundary-size",
        Test::new(kmodules.clone(), Box::new(test_boundary_size_)),
    );
    runner.register(
        "/pdata/space-map/disk/commit-cost",
        Test::new(kmodules.clone(), Box::new(test_commit_cost_)),
    );
    runner.register("/pdata/space-map/disk/inc-cost",
                   Test::new(kmodules.clone(), Box::new(test_inc_cost_)));
    runner.register(
        "/pdata/space-map/disk/wrapping-around",
        Test::new(kmodules, Box::new(test_wrapping_around_)),
    );
    Ok(())
}

//-------------------------------
