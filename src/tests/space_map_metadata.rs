use crate::fixture::*;
use crate::memory::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::space_map::{self, *};
use crate::wrappers::block_manager::*;
use crate::wrappers::transaction_manager::*;

use anyhow::Result;

//-------------------------------

struct MetadataSpaceMap {
    bm: Addr,
    tm: Addr,
    sm: Addr,
    sb: Addr,
}

impl MetadataSpaceMap {
    fn new() -> MetadataSpaceMap {
        MetadataSpaceMap {bm: Addr(0), tm: Addr(0), sm: Addr(0), sb: Addr(0)}
    }
}

impl space_map::SpaceMap for MetadataSpaceMap {
    fn addr(&self) -> Addr {
        self.sm
    }

    fn create(&mut self, fix: &mut Fixture, nr_blocks: u64) -> Result<()> {
        self.bm = dm_bm_create(fix, nr_blocks)?;
        let (tm, sm) = dm_tm_create(fix, self.bm, 0)?;
        self.tm = tm;
        self.sm = sm;
        self.sb = dm_bm_write_lock_zero(fix, self.bm, 0, Addr(0))?;

        Ok(())
    }

    fn commit(&mut self, fix: &mut Fixture) -> Result<()> {
        dm_tm_pre_commit(fix, self.tm)?;
        dm_tm_commit(fix, self.tm, self.sb)?;
        self.sb = dm_bm_write_lock_zero(fix, self.bm, 0, Addr(0))?;

        Ok(())
    }
}

//-------------------------------

fn test_boundary_size_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut sm = MetadataSpaceMap::new();
    test_boundary_size(fix, &mut sm)
}

fn test_commit_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut sm = MetadataSpaceMap::new();
    test_commit_cost(fix, &mut sm)
}

fn test_wrapping_around_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut sm = MetadataSpaceMap::new();
    test_wrapping_around(fix, &mut sm)
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
        "/pdata/space-map/metadata/",
        test!("boundary-size", test_boundary_size_)
        test!("commit-cost", test_commit_cost_)
        test!("wrapping-around", test_wrapping_around_)
    };

    Ok(())
}

//-------------------------------
