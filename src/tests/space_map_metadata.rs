use crate::emulator::memory::*;
use crate::fixture::*;
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

struct MetadataSMBuilder;

impl SpaceMapBuilder for MetadataSMBuilder {
    fn create(&self, fix: &mut Fixture, nr_blocks: u64) -> Result<Box<dyn space_map::SpaceMap>> {
        let bm = dm_bm_create(fix, nr_blocks)?;
        let (tm, sm) = dm_tm_create(fix, bm, 0)?;
        let tm = tm;
        let sm = sm;
        let sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

        Ok(Box::new(MetadataSpaceMap { bm, tm, sm, sb }))
    }
}

impl space_map::SpaceMap for MetadataSpaceMap {
    fn addr(&self) -> Addr {
        self.sm
    }

    fn get_bm(&self) -> Addr {
        self.bm
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

    let mut builder = MetadataSMBuilder;
    test_boundary_size(fix, &mut builder)
}

fn test_commit_cost_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut builder = MetadataSMBuilder;
    test_commit_cost(fix, &mut builder)
}

fn test_wrapping_around_(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut builder = MetadataSMBuilder;
    test_wrapping_around(fix, &mut builder)
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
        "/pdata/space-map/metadata/",
        test!("boundary-size", test_boundary_size_)
        test!("commit-cost", test_commit_cost_)
        test!("wrapping-around", test_wrapping_around_)
    };

    Ok(())
}

//-------------------------------
