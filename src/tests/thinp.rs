use anyhow::{anyhow, ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use nom::{number::complete::*, IResult};
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::BTreeSet;
use std::io;
use std::io::{Cursor, Read, Write};
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;
use thinp::io_engine::BLOCK_SIZE;
use thinp::pdata::btree;
use thinp::pdata::btree::*;
use thinp::pdata::btree_builder::*;
use thinp::pdata::btree_walker::*;
use thinp::pdata::unpack::*;

use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::block_device::*;
use crate::stubs::block_manager::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::btree::*;
use crate::wrappers::thinp_metadata::*;
use crate::wrappers::transaction_manager::*;

//-------------------------------

struct ThinpTest<'a> {
    fix: &'a mut Fixture,
    pmd: Addr,
}

impl<'a> ThinpTest<'a> {
    fn new(
        fix: &'a mut Fixture,
        nr_metadata_blocks: u64,
        data_block_size: u64,
        nr_data_blocks: u64,
    ) -> Result<Self> {
        let bdev_ptr = mk_block_device(&mut fix.vm.mem, 0, 8 * nr_metadata_blocks)?;
        let pmd = dm_pool_metadata_open(fix, bdev_ptr, data_block_size, true)?;

        Ok(ThinpTest { fix, pmd })
    }
}

impl<'a> Drop for ThinpTest<'a> {
    fn drop(&mut self) {
        dm_pool_metadata_close(self.fix, self.pmd).expect("dm_pool_metadata_close() failed");
    }
}

//-------------------------------

fn test_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let t = ThinpTest::new(fix, 1024, 64, 102400)?;
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
        "/thinp/",
        test!("create", test_create)
    }

    Ok(())
}

//-------------------------------
