use anyhow::{ensure, Result};
use log::*;
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::BTreeMap;

use crate::emulator::memory::*;
use crate::fixture::*;
use crate::stubs::block_device::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::cache_metadata::*;

//-------------------------------

#[allow(dead_code)]
struct Cache {
    nr_origin_blocks: u64,
    nr_cache_blocks: u64,
    cmd: Addr,
}

impl Cache {
    fn new(fix: &mut Fixture, nr_origin_blocks: u64, nr_cache_blocks: u64) -> Result<Self> {
        let nr_metadata_blocks = 1024;
        let bdev_ptr = mk_block_device(&mut fix.vm.mem, 0, 8 * nr_metadata_blocks)?;
        let cmd = dm_cache_metadata_open(fix, bdev_ptr, 64, true, 4, 2)?;
        dm_cache_resize(fix, cmd, nr_cache_blocks)?;
        Ok(Cache {
            nr_origin_blocks,
            nr_cache_blocks,
            cmd,
        })
    }

    // Needed to write the discard bitset
    fn shutdown(&mut self, fix: &mut Fixture) -> Result<()> {
        dm_cache_metadata_close(fix, self.cmd)
    }

    fn commit(&mut self, fix: &mut Fixture, clean_shutdown: bool) -> Result<()> {
        dm_cache_commit(fix, self.cmd, clean_shutdown)
    }

    fn insert_mapping(&mut self, fix: &mut Fixture, cblock: u64, oblock: u64) -> Result<()> {
        dm_cache_insert_mapping(fix, self.cmd, cblock, oblock)
    }

    fn remove_mapping(&mut self, fix: &mut Fixture, cblock: u64) -> Result<()> {
        dm_cache_remove_mapping(fix, self.cmd, cblock)
    }

    fn load_mappings(&mut self, fix: &mut Fixture) -> Result<Vec<CacheMapping>> {
        dm_cache_load_mappings(fix, self.cmd)
    }
}

//-------------------------------

fn test_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let mut cache = Cache::new(fix, 1024, 64)?;
    cache.shutdown(fix)?;
    Ok(())
}

//-------------------------------

fn random_mapping(nr_cblocks: u64, nr_oblocks: u64, count: u64) -> Vec<(u64, u64)> {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    let mut cblocks: Vec<u64> = (0..nr_cblocks).into_iter().collect();
    cblocks.shuffle(&mut rng);

    let mut oblocks: Vec<u64> = (0..nr_oblocks).into_iter().collect();
    oblocks.shuffle(&mut rng);

    let mut map = Vec::new();
    for i in 0..count {
        map.push((cblocks[i as usize], oblocks[i as usize]));
    }
    map
}

fn test_insert_some_mappings(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_cblocks = 1024;
    let nr_oblocks = 1024000;

    let mut cache = Cache::new(fix, nr_oblocks, nr_cblocks)?;
    let map = random_mapping(nr_cblocks, nr_oblocks, nr_cblocks / 2);

    for (cb, ob) in &map {
        debug!("{} cache -> {} origin", cb, ob);
        cache.insert_mapping(fix, *cb, *ob)?;
    }
    cache.commit(fix, true)?;

    let mappings = cache.load_mappings(fix)?;

    let mut by_cblock = BTreeMap::new();
    for m in mappings {
        ensure!(!by_cblock.contains_key(&m.cblock));
        by_cblock.insert(m.cblock, m.oblock);
    }

    for (cb, ob) in map {
        let v = by_cblock.get(&cb);
        ensure!(v.is_some());
        ensure!(v.unwrap() == &ob);
    }

    cache.shutdown(fix)?;
    Ok(())
}

fn test_remove_some_mappings(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_cblocks = 1024;
    let nr_oblocks = 1024000;

    let mut cache = Cache::new(fix, nr_oblocks, nr_cblocks)?;
    let map = random_mapping(nr_cblocks, nr_oblocks, nr_cblocks / 2);
    let mut to_remove = Vec::new();
    let mut remaining = Vec::new();

    let count = 0;
    for (cb, ob) in &map {
        debug!("{} cache -> {} origin", cb, ob);
        cache.insert_mapping(fix, *cb, *ob)?;

        if count % 2 == 0 {
            to_remove.push((*cb, *ob));
        } else {
            remaining.push((*cb, *ob));
        }
    }
    cache.commit(fix, true)?;

    // remove every other entry
    for (cb, _) in to_remove {
        cache.remove_mapping(fix, cb)?;
    }

    let mappings = cache.load_mappings(fix)?;

    let mut by_cblock = BTreeMap::new();
    for m in mappings {
        ensure!(!by_cblock.contains_key(&m.cblock));
        by_cblock.insert(m.cblock, m.oblock);
    }

    for (cb, ob) in remaining {
        let v = by_cblock.get(&cb);
        ensure!(v.is_some());
        ensure!(v.unwrap() == &ob);
    }

    cache.shutdown(fix)?;
    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![PDATA_MOD, CACHE_MOD];
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
            runner.register(&p, Test::new(kmodules.clone(), Box::new($func)));
        }};
    }

    test_section! {
        "/cache/",
        test!("create", test_create)
        test!("insert", test_insert_some_mappings)
        test!("remove", test_remove_some_mappings)
    }

    Ok(())
}

//-------------------------------
