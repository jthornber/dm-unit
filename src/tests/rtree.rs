use crate::emulator::memory::*;
use crate::fixture::*;
use crate::pdata::rtree::*;
use crate::pdata::rtree_walker::*;
use crate::stats::*;
use crate::stubs::block_manager::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::rtree::*;
use crate::wrappers::space_map::*;
use crate::wrappers::space_map_disk::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{ensure, Result};
use log::*;
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::BTreeSet;

//-------------------------------

fn calc_max_sib_entries(max_entries: usize) -> usize {
    let mut sib = max_entries / 2;
    while max_entries - sib > 8 {
        sib = (sib + max_entries) / 2;
    }
    sib
}

//-------------------------------

// Delete an empty tree.
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let bm = dm_bm_create(fix, 1024)?;
    let (tm, _sm) = dm_tm_create(fix, bm, 0)?;

    let root = dm_rtree_empty(fix, tm)?;

    // No entries, so no need for a real data_sm
    let data_sm = Addr(0);
    dm_rtree_del(fix, tm, data_sm, root)?;
    Ok(())
}

//-------------------------------

#[allow(dead_code)]
fn enable_traces(fix: &mut Fixture) -> Result<()> {
    let traces = [
        "dm_rtree_insert",
        "dm_rtree_del",
        "find_leaf_",
        "insert_into_leaf",
    ];
    for t in &traces {
        fix.trace_func(t)?;
    }
    Ok(())
}

#[allow(dead_code)]
pub struct RTreeTest<'a> {
    fix: &'a mut Fixture,
    bm: Addr,
    tm: Addr,
    metadata_sm: Addr,
    data_sm: Addr,
    root: u64,
    sb: Addr,
    baseline: Stats,
}

const SUPERBLOCK: u64 = 0;

impl<'a> RTreeTest<'a> {
    pub fn new(fix: &'a mut Fixture, nr_metadata_blocks: u64) -> Result<Self> {
        let bm = dm_bm_create(fix, nr_metadata_blocks)?;
        let (tm, metadata_sm) = dm_tm_create(fix, bm, 0)?;
        let nr_data_blocks = 1024 * 1024;
        let data_sm = dm_sm_disk_create(fix, tm, nr_data_blocks)?;

        let root = dm_rtree_empty(fix, tm)?;

        // Inc the superblock
        sm_inc_block(fix, metadata_sm, SUPERBLOCK, SUPERBLOCK + 1)?;
        let sb = dm_bm_write_lock_zero(fix, bm, SUPERBLOCK, Addr(0))?;

        let baseline = {
            let bm = get_bm(fix, bm);
            Stats::collect_stats(fix, &bm)
        };

        Ok(RTreeTest {
            fix,
            bm,
            tm,
            metadata_sm,
            data_sm,
            root,
            sb,
            baseline,
        })
    }

    /*
    fn begin(&mut self) -> Result<()> {
        if self.sb.is_some() {
            return Err(anyhow!("transaction already begun"));
        }

        self.sb = Some(dm_bm_write_lock_zero(self.fix, self.bm, 0, Addr(0))?);
        Ok(())
    }
    */

    pub fn commit(&mut self) -> Result<()> {
        dm_tm_pre_commit(self.fix, self.tm)?;
        dm_tm_commit(self.fix, self.tm, self.sb)?;
        self.sb = dm_bm_write_lock_zero(self.fix, self.bm, SUPERBLOCK, Addr(0))?;
        Ok(())
    }

    pub fn del(&mut self) -> Result<()> {
        dm_rtree_del(self.fix, self.tm, self.data_sm, self.root)
    }

    pub fn insert(&mut self, v: &Mapping) -> Result<u32> {
        sm_inc_block(
            self.fix,
            self.data_sm,
            v.data_begin,
            v.data_begin + v.len as u64,
        )
        .map_err(|e| {
            println!("cannot inc {}:{}", v.data_begin, v.len);
            e
        })?;

        let mut m = v.clone();
        m.len = 1;
        for _i in 0..v.len {
            let (r, _) =
                dm_rtree_insert(self.fix, self.tm, self.data_sm, self.root, &m).map_err(|e| {
                    println!("insert failed at {}: {:?}", m.thin_begin, e);
                    e
                })?;
            self.root = r;
            m.thin_begin += 1;
            m.data_begin += 1;
        }

        // FIXME: remove
        // self.check()?;

        // FIXME: return the nr_inserted from rtree_insert
        Ok(v.len)
    }

    fn insert_reversed(&mut self, v: &Mapping) -> Result<u32> {
        sm_inc_block(
            self.fix,
            self.data_sm,
            v.data_begin,
            v.data_begin + v.len as u64,
        )?;

        let mut m = v.clone();
        m.thin_begin += m.len as u64 - 1;
        m.data_begin += m.len as u64 - 1;
        m.len = 1;
        for _i in 0..v.len {
            let (r, _) = dm_rtree_insert(self.fix, self.tm, self.data_sm, self.root, &m)?;
            self.root = r;
            m.thin_begin -= 1;
            m.data_begin -= 1;
        }

        // FIXME: return the nr_inserted from rtree_insert
        Ok(v.len)
    }

    fn remove(&mut self, thin_begin: u64, thin_end: u64) -> Result<()> {
        let new_root = dm_rtree_remove(
            self.fix,
            self.tm,
            self.data_sm,
            self.root,
            thin_begin,
            thin_end,
        )?;
        self.root = new_root;
        Ok(())
    }

    pub fn check(&mut self) -> Result<TreeStats> {
        // Ensure everything has been written.
        self.commit()?;

        let bm = get_bm(self.fix, self.bm);
        let mut stats = TreeStats::default();
        let kr = KeyRange::new();
        rtree_check(&*bm, self.root, &kr, &mut stats)?;
        Ok(stats)
    }

    fn walk(&mut self, visitor: &mut dyn NodeVisitor) -> Result<()> {
        self.commit()?;

        let bm = get_bm(self.fix, self.bm);
        rtree_walk(&*bm, self.root, visitor)?;
        Ok(())
    }

    pub fn lookup(&mut self, thin_begin: u64) -> Result<Option<Mapping>> {
        dm_rtree_lookup(self.fix, self.tm, self.root, thin_begin)
    }

    pub fn stats_start(&mut self) {
        let bm = get_bm(self.fix, self.bm);
        self.baseline = Stats::collect_stats(self.fix, &bm);
    }

    pub fn stats_delta(&mut self) -> Result<Stats> {
        let bm = get_bm(self.fix, self.bm);
        let delta = self.baseline.delta(self.fix, &bm);
        Ok(delta)
    }

    pub fn load_internal_stats(&mut self) -> Result<(Vec<u32>, Vec<u32>)> {
        dm_tm_load_stats(self.fix, self.tm)
    }
}

impl<'a> Drop for RTreeTest<'a> {
    fn drop(&mut self) {
        dm_bm_unlock(self.fix, self.sb).expect("unlock superblock");
        dm_tm_destroy(self.fix, self.tm).expect("destroy tm");
        dm_bm_destroy(self.fix, self.bm).expect("destroy bm");
    }
}

//-------------------------

fn test_insert_single_entry(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    let result = rtree.lookup(v.thin_begin)?;
    ensure!(result == Some(v));

    Ok(())
}

fn test_insert_two_separate(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v1 = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v1)?;

    let v2 = Mapping {
        thin_begin: 1000,
        data_begin: 10000,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v2)?;

    let result = rtree.lookup(v1.thin_begin)?;
    debug!("result = {:?}, expected = {:?}", result, v1);
    ensure!(result == Some(v1));

    let result = rtree.lookup(v2.thin_begin)?;
    debug!("result = {:?}, expected = {:?}", result, v2);
    ensure!(result == Some(v2));

    rtree.del()?;
    Ok(())
}

fn test_insert_two_adjacent(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v1 = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v1)?;

    let v2 = Mapping {
        thin_begin: 100,
        data_begin: 101,
        len: 17,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v2)?;

    let result = rtree.lookup(v1.thin_begin)?;
    let expected = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: 117,
        time: 0,
    };
    ensure!(result == Some(expected));

    rtree.del()?;
    Ok(())
}

fn test_insert_two_reversed(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;

    let v1 = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let v2 = Mapping {
        thin_begin: 100,
        data_begin: 101,
        len: 17,
        time: 0,
    };

    let _nr_inserted = rtree.insert(&v2)?;
    let _nr_inserted = rtree.insert_reversed(&v1)?;

    let result = rtree.lookup(v1.thin_begin)?;
    let expected = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: 117,
        time: 0,
    };
    ensure!(result == Some(expected));

    rtree.del()?;
    Ok(())
}

fn insert_three_(
    fix: &mut Fixture,
    v1: &Mapping,
    v2: &Mapping,
    v3: &Mapping,
    expected: &Mapping,
) -> Result<()> {
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let _ = rtree.insert(v1)?;
    let _ = rtree.insert(v2)?;
    let _ = rtree.insert(v3)?;

    let result = rtree.lookup(v1.thin_begin)?;
    debug!("result = {:?}, expected = {:?}", result, expected);
    ensure!(result == Some(expected.clone()));
    rtree.del()?;
    rtree.commit()?;
    Ok(())
}

fn test_insert_three(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let v1 = Mapping {
        thin_begin: 0,
        data_begin: 1000,
        len: 100,
        time: 0,
    };
    let v2 = Mapping {
        thin_begin: 100,
        data_begin: 1100,
        len: 57,
        time: 0,
    };
    let v3 = Mapping {
        thin_begin: 157,
        data_begin: 1157,
        len: 62,
        time: 0,
    };
    let expected = Mapping {
        thin_begin: 0,
        data_begin: 1000,
        len: 100 + 57 + 62,
        time: 0,
    };

    insert_three_(fix, &v1, &v2, &v3, &expected)?;
    insert_three_(fix, &v1, &v3, &v2, &expected)?;
    insert_three_(fix, &v2, &v1, &v3, &expected)?;
    insert_three_(fix, &v2, &v3, &v1, &expected)?;
    insert_three_(fix, &v3, &v1, &v2, &expected)?;
    insert_three_(fix, &v3, &v2, &v1, &expected)?;
    Ok(())
}

// test that a mapping should be inserted to the lower-bound position
fn test_insert_tail_adjacented(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;

    // Create a tree with two or more leaves
    let mappings: Vec<Mapping> = (0..MAX_LEAF_ENTRIES + 1)
        .map(|i| Mapping {
            thin_begin: i as u64 * 2,
            data_begin: i as u64 * 2,
            len: 1,
            time: 0,
        })
        .collect();

    for v in &mappings {
        let _nr_inserted = rtree.insert(v)?;
    }

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    let last = visitor.entries[visitor.nr_entries[0] as usize - 1].clone();

    // Insert a mapping that falls between two leaves,
    // and is adjacented to the last entry of the left one.
    let v = Mapping {
        thin_begin: last.thin_begin + 1,
        data_begin: last.data_begin + 1,
        len: 1,
        time: 0,
    };
    rtree.insert(&v)?;

    rtree.check()?;

    // Ensure the last entry of the first leaf, rather than the first entry of the sibling,
    // is expanded
    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    let last_modified = visitor.entries[visitor.nr_entries[0] as usize - 1].clone();
    ensure!(last_modified.thin_begin == last.thin_begin);
    ensure!(last_modified.data_begin == last.data_begin);
    ensure!(last_modified.len == 2);

    Ok(())
}

/// Trims a mapping to a particular thin_begin and len.
fn trim_mapping(m: &Mapping, thin_begin: u64, len: u32) -> Option<Mapping> {
    if thin_begin < m.thin_begin {
        None
    } else if thin_begin + (len as u64) > m.thin_begin + (m.len as u64) {
        None
    } else {
        Some(Mapping {
            thin_begin,
            data_begin: m.data_begin + thin_begin - m.thin_begin,
            len,
            time: m.time,
        })
    }
}

fn test_insert_ascending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 20000;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: i + 1234,
            len: 1,
            time: 0,
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    // These mappings should have all been merged into several
    // large mappings.
    for i in (0..COUNT).step_by(MAPPINGS_MAX_LEN) {
        let result = rtree.lookup(i)?;
        let len = if i as u64 <= COUNT - MAPPINGS_MAX_LEN as u64 {
            MAPPINGS_MAX_LEN as u64
        } else {
            COUNT - i as u64
        };
        let expected = Mapping {
            thin_begin: i,
            data_begin: i + 1234,
            len: len as u32,
            time: 0,
        };
        debug!("result = {:?}, expected = {:?}", result, expected);
        ensure!(result == Some(expected));
    }

    rtree.del()?;
    Ok(())
}

fn test_insert_descending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 20000;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: i + 1234,
            len: 1,
            time: 0,
        })
        .collect();
    mappings.reverse();

    for v in &mappings {
        let _nr_inserted = rtree.insert(v)?;
    }

    // These mappings should have all been merged into several
    // large mappings.
    for i in (0..COUNT).rev().step_by(MAPPINGS_MAX_LEN) {
        let result = rtree.lookup(i)?;
        let len = if i < MAPPINGS_MAX_LEN as u64 {
            i as u64 + 1
        } else {
            MAPPINGS_MAX_LEN as u64
        };
        let thin_begin = i - (len - 1);
        let expected = Mapping {
            thin_begin,
            data_begin: thin_begin + 1234,
            len: len as u32,
            time: 0,
        };
        debug!("{} result = {:?}, expected = {:?}", i, result, expected);
        ensure!(result == Some(expected));
    }

    rtree.del()?;
    Ok(())
}

fn test_insert_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 200000;
    const COMMIT_INTERVAL: usize = 1000;
    let mut rtree = RTreeTest::new(fix, 2048)?;
    rtree.check()?;

    let mut dblocks: Vec<u64> = (0..COUNT).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    dblocks.shuffle(&mut rng);

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: dblocks[i as usize],
            len: 1,
            time: 0,
        })
        .collect();

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    mappings.shuffle(&mut rng);

    let mut n = 0;
    rtree.stats_start();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
        n += 1;

        if n == COMMIT_INTERVAL {
            rtree.check()?;
            n = 0;
        }
    }
    rtree.check()?;

    for m in &mappings {
        let result = rtree
            .lookup(m.thin_begin)?
            .and_then(|r| trim_mapping(&r, m.thin_begin, m.len));

        if result != Some(m.clone()) {
            debug!("lookup of {}", m.thin_begin);
            ensure!(result == Some(m.clone()));
        }
    }

    rtree.del()?;
    Ok(())
}

fn test_insert_runs(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: usize = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }
    ranges.shuffle(&mut rng);

    let mut mappings = Vec::new();
    let mut data_begin = 0u64;
    for r in ranges {
        let len = r.end - r.start;
        mappings.push(Mapping {
            thin_begin: r.start as u64,
            data_begin,
            len: len as u32,
            time: 0,
        });
        data_begin += len as u64;
    }

    // FIXME: factor out common code
    const COMMIT_INTERVAL: usize = 1000;
    let mut rtree = RTreeTest::new(fix, 1024)?;
    let mut n = 0;
    rtree.stats_start();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
        n += 1;

        if n == COMMIT_INTERVAL {
            rtree.check()?;
            n = 0;
        }
    }
    rtree.check()?;

    for m in &mappings {
        let result = rtree
            .lookup(m.thin_begin)?
            .and_then(|r| trim_mapping(&r, m.thin_begin, m.len));

        if result != Some(m.clone()) {
            debug!("lookup of {}", m.thin_begin);
            ensure!(result == Some(m.clone()));
        }
    }

    // rtree.del()?;
    Ok(())
}

fn test_insert_runs_descending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: usize = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }
    ranges.shuffle(&mut rng);

    let mut mappings = Vec::new();
    let mut data_begin = 0u64;
    for r in ranges {
        let len = r.end - r.start;
        mappings.push(Mapping {
            thin_begin: r.start as u64,
            data_begin,
            len: len as u32,
            time: 0,
        });
        data_begin += len as u64;
    }

    // FIXME: factor out common code
    let mut rtree = RTreeTest::new(fix, 1024)?;
    rtree.stats_start();

    for m in &mappings {
        let _nr_inserted = rtree.insert_reversed(m)?;
    }
    rtree.check()?;

    for m in &mappings {
        let result = rtree
            .lookup(m.thin_begin)?
            .and_then(|r| trim_mapping(&r, m.thin_begin, m.len));

        if result != Some(m.clone()) {
            debug!("lookup of {}", m.thin_begin);
            ensure!(result == Some(m.clone()));
        }
    }

    Ok(())
}

// Test randomly merging runs by filling the gaps (MERGE)
fn test_insert_with_merges(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: usize = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }

    let mut mappings = Vec::new();
    for r in ranges {
        let len = r.end - r.start;
        mappings.push(Mapping {
            thin_begin: r.start as u64,
            data_begin: r.start as u64,
            len: len as u32,
            time: 0,
        });
    }

    // FIXME: factor out common code
    let mut rtree = RTreeTest::new(fix, 1024)?;

    // insert ranges with gaps
    for m in &mappings {
        if m.len > 1 {
            let mut m = m.clone();
            m.len -= 1;
            rtree.insert(&m)?;
        }
    }
    rtree.check()?;

    // merge ranges by randomly filling up gaps
    mappings.shuffle(&mut rng);
    for m in &mappings {
        let gap = Mapping {
            thin_begin: m.thin_begin + m.len as u64 - 1,
            data_begin: m.data_begin + m.len as u64 - 1,
            len: 1,
            time: 0,
        };
        rtree.insert(&gap)?;
    }

    let tree_stats = rtree.check()?;
    ensure!(tree_stats.nr_entries >= thinp::math::div_up(KEY_COUNT, MAPPINGS_MAX_LEN) as u64);
    ensure!(tree_stats.nr_mapped_blocks == KEY_COUNT as u64);

    // This test is optional. We might end up with more than twice number of entries
    // due to the entries across the leaf boundaries won't be merged.
    ensure!(tree_stats.nr_entries <= 2 * thinp::math::div_up(KEY_COUNT, MAPPINGS_MAX_LEN) as u64);

    Ok(())
}

//-------------------------------

fn test_trim_entry_begin(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    ensure!(rtree.remove(0, 50).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 1);

    let result = rtree.lookup(50)?;
    ensure!(
        result
            == Some(Mapping {
                thin_begin: 50,
                data_begin: 41,
                len: 60,
                time: 0,
            })
    );

    Ok(())
}

fn test_trim_entry_end(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    ensure!(rtree.remove(50, 120).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 1);

    let result = rtree.lookup(50)?;
    ensure!(
        result
            == Some(Mapping {
                thin_begin: 10,
                data_begin: 1,
                len: 40,
                time: 0,
            })
    );

    Ok(())
}

fn test_remove_single_entry(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    ensure!(rtree.remove(0, 120).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 0);

    let result = rtree.lookup(10)?;
    ensure!(result.is_none());

    Ok(())
}

fn test_split_single_entry(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    ensure!(rtree.remove(50, 70).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 2);

    let result = rtree.lookup(10)?;
    ensure!(
        result
            == Some(Mapping {
                thin_begin: 10,
                data_begin: 1,
                len: 40,
                time: 0,
            })
    );

    let result = rtree.lookup(70)?;
    ensure!(
        result
            == Some(Mapping {
                thin_begin: 70,
                data_begin: 61,
                len: 40,
                time: 0,
            })
    );

    Ok(())
}

fn test_remove_range_below(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    ensure!(rtree.remove(110, 120).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 1);

    let result = rtree.lookup(v.thin_begin)?;
    ensure!(result == Some(v));

    Ok(())
}

fn test_remove_range_above(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;
    ensure!(rtree.remove(0, 10).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 1);

    let result = rtree.lookup(v.thin_begin)?;
    ensure!(result == Some(v));

    Ok(())
}

//-------------------------------

fn test_remove_leading_entries(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 25;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT);

    // remove and trim leading entries
    ensure!(rtree
        .remove(mappings[0].thin_begin, mappings[9].thin_begin + 1)
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT - 9);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(
        visitor.entries[0]
            == Mapping {
                thin_begin: mappings[9].thin_begin + 1,
                data_begin: mappings[9].data_begin + 1,
                len: mappings[9].len - 1,
                time: 0,
            }
    );
    ensure!(visitor.entries[1..] == mappings[10..]);

    Ok(())
}

fn test_remove_trailing_entries(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 25;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64);

    // remove and trim trailing entries
    let last = mappings.last().unwrap();
    ensure!(rtree
        .remove(
            mappings[15].thin_begin + 1,
            last.thin_begin + last.len as u64
        )
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64 - 9);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(visitor.entries[..14] == mappings[..14]);
    ensure!(
        visitor.entries[15]
            == Mapping {
                thin_begin: mappings[15].thin_begin,
                data_begin: mappings[15].data_begin,
                len: 1,
                time: 0,
            }
    );

    Ok(())
}

fn test_remove_middle_entries(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 100;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64);

    ensure!(rtree
        .remove(mappings[10].thin_begin + 1, mappings[14].thin_begin + 1)
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64 - 3);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(visitor.entries[..10] == mappings[..10]);
    ensure!(visitor.entries[12..] == mappings[15..]);
    ensure!(
        visitor.entries[10]
            == Mapping {
                thin_begin: mappings[10].thin_begin,
                data_begin: mappings[10].data_begin,
                len: 1,
                time: 0,
            }
    );
    ensure!(
        visitor.entries[11]
            == Mapping {
                thin_begin: mappings[14].thin_begin + 1,
                data_begin: mappings[14].data_begin + 1,
                len: mappings[14].len - 1,
                time: 0,
            }
    );

    Ok(())
}

fn test_remove_all_entries(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 25;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64);

    let last = mappings.last().unwrap();
    ensure!(rtree.remove(0, last.thin_begin + last.len as u64).is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 0);

    Ok(())
}

fn test_split_middle_entry(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 25;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..COUNT)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64);

    ensure!(rtree
        .remove(mappings[10].thin_begin + 1, mappings[10].thin_begin + 2)
        .is_ok());
    ensure!(rtree
        .remove(mappings[20].thin_begin + 1, mappings[20].thin_begin + 2)
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == COUNT as u64 + 2);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(visitor.entries[..10] == mappings[..10]);
    ensure!(visitor.entries[12..21] == mappings[11..20]);
    ensure!(visitor.entries[23..] == mappings[21..]);
    ensure!(
        visitor.entries[10]
            == Mapping {
                thin_begin: mappings[10].thin_begin,
                data_begin: mappings[10].data_begin,
                len: 1,
                time: 0,
            }
    );
    ensure!(
        visitor.entries[11]
            == Mapping {
                thin_begin: mappings[10].thin_begin + 2,
                data_begin: mappings[10].data_begin + 2,
                len: mappings[10].len - 2,
                time: 0,
            }
    );
    ensure!(
        visitor.entries[21]
            == Mapping {
                thin_begin: mappings[20].thin_begin,
                data_begin: mappings[20].data_begin,
                len: 1,
                time: 0,
            }
    );
    ensure!(
        visitor.entries[22]
            == Mapping {
                thin_begin: mappings[20].thin_begin + 2,
                data_begin: mappings[20].data_begin + 2,
                len: mappings[20].len - 2,
                time: 0,
            }
    );

    Ok(())
}

//-------------------------------

fn test_remove_leading_leaves(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = (calc_max_sib_entries(MAX_LEAF_ENTRIES) * 2 + MAX_LEAF_ENTRIES) as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 3);
    ensure!(stats.nr_entries == count as u64);

    let remove_end: usize = MAX_LEAF_ENTRIES + 100;

    ensure!(rtree
        .remove(mappings[0].thin_begin, mappings[remove_end].thin_begin + 1)
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 2);
    ensure!(stats.nr_entries == (count - remove_end as u64));

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(
        visitor.entries[0]
            == Mapping {
                thin_begin: mappings[remove_end].thin_begin + 1,
                data_begin: mappings[remove_end].data_begin + 1,
                len: mappings[remove_end].len - 1,
                time: 0,
            }
    );
    ensure!(visitor.entries[1..] == mappings[(remove_end + 1)..]);

    Ok(())
}

fn test_remove_trailing_leaves(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = (calc_max_sib_entries(MAX_LEAF_ENTRIES) * 2 + MAX_LEAF_ENTRIES) as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 3);
    ensure!(stats.nr_entries == count as u64);

    let remove_begin: usize = MAX_LEAF_ENTRIES + 100;

    // remove and trim trailing entries
    let last = mappings.last().unwrap();
    ensure!(rtree
        .remove(
            mappings[remove_begin].thin_begin + 1,
            last.thin_begin + last.len as u64
        )
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 2);
    ensure!(stats.nr_entries == remove_begin as u64 + 1);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(visitor.entries[..remove_begin] == mappings[..remove_begin]);
    ensure!(
        visitor.entries[remove_begin]
            == Mapping {
                thin_begin: mappings[remove_begin].thin_begin,
                data_begin: mappings[remove_begin].data_begin,
                len: 1,
                time: 0,
            }
    );

    Ok(())
}

fn test_remove_middle_leaves(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = (calc_max_sib_entries(MAX_LEAF_ENTRIES) * 2 + MAX_LEAF_ENTRIES) as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 3);
    ensure!(stats.nr_entries == count as u64);

    let remove_begin: usize = calc_max_sib_entries(MAX_LEAF_ENTRIES) - 100;
    let remove_end: usize = calc_max_sib_entries(MAX_LEAF_ENTRIES) * 2 + 100;
    let nr_removed: usize = remove_end - remove_begin - 1; // assume END > BEGIN

    ensure!(rtree
        .remove(
            mappings[remove_begin].thin_begin + 1,
            mappings[remove_end].thin_begin + 1
        )
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 2);
    ensure!(stats.nr_entries == (count - nr_removed as u64));

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;
    ensure!(visitor.entries[..remove_begin] == mappings[..remove_begin]);
    ensure!(visitor.entries[(remove_begin + 2)..] == mappings[(remove_end + 1)..]);
    ensure!(
        visitor.entries[remove_begin]
            == Mapping {
                thin_begin: mappings[remove_begin].thin_begin,
                data_begin: mappings[remove_begin].data_begin,
                len: 1,
                time: 0,
            }
    );
    ensure!(
        visitor.entries[remove_begin + 1]
            == Mapping {
                thin_begin: mappings[remove_end].thin_begin + 1,
                data_begin: mappings[remove_end].data_begin + 1,
                len: mappings[remove_end].len - 1,
                time: 0,
            }
    );

    Ok(())
}

fn test_remove_all_leaves(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = (calc_max_sib_entries(MAX_LEAF_ENTRIES) * 2 + MAX_LEAF_ENTRIES) as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 3);
    ensure!(stats.nr_entries == count as u64);

    let last = mappings.last().unwrap();
    ensure!(rtree
        .remove(mappings[0].thin_begin, last.thin_begin + last.len as u64)
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 0);

    Ok(())
}

// split the root into two
fn test_remove_split_root(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = MAX_LEAF_ENTRIES as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == count as u64);

    // split an entry into two, causing splitting of the leaf
    ensure!(rtree
        .remove(mappings[100].thin_begin + 1, mappings[100].thin_begin + 2)
        .is_ok());

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 2);
    ensure!(stats.nr_entries == count as u64 + 1);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;

    ensure!(visitor.entries[..100] == mappings[..100]);
    ensure!(visitor.entries[102..] == mappings[101..]);
    ensure!(
        visitor.entries[100]
            == Mapping {
                thin_begin: mappings[100].thin_begin,
                data_begin: mappings[100].data_begin,
                len: 1,
                time: 0,
            }
    );
    ensure!(
        visitor.entries[101]
            == Mapping {
                thin_begin: mappings[100].thin_begin + 2,
                data_begin: mappings[100].data_begin + 2,
                len: mappings[100].len - 2,
                time: 0,
            }
    );

    Ok(())
}

fn test_remove_split_first_leaf(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = (calc_max_sib_entries(MAX_LEAF_ENTRIES) + MAX_LEAF_ENTRIES) as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 3;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 2);
    ensure!(stats.nr_entries == count as u64);

    const RANGES_BEGIN: usize = 100;
    const RANGES_END: usize = 110;
    const NR_INSERTED: usize = RANGES_END - RANGES_BEGIN;

    // split several ranges to produce insertions
    for i in RANGES_BEGIN..RANGES_END {
        ensure!(rtree
            .remove(mappings[i].thin_begin + 1, mappings[i].thin_begin + 2)
            .is_ok());
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 3);
    ensure!(stats.nr_entries == count + NR_INSERTED as u64);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;

    ensure!(visitor.entries[..RANGES_BEGIN] == mappings[..RANGES_BEGIN]);
    ensure!(visitor.entries[RANGES_END + NR_INSERTED..] == mappings[RANGES_END..]);

    // verify splitted ranges
    for (pos, i) in (RANGES_BEGIN..RANGES_END).enumerate() {
        let idx = RANGES_BEGIN + pos * 2;
        ensure!(
            visitor.entries[idx]
                == Mapping {
                    thin_begin: mappings[i].thin_begin,
                    data_begin: mappings[i].data_begin,
                    len: 1,
                    time: 0,
                }
        );
        ensure!(
            visitor.entries[idx + 1]
                == Mapping {
                    thin_begin: mappings[i].thin_begin + 2,
                    data_begin: mappings[i].data_begin + 2,
                    len: mappings[i].len - 2,
                    time: 0,
                }
        );
    }

    Ok(())
}

fn test_remove_split_last_leaf(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count: u64 = (calc_max_sib_entries(MAX_LEAF_ENTRIES) + MAX_LEAF_ENTRIES) as u64;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut begin: u64 = 0;
    let mut len: u32 = 2;
    let mappings: Vec<Mapping> = (0..count)
        .map(|_| {
            let thin_begin = begin;
            let map_len = len;
            begin += len as u64 + 1;
            len += 1;

            Mapping {
                thin_begin,
                data_begin: thin_begin + 1234,
                len: map_len,
                time: 0,
            }
        })
        .collect();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 2);
    ensure!(stats.nr_entries == count);

    const RANGES_BEGIN: usize = 200;
    const RANGES_END: usize = 210;
    const NR_INSERTED: usize = RANGES_END - RANGES_BEGIN;

    // split several ranges to produce insertions
    for i in RANGES_BEGIN..RANGES_END {
        ensure!(rtree
            .remove(mappings[i].thin_begin + 1, mappings[i].thin_begin + 2)
            .is_ok());
    }

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 1);
    ensure!(stats.nr_leaves == 3);
    ensure!(stats.nr_entries == count + NR_INSERTED as u64);

    let mut visitor = MappingCollector::new();
    rtree.walk(&mut visitor)?;

    ensure!(visitor.entries[..RANGES_BEGIN] == mappings[..RANGES_BEGIN]);
    ensure!(visitor.entries[RANGES_END + NR_INSERTED..] == mappings[RANGES_END..]);

    // verify splitted ranges
    for (pos, i) in (RANGES_BEGIN..RANGES_END).enumerate() {
        let idx = RANGES_BEGIN + pos * 2;
        ensure!(
            visitor.entries[idx]
                == Mapping {
                    thin_begin: mappings[i].thin_begin,
                    data_begin: mappings[i].data_begin,
                    len: 1,
                    time: 0,
                }
        );
        ensure!(
            visitor.entries[idx + 1]
                == Mapping {
                    thin_begin: mappings[i].thin_begin + 2,
                    data_begin: mappings[i].data_begin + 2,
                    len: mappings[i].len - 2,
                    time: 0,
                }
        );
    }

    Ok(())
}

//-------------------------------

fn test_overwrite_entry_begin(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut rtree = RTreeTest::new(fix, 1024)?;
    let v = Mapping {
        thin_begin: 10,
        data_begin: 1,
        len: 100,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;

    let v = Mapping {
        thin_begin: 5,
        data_begin: 20,
        len: 10,
        time: 0,
    };
    let _nr_inserted = rtree.insert(&v)?;

    let stats = rtree.check()?;
    ensure!(stats.nr_internal == 0);
    ensure!(stats.nr_leaves == 1);
    ensure!(stats.nr_entries == 2);

    let result = rtree.lookup(5)?;
    ensure!(
        result
            == Some(Mapping {
                thin_begin: 5,
                data_begin: 20,
                len: 10,
                time: 0,
            })
    );

    let result = rtree.lookup(15)?;
    ensure!(
        result
            == Some(Mapping {
                thin_begin: 15,
                data_begin: 6,
                len: 95,
                time: 0,
            })
    );

    Ok(())
}

// Test TRUNCATE_FRONT, PUSH_BACK_TRUNCATED, and PUSH_BACK_REPLACED
fn test_overwrite_runs(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: usize = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }
    ranges.shuffle(&mut rng);

    let mut mappings = Vec::new();
    let mut data_begin = 0u64;
    for r in ranges {
        let len = r.end - r.start;
        mappings.push(Mapping {
            thin_begin: r.start as u64,
            data_begin,
            len: len as u32,
            time: 0,
        });
        data_begin += len as u64;
    }

    let mut rtree = RTreeTest::new(fix, 1024)?;
    rtree.stats_start();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }
    rtree.check()?;

    // overwrite the runs with modified mapped values
    for m in &mut mappings {
        m.data_begin += KEY_COUNT as u64;
        m.time = 1;
        let _nr_inserted = rtree.insert(m)?;
    }
    rtree.check()?;

    for m in &mappings {
        let result = rtree
            .lookup(m.thin_begin)?
            .and_then(|r| trim_mapping(&r, m.thin_begin, m.len));

        if result != Some(m.clone()) {
            debug!("lookup of {}", m.thin_begin);
            ensure!(result == Some(m.clone()));
        }
    }

    // rtree.del()?;
    Ok(())
}

// Test TRUNCATE_BACK, PUSH_FRONT_TRUNCATED, and PUSH_FRONT_REPLACED
fn test_overwrite_runs_descending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: usize = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }
    ranges.shuffle(&mut rng);

    let mut mappings = Vec::new();
    let mut data_begin = 0u64;
    for r in ranges {
        let len = r.end - r.start;
        mappings.push(Mapping {
            thin_begin: r.start as u64,
            data_begin,
            len: len as u32,
            time: 0,
        });
        data_begin += len as u64;
    }

    let mut rtree = RTreeTest::new(fix, 1024)?;
    rtree.stats_start();

    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
    }
    rtree.check()?;

    // overwrite the runs with modified mapped values
    for m in &mut mappings {
        m.data_begin += KEY_COUNT as u64;
        m.time = 1;
        let _nr_inserted = rtree.insert_reversed(m)?;
    }
    rtree.check()?;

    for m in &mappings {
        let result = rtree
            .lookup(m.thin_begin)?
            .and_then(|r| trim_mapping(&r, m.thin_begin, m.len));

        if result != Some(m.clone()) {
            debug!("lookup of {}", m.thin_begin);
            ensure!(result == Some(m.clone()));
        }
    }

    // rtree.del()?;
    Ok(())
}

// Test overwriting length-1 mappings (REPLACE)
fn test_overwrite_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 200000;
    const COMMIT_INTERVAL: usize = 1000;
    let mut rtree = RTreeTest::new(fix, 4096)?;
    rtree.check()?;

    let mut dblocks: Vec<u64> = (0..COUNT).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    dblocks.shuffle(&mut rng);

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: dblocks[i as usize],
            len: 1,
            time: 0,
        })
        .collect();

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    mappings.shuffle(&mut rng);

    // populate
    let mut n = 0;
    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
        n += 1;

        // commit the transaction to prevent from holding too much shadows
        if n == COMMIT_INTERVAL {
            rtree.commit()?;
            n = 0;
        }
    }
    rtree.check()?;

    // overwrite
    n = 0;
    for m in &mut mappings {
        m.data_begin += COUNT;
        m.time = 1;
        let _nr_inserted = rtree.insert(m)?;
        n += 1;

        // commit the transaction to prevent from holding too much shadows
        if n == COMMIT_INTERVAL {
            rtree.commit()?;
            n = 0;
        }
    }
    rtree.check()?;

    for m in &mappings {
        let result = rtree
            .lookup(m.thin_begin)?
            .and_then(|r| trim_mapping(&r, m.thin_begin, m.len));

        if result != Some(m.clone()) {
            debug!("lookup of {}", m.thin_begin);
            ensure!(result == Some(m.clone()));
        }
    }

    rtree.del()?;
    Ok(())
}

// Test randomly merge runs by overwriting the gaps (MERGE_REPLACED)
fn test_overwrite_with_merges(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: usize = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }

    let mut mappings = Vec::new();
    for r in ranges {
        let len = r.end - r.start;
        mappings.push(Mapping {
            thin_begin: r.start as u64,
            data_begin: r.start as u64,
            len: len as u32,
            time: 1,
        });
    }

    // FIXME: factor out common code
    let mut rtree = RTreeTest::new(fix, 1024)?;

    // insert ranges with gaps
    for m in &mappings {
        if m.len > 1 {
            let mut m2 = m.clone();
            m2.len -= 1;
            rtree.insert(&m2)?;
        }

        // the gaps have different time
        let gap = Mapping {
            thin_begin: m.thin_begin + m.len as u64 - 1,
            data_begin: m.data_begin + m.len as u64 - 1,
            len: 1,
            time: 0,
        };
        rtree.insert(&gap)?;
    }
    rtree.check()?;

    // merge ranges by randomly filling up gaps
    mappings.shuffle(&mut rng);
    for m in &mappings {
        let gap = Mapping {
            thin_begin: m.thin_begin + m.len as u64 - 1,
            data_begin: m.data_begin + m.len as u64 - 1,
            len: 1,
            time: 1,
        };
        rtree.insert(&gap)?;
    }

    let tree_stats = rtree.check()?;
    ensure!(tree_stats.nr_entries >= thinp::math::div_up(KEY_COUNT, MAPPINGS_MAX_LEN) as u64);
    ensure!(tree_stats.nr_mapped_blocks == KEY_COUNT as u64);

    // This test is optional. We might end up with more than twice number of entries
    // due to the entries across the leaf boundaries won't be merged.
    ensure!(tree_stats.nr_entries <= 2 * thinp::math::div_up(KEY_COUNT, MAPPINGS_MAX_LEN) as u64);

    Ok(())
}

// Test the SPLIT scenario
fn test_overwrite_with_splitting(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const KEY_COUNT: u64 = 200000;
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..(KEY_COUNT / 20) {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    for i in (MAPPINGS_MAX_LEN as u64..KEY_COUNT).step_by(MAPPINGS_MAX_LEN) {
        endpoints.insert(i);
    }
    let mut endpoints: Vec<u64> = endpoints.into_iter().collect();

    let mut rtree = RTreeTest::new(fix, 1024)?;

    // prepare the initial mappings
    rtree.insert(&Mapping {
        thin_begin: 0,
        data_begin: 0,
        len: KEY_COUNT as u32,
        time: 0,
    })?;
    rtree.check()?;

    // overwrite incompatible mappings to split the entries
    endpoints.shuffle(&mut rng);
    for (i, e) in endpoints.iter().enumerate() {
        let gap = Mapping {
            thin_begin: *e,
            data_begin: KEY_COUNT + i as u64,
            len: 1,
            time: 0,
        };
        rtree.insert(&gap)?;
    }
    rtree.check()?;

    // check the gaps
    for (i, e) in endpoints.iter().enumerate() {
        let result = rtree.lookup(*e)?;
        let gap = Mapping {
            thin_begin: *e,
            data_begin: KEY_COUNT + i as u64,
            len: 1,
            time: 0,
        };
        ensure!(result == Some(gap));
    }

    // check the splitted entries
    endpoints.sort();
    let mut last = 0u64;
    for e in endpoints {
        if e == last {
            last = e + 1;
            continue;
        }

        let result = rtree.lookup(last)?;
        let expected = Mapping {
            thin_begin: last,
            data_begin: last,
            len: (e - last) as u32,
            time: 0,
        };
        ensure!(result == Some(expected));

        last = e + 1;
    }

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
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
            runner.register(&p, Test::new(kmodules.clone(), Box::new($func)));
        }};
    }

    test_section! {
        "/pdata/rtree/",
        test!("del/empty", test_del_empty)
        test!("insert/single", test_insert_single_entry)
        test!("insert/two/separate", test_insert_two_separate)
        test!("insert/two/adjacent", test_insert_two_adjacent)
        test!("insert/two/reversed", test_insert_two_reversed)
        test!("insert/three", test_insert_three)
        test!("insert/tail_adjacented", test_insert_tail_adjacented)
        test!("insert/many/ascending", test_insert_ascending)
        test!("insert/many/descending", test_insert_descending)
        test!("insert/many/random", test_insert_random)
        test!("insert/many/runs", test_insert_runs)
        test!("insert/many/runs_descending", test_insert_runs_descending)
        test!("insert/many/merge", test_insert_with_merges)
        test!("remove/single/trim-begin", test_trim_entry_begin)
        test!("remove/single/trim-end", test_trim_entry_end)
        test!("remove/single/all", test_remove_single_entry)
        test!("remove/single/split", test_split_single_entry)
        test!("remove/single/below", test_remove_range_below)
        test!("remove/single/above", test_remove_range_above)
        test!("remove/multiple/leading", test_remove_leading_entries)
        test!("remove/multiple/trailing", test_remove_trailing_entries)
        test!("remove/multiple/middle", test_remove_middle_entries)
        test!("remove/multiple/all", test_remove_all_entries)
        test!("remove/multiple/split", test_split_middle_entry)
        test!("remove/leaves/leading", test_remove_leading_leaves)
        test!("remove/leaves/trailing", test_remove_trailing_leaves)
        test!("remove/leaves/middle", test_remove_middle_leaves)
        test!("remove/leaves/all", test_remove_all_leaves)
        test!("remove/leaves/split-root", test_remove_split_root)
        test!("remove/leaves/split-first", test_remove_split_first_leaf)
        test!("remove/leaves/split-last", test_remove_split_last_leaf)
        test!("overwrite/single/", test_overwrite_entry_begin)
        test!("overwrite/many/random", test_overwrite_random)
        test!("overwrite/many/runs", test_overwrite_runs)
        test!("overwrite/many/runs_descending", test_overwrite_runs_descending)
        test!("overwrite/many/merge", test_overwrite_with_merges)
        test!("overwrite/many/split", test_overwrite_with_splitting)
    };

    Ok(())
}

//-------------------------------
