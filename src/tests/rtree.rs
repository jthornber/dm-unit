use crate::emulator::memory::*;
use crate::fixture::*;
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
use nom::{number::complete::*, IResult};
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::BTreeSet;
use std::fs::File;
use std::io::prelude::*;
use thinp::io_engine::{IoEngine, BLOCK_SIZE};
use thinp::pdata::unpack::Unpack;

//-------------------------------

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
struct Header {
    pub block: u64,
    pub is_leaf: bool,
    pub node_end: u64,
    pub nr_entries: u32,
}

const MAX_LEAF_ENTRIES: usize = (BLOCK_SIZE - 32) / (8 + 16);
const MAX_INTERNAL_ENTRIES: usize = (BLOCK_SIZE - 32) / 16;

#[allow(dead_code)]
const INTERNAL_NODE: u32 = 1;
const LEAF_NODE: u32 = 2;

impl Unpack for Header {
    fn disk_size() -> u32 {
        32
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Header> {
        let (i, _csum) = le_u32(data)?;
        let (i, flags) = le_u32(i)?;
        let (i, block) = le_u64(i)?;
        let (i, node_end) = le_u64(i)?;
        let (i, nr_entries) = le_u32(i)?;
        let (i, _padding) = le_u32(i)?;

        Ok((
            i,
            Header {
                block,
                is_leaf: flags == LEAF_NODE,
                node_end,
                nr_entries,
            },
        ))
    }
}

enum Node {
    Internal {
        header: Header,
        entries: Vec<(u64, u64)>,
    },
    Leaf {
        header: Header,
        entries: Vec<Mapping>,
    },
}

struct DiskMapping {
    data_begin: u64,
    len: u32,
    time: u32,
}

fn disk_mapping(data: &[u8]) -> IResult<&[u8], DiskMapping> {
    let (i, data_begin) = le_u64(data)?;
    let (i, len) = le_u32(i)?;
    let (i, time) = le_u32(i)?;

    Ok((
        i,
        DiskMapping {
            data_begin,
            len,
            time,
        },
    ))
}

impl Unpack for Node {
    fn disk_size() -> u32 {
        BLOCK_SIZE as u32
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Node> {
        use nom::multi::count;

        let (i, header) = Header::unpack(data)?;
        if header.is_leaf {
            let (i, keys) = count(le_u64, header.nr_entries as usize)(i)?;
            let (i, _unused_keys) =
                count(le_u64, MAX_LEAF_ENTRIES - header.nr_entries as usize)(i)?;
            let (i, values) = count(disk_mapping, header.nr_entries as usize)(i)?;

            let entries = keys
                .iter()
                .zip(values)
                .map(|(thin_begin, dm)| Mapping {
                    thin_begin: *thin_begin,
                    data_begin: dm.data_begin,
                    len: dm.len,
                    time: dm.time,
                })
                .collect();
            Ok((i, Node::Leaf { header, entries }))
        } else {
            let (i, keys) = count(le_u64, header.nr_entries as usize)(i)?;
            let (i, _unused_keys) =
                count(le_u64, MAX_INTERNAL_ENTRIES - header.nr_entries as usize)(i)?;
            let (i, values) = count(le_u64, header.nr_entries as usize)(i)?;
            Ok((
                i,
                Node::Internal {
                    header,
                    entries: keys.iter().copied().zip(values).collect(),
                },
            ))
        }
    }
}

#[derive(Debug)]
#[derive(Default)]
struct TreeStats {
    nr_internal: u64,
    nr_leaves: u64,
    nr_entries: u64,
}



fn rtree_check(
    engine: &dyn IoEngine,
    root: u64,
    mut lowest_key: u64,
    stats: &mut TreeStats,
) -> Result<()> {
    let b = engine.read(root)?;
    let data = b.get_data();
    let (_, node) = Node::unpack(data)?;

    match node {
        Node::Internal { header, entries } => {
            stats.nr_internal += 1;
            ensure!(header.block == root);
            for (key, val) in entries {
                ensure!(key >= lowest_key);
                ensure!(val != 0);
                lowest_key = key;
                rtree_check(engine, val, lowest_key, stats)?;
            }
        }
        Node::Leaf { header, entries } => {
            stats.nr_leaves += 1;
            stats.nr_entries += entries.len() as u64;
            ensure!(header.block == root);
            for m in entries {
                ensure!(m.thin_begin >= lowest_key);
                lowest_key = m.thin_begin;
            }
        }
    }

    Ok(())
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
struct RTreeTest<'a> {
    fix: &'a mut Fixture,
    bm: Addr,
    tm: Addr,
    metadata_sm: Addr,
    data_sm: Addr,
    root: u64,
    sb: Addr,
}

const SUPERBLOCK: u64 = 0;

impl<'a> RTreeTest<'a> {
    fn new(fix: &'a mut Fixture, nr_metadata_blocks: u64) -> Result<Self> {
        let bm = dm_bm_create(fix, nr_metadata_blocks)?;
        let (tm, metadata_sm) = dm_tm_create(fix, bm, 0)?;
        let nr_data_blocks = 1024 * 1024;
        let data_sm = dm_sm_disk_create(fix, tm, nr_data_blocks)?;

        let root = dm_rtree_empty(fix, tm)?;

        // Inc the superblock
        sm_inc_block(fix, metadata_sm, SUPERBLOCK, SUPERBLOCK + 1)?;
        let sb = dm_bm_write_lock_zero(fix, bm, SUPERBLOCK, Addr(0))?;

        Ok(RTreeTest {
            fix,
            bm,
            tm,
            metadata_sm,
            data_sm,
            root,
            sb,
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

    fn commit(&mut self) -> Result<()> {
        dm_tm_pre_commit(self.fix, self.tm)?;
        dm_tm_commit(self.fix, self.tm, self.sb)?;
        self.sb = dm_bm_write_lock_zero(self.fix, self.bm, SUPERBLOCK, Addr(0))?;
        Ok(())
    }

    fn del(&mut self) -> Result<()> {
        dm_rtree_del(self.fix, self.tm, self.data_sm, self.root)
    }

    fn insert(&mut self, v: &Mapping) -> Result<u32> {
        /*
        sm_inc_block(
            self.fix,
            self.data_sm,
            v.data_begin,
            v.data_begin + v.len as u64,
        )?;
        */
        let (new_root, nr_inserted) =
            dm_rtree_insert(self.fix, self.tm, self.data_sm, self.root, v)?;
        self.root = new_root;

        // FIXME: remove
        // self.check()?;

        Ok(nr_inserted)
    }

    fn check(&mut self) -> Result<TreeStats> {
        // Ensure everything has been written.
        self.commit()?;

        let bm = get_bm(self.fix, self.bm);
        let mut stats = TreeStats::default();
        rtree_check(&*bm, self.root, 0, &mut stats)?;
        debug!("{:?}", stats);
        Ok(stats)
    }

    fn lookup(&mut self, thin_begin: u64) -> Result<Option<Mapping>> {
        dm_rtree_lookup(self.fix, self.tm, self.root, thin_begin)
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
    let _nr_inserted = rtree.insert(&v1)?;

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

/// Trims a mapping to a particular thin_begin and len.
fn trim_mapping(m: &Mapping, thin_begin: u64, len: u32) -> Option<Mapping> {
    if thin_begin + (len as u64) < m.thin_begin {
        None
    } else if thin_begin >= m.thin_begin + (m.len as u64) {
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
        .into_iter()
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

    // These mappings should have all been merged into a single
    // large mapping.
    let result = rtree.lookup(0)?;
    let expected = Mapping {
        thin_begin: 0,
        data_begin: 1234,
        len: COUNT as u32,
        time: 0,
    };
    debug!("result = {:?}, expected = {:?}", result, expected);
    ensure!(result == Some(expected));

    rtree.del()?;
    Ok(())
}

fn test_insert_descending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 20000;
    let mut rtree = RTreeTest::new(fix, 1024)?;

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .into_iter()
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: i + 1,
            len: 1,
            time: 0,
        })
        .collect();
    mappings.reverse();

    for v in &mappings {
        let _nr_inserted = rtree.insert(v)?;
    }

    let result = rtree.lookup(0)?;
    let expected = Mapping {
        thin_begin: 0,
        data_begin: 1,
        len: COUNT as u32,
        time: 0,
    };
    debug!("result = {:?}, expected = {:?}", result, expected);
    ensure!(result == Some(expected));

    rtree.del()?;
    Ok(())
}

fn test_insert_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    const COUNT: u64 = 200000;
    const COMMIT_INTERVAL: usize = 1000;
    let mut rtree = RTreeTest::new(fix, 1024)?;
    rtree.check()?;

    let mut mappings: Vec<Mapping> = (0..COUNT)
        .into_iter()
        .map(|i| Mapping {
            thin_begin: i,
            data_begin: i + 1234,
            len: 1,
            time: 0,
        })
        .collect();

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    mappings.shuffle(&mut rng);

    let mut n = 0;
    let mut total = 0;
    let mut csv = File::create("./rtree.csv")?;
    writeln!(csv, "inserts, nr_internal, nr_leaves, nr_entries")?;
    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
        n += 1;

        if n == COMMIT_INTERVAL {
            let stats = rtree.check()?;
            total += n;
            writeln!(
                csv,
                "{}, {}, {}, {}",
                total, stats.nr_internal, stats.nr_leaves, stats.nr_entries
            )?;
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
    let mut total = 0;
    let mut csv = File::create("./rtree.csv")?;
    writeln!(csv, "inserts, nr_internal, nr_leaves, nr_entries")?;
    for m in &mappings {
        let _nr_inserted = rtree.insert(m)?;
        n += 1;

        if n == COMMIT_INTERVAL {
            let stats = rtree.check()?;
            total += n;
            writeln!(
                csv,
                "{}, {}, {}, {}",
                total, stats.nr_internal, stats.nr_leaves, stats.nr_entries
            )?;
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
        test!("insert/many/ascending", test_insert_ascending)
        test!("insert/many/descending", test_insert_descending)
        test!("insert/many/random", test_insert_random)
        test!("insert/many/runs", test_insert_runs)
    };

    Ok(())
}

//-------------------------------
