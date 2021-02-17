use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;
use crate::stubs::block_manager::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::btree::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{anyhow, ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use nom::{number::complete::*, IResult};
use std::io;
use std::io::{Read, Write};
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU32, Ordering};
use thinp::io_engine::BLOCK_SIZE;
use thinp::pdata::btree;
use thinp::pdata::btree::*;
use thinp::pdata::btree_walker::*;
use thinp::pdata::unpack::*;

//-------------------------------

struct NoopVisitor {}

impl<V: Unpack> NodeVisitor<V> for NoopVisitor {
    fn visit(
        &self,
        _path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        _keys: &[u64],
        _values: &[V],
    ) -> btree::Result<()> {
        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

#[allow(dead_code)]
fn check_btree(root: u64) -> Result<()> {
    let engine = get_bm()?.engine.clone();
    let walker = BTreeWalker::new(engine, false);
    let visitor = NoopVisitor {};
    let mut path = Vec::new();

    walker.walk::<NoopVisitor, Value64>(&mut path, &visitor, root)?;

    Ok(())
}

//-------------------------------

struct ResidencyVisitor {
    nr_entries: AtomicU32,
    nr_leaves: AtomicU32,
}

impl<V: Unpack> NodeVisitor<V> for ResidencyVisitor {
    fn visit(
        &self,
        _path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        keys: &[u64],
        _values: &[V],
    ) -> btree::Result<()> {
        self.nr_entries
            .fetch_add(keys.len() as u32, Ordering::SeqCst);
        self.nr_leaves.fetch_add(1, Ordering::SeqCst);
        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

fn calc_max_entries<V: Unpack>() -> usize {
    let elt_size = 8 + V::disk_size() as usize; // key + value size
    ((BLOCK_SIZE - NodeHeader::disk_size() as usize) / elt_size) as usize
}

// Because this is a walk it implicitly checks the btree.  Returns
// average residency as a _percentage_.
fn calc_residency(root: u64) -> Result<usize> {
    let engine = get_bm()?.engine.clone();
    let walker = BTreeWalker::new(engine, false);
    let visitor = ResidencyVisitor {
        nr_entries: AtomicU32::new(0),
        nr_leaves: AtomicU32::new(0),
    };
    let mut path = Vec::new();

    walker.walk::<ResidencyVisitor, Value64>(&mut path, &visitor, root)?;

    let nr_entries = visitor.nr_entries.load(Ordering::SeqCst) as usize;
    let nr_leaves = visitor.nr_leaves.load(Ordering::SeqCst) as usize;
    let max_entries = calc_max_entries::<Value64>();

    let percent = (nr_entries * 100) / (max_entries * nr_leaves);

    Ok(percent)
}

//-------------------------------

/// A little wrapper to let us store u64's in btrees.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Value64(u64);

impl Guest for Value64 {
    fn guest_len() -> usize {
        8
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.0)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let v = r.read_u64::<LittleEndian>()?;
        Ok(Value64(v))
    }
}

impl Unpack for Value64 {
    fn disk_size() -> u32 {
        8
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Self> {
        let (i, v) = le_u64(data)?;
        Ok((i, Value64(v)))
    }
}

#[allow(dead_code)]
fn enable_traces(fix: &mut Fixture) -> Result<()> {
    let traces = [
        "btree_insert_raw",
        "dm_btree_cursor_begin",
        "dm_btree_cursor_end",
        "dm_btree_cursor_get_value",
        "dm_btree_cursor_next",
        "dm_btree_cursor_skip",
        "dm_btree_del",
        "dm_btree_empty",
        "dm_btree_find_highest_key",
        "dm_btree_find_lowest_key",
        "dm_btree_insert",
        "dm_btree_insert_notify",
        "dm_btree_lookup",
        "dm_btree_lookup_next",
        "dm_btree_lookup_next_single",
        "dm_btree_remove",
        "dm_btree_remove_leaves",
        "dm_btree_walk",
        "dm_sm_metadata_create",
        "dm_tm_create",
        "dm_tm_create_with_sm",
        "dm_tm_new_block",
        "dm_tm_unlock",
        "insert",
        "insert_at",
        "lower_bound",
        "metadata_ll_init_index",
        "shadow_current",
        "shadow_step",
        "sm_bootstrap_new_block",
        "sm_bootstrap_new_block",
        "sm_ll_extend",
        "sm_ll_init",
        "sm_ll_new_metadata",
    ];
    for t in &traces {
        fix.trace_func(t)?;
    }
    Ok(())
}

//-------------------------------

// Delete an empty tree.
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let bm = dm_bm_create(fix, 1024)?;
    let (tm, _sm) = dm_tm_create(fix, bm, 0)?;

    let vtype: BTreeValueType<Value64> = BTreeValueType {
        context: Addr(0),
        inc_fn: Addr(0),
        dec_fn: Addr(0),
        eq_fn: Addr(0),
        rust_value_type: PhantomData,
    };
    let info = BTreeInfo {
        tm,
        levels: 1,
        vtype,
    };

    let root = dm_btree_empty(fix, &info)?;
    dm_btree_del(fix, &info, root)?;
    Ok(())
}

fn test_insert_ascending(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    enable_traces(fix)?;

    let bm = dm_bm_create(fix, 1024)?;
    let (tm, _sm) = dm_tm_create(fix, bm, 0)?;

    let vtype: BTreeValueType<Value64> = BTreeValueType {
        context: Addr(0),
        inc_fn: Addr(0),
        dec_fn: Addr(0),
        eq_fn: Addr(0),
        rust_value_type: PhantomData,
    };
    let info = BTreeInfo {
        tm,
        levels: 1,
        vtype,
    };
    let mut root = dm_btree_empty(fix, &info)?;
    debug!("empty complete");

    for i in 0u64..1024u64 {
        let keys = vec![i];
        let v = Value64(i + 1000000);
        root = dm_btree_insert(fix, &info, root, &keys, &v)?;
    }

    let residency = calc_residency(root)?;

    if residency < 75 {
        return Err(anyhow!("Residency is too low ({}%)", residency));
    }
    info!("residency = {}", residency);

    dm_btree_del(fix, &info, root)?;
    dm_tm_destroy(fix, tm)?;
    dm_bm_destroy(fix, bm)?;

    Ok(())
}

fn test_lookup(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    enable_traces(fix)?;

    let bm = dm_bm_create(fix, 1024)?;
    let (tm, _sm) = dm_tm_create(fix, bm, 0)?;

    let vtype: BTreeValueType<Value64> = BTreeValueType {
        context: Addr(0),
        inc_fn: Addr(0),
        dec_fn: Addr(0),
        eq_fn: Addr(0),
        rust_value_type: PhantomData,
    };
    let info = BTreeInfo {
        tm,
        levels: 1,
        vtype,
    };
    let mut root = dm_btree_empty(fix, &info)?;

    // FIXME: bump count up
    let count = 1024u64;
    for i in 0u64..count {
        let keys = vec![i];
        let v = Value64(i + 1000000);
        root = dm_btree_insert(fix, &info, root, &keys, &v)?;
    }

    check_btree(root)?;

    for i in 0u64..count {
        let keys = vec![i];
        let v = dm_btree_lookup(fix, &info, root, &keys)?;
        ensure!(v == Value64(i + 1000000));
    }

    dm_btree_del(fix, &info, root)?;
    dm_tm_destroy(fix, tm)?;
    dm_bm_destroy(fix, bm)?;

    Ok(())
}

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let mut reg = move |path, func| {
        let mut p = "/pdata/btree/".to_string();
        p.push_str(path);
        runner.register(&p, func);
    };

    reg("del/empty", Box::new(test_del_empty));
    reg("insert/ascending", Box::new(test_insert_ascending));
    reg("lookup", Box::new(test_lookup));

    info!("registered /pdata/btree/remove tests");
    Ok(())
}

//-------------------------------
