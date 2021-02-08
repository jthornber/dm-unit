use crate::memory::*;
use crate::test_runner::*;
use crate::fixture::*;
use crate::wrappers::transaction_manager::*;
use crate::wrappers::btree::*;
use crate::wrappers::block_manager::*;
use crate::stubs::*;

use anyhow::{ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::info;
use std::io;
use std::io::{Read, Write};
use std::marker::PhantomData;

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

    for i in 0u64..1024u64 {
        let keys = vec![i];
        let v = Value64(i + 1000000);
        root = dm_btree_insert(fix, &info, root, &keys, &v)?;
    }

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
