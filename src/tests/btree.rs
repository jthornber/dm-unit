use crate::decode::*;
use crate::memory::*;
use crate::test_runner::*;
use crate::tests::block_manager::*;
use crate::tests::fixture::*;
use crate::tests::transaction_manager::*;

use anyhow::{ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::info;
use std::io;
use std::io::{Read, Write};
use std::marker::PhantomData;

use Reg::*;

//-------------------------------

pub struct BTreeValueType<G: Guest> {
    context: Addr,
    inc_fn: Addr,
    dec_fn: Addr,
    eq_fn: Addr,
    rust_value_type: PhantomData<G>,
}

impl<G: Guest> Guest for BTreeValueType<G> {
    fn guest_len() -> usize {
        // 4 functions ptrs and a u32
        4 * 8 + 4
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.context.0)?;
        w.write_u32::<LittleEndian>(G::guest_len() as u32)?;
        w.write_u32::<LittleEndian>(0)?; // padding
        w.write_u64::<LittleEndian>(self.inc_fn.0)?;
        w.write_u64::<LittleEndian>(self.dec_fn.0)?;
        w.write_u64::<LittleEndian>(self.eq_fn.0)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let context = Addr(r.read_u64::<LittleEndian>()?);
        let size = r.read_u32::<LittleEndian>()?;
        let _padding = r.read_u32::<LittleEndian>()?;
        let inc_fn = Addr(r.read_u64::<LittleEndian>()?);
        let dec_fn = Addr(r.read_u64::<LittleEndian>()?);
        let eq_fn = Addr(r.read_u64::<LittleEndian>()?);

        assert!(size == G::guest_len() as u32);

        Ok(BTreeValueType {
            context,
            inc_fn,
            dec_fn,
            eq_fn,
            rust_value_type: PhantomData,
        })
    }
}

pub struct BTreeInfo<G: Guest> {
    tm: Addr,
    levels: u32,
    vtype: BTreeValueType<G>,
}

impl<G: Guest> Guest for BTreeInfo<G> {
    fn guest_len() -> usize {
        8 + 4 + BTreeValueType::<G>::guest_len()
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.tm.0)?;
        w.write_u32::<LittleEndian>(self.levels)?;
        w.write_u32::<LittleEndian>(0)?; // padding
        self.vtype.pack(w)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let tm = Addr(r.read_u64::<LittleEndian>()?);
        let levels = r.read_u32::<LittleEndian>()?;
        let _padding = r.read_u32::<LittleEndian>()?;
        let vtype = BTreeValueType::unpack(r)?;

        Ok(BTreeInfo { tm, levels, vtype })
    }
}

fn auto_info<'a, G: Guest>(
    fix: &'a mut Fixture,
    info: &BTreeInfo<G>,
) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = alloc_guest(&mut fix.vm.mem, info, PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

pub fn dm_btree_empty<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;

    fix.vm.set_reg(A0, info_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_btree_empty")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_btree_del<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>, root: u64) -> Result<()> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.call_with_errno("dm_btree_del")
}

fn auto_keys<'a>(fix: &'a mut Fixture, keys: &[u64]) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = fix.vm.mem.alloc(8 * keys.len())?;

    for i in 0..keys.len() {
        let bytes = keys[i].to_le_bytes();
        fix.vm
            .mem
            .write(Addr(ptr.0 + (8 * i as u64)), &bytes, PERM_WRITE)?;
    }

    Ok((AutoGPtr::new(fix, ptr), ptr))
}

// Returns the new root
pub fn dm_btree_insert<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
    v: &G,
) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;
    let (mut fix, guest_keys) = auto_keys(&mut *fix, keys)?;
    let (mut fix, guest_value) = auto_guest(&mut *fix, v, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root) = auto_alloc(&mut *fix, 8)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, guest_keys.0);
    fix.vm.set_reg(A3, guest_value.0);
    fix.vm.set_reg(A4, new_root.0);

    fix.call_with_errno("dm_btree_insert")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root, PERM_READ)?;
    Ok(new_root)
}

pub fn dm_btree_lookup<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
) -> Result<G> {
    ensure!(keys.len() == info.levels as usize);

    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);

    let (mut fix, keys_ptr) = auto_keys(&mut *fix, keys)?;
    fix.vm.set_reg(A2, keys_ptr.0);

    let (mut fix, value_ptr) = auto_alloc(&mut *fix, G::guest_len())?;
    fix.vm.set_reg(A3, value_ptr.0);

    fix.call_with_errno("dm_btree_lookup")?;

    let value = read_guest::<G>(&fix.vm.mem, value_ptr)?;
    Ok(value)
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

// Delete an empty tree.
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
    fix.standard_globals()?;

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
    fix.standard_globals()?;
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
    fix.standard_globals()?;
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
