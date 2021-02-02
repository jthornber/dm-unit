use crate::decode::*;
use crate::memory::*;
use crate::test_runner::*;
use crate::tests::block_manager::*;
use crate::tests::transaction_manager::*;
use crate::tests::fixture::*;

use anyhow::{anyhow, ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use crc32c::crc32c;
use log::{debug, info, warn};
use std::collections::BTreeMap;
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
        w.write_u64::<LittleEndian>(self.inc_fn.0)?;
        w.write_u64::<LittleEndian>(self.dec_fn.0)?;
        w.write_u64::<LittleEndian>(self.eq_fn.0)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let context = Addr(r.read_u64::<LittleEndian>()?);
        let size = r.read_u32::<LittleEndian>()?;
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
        self.vtype.pack(w)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let tm = Addr(r.read_u64::<LittleEndian>()?);
        let levels = r.read_u32::<LittleEndian>()?;
        let vtype = BTreeValueType::unpack(r)?;

        Ok(BTreeInfo { tm, levels, vtype })
    }
}

fn alloc_info<'a, G: Guest>(
    fix: &'a mut Fixture,
    info: &BTreeInfo<G>,
) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = alloc_guest(&mut fix.vm.mem, info, PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

pub fn dm_btree_empty<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>) -> Result<u64> {
    let (mut fix, info_ptr) = alloc_info(fix, info)?;

    fix.vm.set_reg(A0, info_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_btree_empty");
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_btree_del<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>, root: u64) -> Result<()> {
    let (mut fix, info_ptr) = alloc_info(fix, info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.call_with_errno("dm_btree_del")
}

/*
// FIXME: return value
fn dm_btree_lookup(fix: &mut Fixture, info: BTreeInfo, root: u64, keys: &[u64]) -> Result<()> {
    ensure!(keys.len() == info.levels);

    let (mut fix, info_ptr) = alloc_info(fix, info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);

    let (mut fix, keys_ptr) = alloc_keys(&mut *fix, keys)?;
    fix.vm.set_reg(A2, keys_ptr.0);

    let (mut fix, value_ptr) = auto_alloc(&mut *fix, ValueType::guest_len())?;
    fix.vm.set_reg(A3, value_ptr.0);

    fix.call_with_errno("dm_btree_lookup")?;

    // FIXME: unpack the value
    let value = read_guest::<???>(fix.vm.mem, value_ptr);
    Ok(value)
}
*/

//-------------------------------

/// A little wrapper to let us store u64's in btrees.
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

// Delete an empty tree.
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
    fix.standard_globals()?;
    fix.trace_func("dm_btree_empty")?;
    fix.trace_func("sm_bootstrap_new_block")?;
    fix.trace_func("dm_tm_create")?;
    fix.trace_func("dm_sm_metadata_create")?;
    fix.trace_func("sm_ll_new_metadata")?;
    fix.trace_func("sm_ll_init")?;
    fix.trace_func("metadata_ll_init_index")?;
    fix.trace_func("dm_tm_new_block")?;
    fix.trace_func("sm_bootstrap_new_block")?;
    fix.trace_func("sm_ll_extend")?;

    let bm = dm_bm_create(fix, 1024)?;
    debug!("calling dm_tm_create");
    let (tm, sm) = dm_tm_create(fix, bm, 0)?;

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
    debug!("calling dm_btree_empty");
    let root = dm_btree_empty(fix, &info)?;
    debug!("calling dm_btree_del");
    dm_btree_del(fix, &info, root)?;
    Ok(())
}

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    info!("registered /pdata/btree/remove tests");

    runner.register("/pdata/btree/del/empty", Box::new(test_del_empty));
    Ok(())
}

//-------------------------------
