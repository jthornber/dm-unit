use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::wrappers::btree::BTreeInfoPtr;

use anyhow::Result;
use std::marker::PhantomData;

use Reg::*;

//-------------------------------

// sizeof(struct dm_btree_cursor)
const BTREE_CURSOR_GUEST_LEN: usize = 288;

#[derive(Debug)]
pub struct BTreeCursor<G: Guest> {
    ptr: Addr,
    rust_value_type: PhantomData<G>,
}

fn alloc_btree_cursor<G: Guest>(fix: &mut Fixture) -> Result<BTreeCursor<G>> {
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0; BTREE_CURSOR_GUEST_LEN], PERM_READ | PERM_WRITE)?;
    Ok(BTreeCursor {
        ptr,
        rust_value_type: PhantomData,
    })
}

pub fn init_btree_cursor<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfoPtr<G>,
    root: u64,
    prefetch_leaves: bool,
) -> Result<BTreeCursor<G>> {
    let mut cursor = alloc_btree_cursor::<G>(fix)?;

    if let Err(e) = dm_btree_cursor_begin(fix, info, root, prefetch_leaves, &mut cursor) {
        dm_btree_cursor_end(fix, &mut cursor)?;
        free_btree_cursor(fix, cursor)?;
        return Err(e);
    }

    Ok(cursor)
}

pub fn free_btree_cursor<G: Guest>(fix: &mut Fixture, info: BTreeCursor<G>) -> Result<()> {
    fix.vm.mem.free(info.ptr)?;
    Ok(())
}

//-------------------------------

pub fn dm_btree_cursor_begin<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfoPtr<G>,
    root: u64,
    prefetch_leaves: bool,
    cursor: &mut BTreeCursor<G>,
) -> Result<()> {
    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, prefetch_leaves as u64);
    fix.vm.set_reg(A3, cursor.ptr.0);
    fix.call_with_errno("dm_btree_cursor_begin")
}

pub fn dm_btree_cursor_end<G: Guest>(fix: &mut Fixture, cursor: &mut BTreeCursor<G>) -> Result<()> {
    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.call("dm_btree_cursor_end")
}

pub fn dm_btree_cursor_next<G: Guest>(
    fix: &mut Fixture,
    cursor: &mut BTreeCursor<G>,
) -> Result<()> {
    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.call_with_errno("dm_btree_cursor_next")
}

pub fn dm_btree_cursor_skip<G: Guest>(
    fix: &mut Fixture,
    cursor: &mut BTreeCursor<G>,
    count: u32,
) -> Result<()> {
    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.vm.set_reg(A1, count as u64);
    fix.call_with_errno("dm_btree_cursor_skip")
}

pub fn dm_btree_cursor_get_value<G: Guest>(
    fix: &mut Fixture,
    cursor: &BTreeCursor<G>,
) -> Result<(u64, G)> {
    let (mut fix, key_ptr) = auto_alloc(fix, 8)?;
    let (mut fix, value_ptr) = auto_alloc(&mut fix, G::guest_len())?;

    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.vm.set_reg(A1, key_ptr.0);
    fix.vm.set_reg(A2, value_ptr.0);

    fix.call_with_errno("dm_btree_cursor_get_value")?;

    let key = fix.vm.mem.read_into::<u64>(key_ptr, PERM_READ)?;
    let value = read_guest::<G>(&fix.vm.mem, value_ptr)?;
    Ok((key, value))
}

//-------------------------------
