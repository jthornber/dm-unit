use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::wrappers::array::ArrayInfo;

use anyhow::Result;
use std::marker::PhantomData;

use Reg::*;

//-------------------------------

// sizeof(struct dm_array_cursor)
const ARRAY_CURSOR_GUEST_LEN: usize = 320;

#[derive(Debug)]
pub struct ArrayCursor<G: Guest> {
    ptr: Addr,
    rust_value_type: PhantomData<G>,
}

fn alloc_array_cursor<G: Guest>(fix: &mut Fixture) -> Result<ArrayCursor<G>> {
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0; ARRAY_CURSOR_GUEST_LEN], PERM_READ | PERM_WRITE)?;
    Ok(ArrayCursor {
        ptr,
        rust_value_type: PhantomData,
    })
}

pub fn init_array_cursor<G: Guest>(
    fix: &mut Fixture,
    info: &ArrayInfo<G>,
    root: u64,
) -> Result<ArrayCursor<G>> {
    let mut cursor = alloc_array_cursor::<G>(fix)?;
    if let Err(e) = dm_array_cursor_begin(fix, info, root, &mut cursor) {
        dm_array_cursor_end(fix, &mut cursor)?;
        free_array_cursor(fix, cursor)?;
        return Err(e);
    }
    Ok(cursor)
}

pub fn free_array_cursor<G: Guest>(fix: &mut Fixture, cursor: ArrayCursor<G>) -> Result<()> {
    fix.vm.mem.free(cursor.ptr)?;
    Ok(())
}

//-------------------------------

pub fn dm_array_cursor_begin<G: Guest>(
    fix: &mut Fixture,
    info: &ArrayInfo<G>,
    root: u64,
    cursor: &mut ArrayCursor<G>,
) -> Result<()> {
    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, cursor.ptr.0);
    fix.call_with_errno("dm_array_cursor_begin")
}

pub fn dm_array_cursor_end<G: Guest>(fix: &mut Fixture, cursor: &mut ArrayCursor<G>) -> Result<()> {
    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.call("dm_array_cursor_end")
}

pub fn dm_array_cursor_next<G: Guest>(
    fix: &mut Fixture,
    cursor: &mut ArrayCursor<G>,
) -> Result<()> {
    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.call_with_errno("dm_array_cursor_next")
}

pub fn dm_array_cursor_skip<G: Guest>(
    fix: &mut Fixture,
    cursor: &mut ArrayCursor<G>,
    count: u32,
) -> Result<()> {
    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.vm.set_reg(A1, count as u64);
    fix.call_with_errno("dm_array_cursor_skip")
}

pub fn dm_array_cursor_get_value<G: Guest>(
    fix: &mut Fixture,
    cursor: &ArrayCursor<G>,
) -> Result<G> {
    let (mut fix, ppvalue) = auto_alloc(fix, 8)?;

    fix.vm.set_reg(A0, cursor.ptr.0);
    fix.vm.set_reg(A1, ppvalue.0);

    fix.call("dm_array_cursor_get_value")?;

    let value_ptr = Addr(read_guest::<u64>(&fix.vm.mem, ppvalue)?);
    let value = read_guest::<G>(&fix.vm.mem, value_ptr)?;
    Ok(value)
}

//-------------------------------
