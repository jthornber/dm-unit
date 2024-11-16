use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::wrappers::btree::*;

use anyhow::Result;
use std::marker::PhantomData;

use Reg::*;

//-------------------------------

const DM_ARRAY_INFO_GUEST_LEN: usize = 104;

pub struct ArrayInfo<G: Guest> {
    pub ptr: Addr,
    rust_value_type: PhantomData<G>,
}

fn alloc_array_info<G: Guest>(fix: &mut Fixture) -> Result<ArrayInfo<G>> {
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0; DM_ARRAY_INFO_GUEST_LEN], PERM_READ | PERM_WRITE)?;
    Ok(ArrayInfo {
        ptr,
        rust_value_type: PhantomData,
    })
}

pub fn init_array_info<G: Guest>(
    fix: &mut Fixture,
    tm: Addr,
    vtype: &BTreeValueType<G>,
) -> Result<ArrayInfo<G>> {
    let mut info = alloc_array_info::<G>(fix)?;
    dm_array_info_init(fix, &mut info, tm, vtype)?;
    Ok(info)
}

pub fn free_array_info<G: Guest>(fix: &mut Fixture, info: &mut ArrayInfo<G>) -> Result<()> {
    fix.vm.mem.free(info.ptr)?;
    info.ptr = Addr(0);
    Ok(())
}

pub fn dm_array_info_init<G: Guest>(
    fix: &mut Fixture,
    info: &mut ArrayInfo<G>,
    tm: Addr,
    value_type: &BTreeValueType<G>, // the contained type for the array
) -> Result<()> {
    let (mut fix, vt_ptr) = auto_guest(fix, value_type, PERM_READ | PERM_WRITE)?;

    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, tm.0);
    fix.vm.set_reg(A2, vt_ptr.0);

    fix.call("dm_array_info_init")?;
    Ok(())
}

pub fn dm_array_empty<G: Guest>(fix: &mut Fixture, info: &ArrayInfo<G>) -> Result<u64> {
    let (mut fix, root_ptr) = auto_alloc(fix, 8)?;

    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root_ptr.0);

    fix.call_with_errno("dm_array_empty")?;
    Ok(fix.vm.mem.read_into::<u64>(root_ptr, PERM_READ)?)
}

pub fn dm_array_resize<G: Guest>(
    fix: &mut Fixture,
    info: &ArrayInfo<G>,
    root: u64,
    old_size: u32,
    new_size: u32,
    value: &G,
) -> Result<u64> {
    let (mut fix, value_ptr) = auto_guest(fix, value, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root) = auto_alloc(&mut fix, 8)?;

    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, old_size as u64);
    fix.vm.set_reg(A3, new_size as u64);
    fix.vm.set_reg(A4, value_ptr.0);
    fix.vm.set_reg(A5, new_root.0);

    fix.call_with_errno("dm_array_resize")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root, PERM_READ)?;
    Ok(new_root)
}

pub fn dm_array_new() -> Result<u64> {
    unimplemented!();
}

pub fn dm_array_del<G: Guest>(fix: &mut Fixture, info: &ArrayInfo<G>, root: u64) -> Result<()> {
    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root);
    fix.call_with_errno("dm_array_del")
}

pub fn dm_array_set_value<G: Guest>(
    fix: &mut Fixture,
    info: &ArrayInfo<G>,
    root: u64,
    index: u32,
    value: &G,
) -> Result<u64> {
    let (mut fix, value_ptr) = auto_guest(fix, value, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root) = auto_alloc(&mut fix, 8)?;

    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, index as u64);
    fix.vm.set_reg(A3, value_ptr.0);
    fix.vm.set_reg(A4, new_root.0);

    fix.call_with_errno("dm_array_set_value")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root, PERM_READ)?;
    Ok(new_root)
}

pub fn dm_array_get_value<G: Guest>(
    fix: &mut Fixture,
    info: &ArrayInfo<G>,
    root: u64,
    index: u32,
) -> Result<G> {
    let (mut fix, value_ptr) = auto_alloc(fix, G::guest_len())?;

    fix.vm.set_reg(A0, info.ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, index as u64);
    fix.vm.set_reg(A3, value_ptr.0);

    fix.call_with_errno("dm_array_get_value")?;

    let value = read_guest::<G>(&fix.vm.mem, value_ptr)?;
    Ok(value)
}

//-------------------------------
