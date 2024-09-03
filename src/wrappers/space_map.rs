use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};

use Reg::*;

//-------------------------------

pub const ENTRIES_PER_BLOCK: u32 = 16320;

//-------------------------------

pub struct SpaceMap {
    destroy: Addr,
    extend: Addr,
    get_nr_blocks: Addr,
    get_nr_free: Addr,
    get_count: Addr,
    count_is_more_than_one: Addr,
    set_count: Addr,
    commit: Addr,
    inc_block: Addr,
    dec_block: Addr,
    new_block: Addr,
    new_block_in_range: Addr,
    root_size: Addr,
    copy_root: Addr,
    next_free_run: Addr,
    register_threshold_callback: Addr,
}

impl Guest for SpaceMap {
    fn guest_len() -> usize {
        128
    }

    fn pack<W: Write>(&self, w: &mut W, _loc: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.destroy.0)?;
        w.write_u64::<LittleEndian>(self.extend.0)?;
        w.write_u64::<LittleEndian>(self.get_nr_blocks.0)?;
        w.write_u64::<LittleEndian>(self.get_nr_free.0)?;
        w.write_u64::<LittleEndian>(self.get_count.0)?;
        w.write_u64::<LittleEndian>(self.count_is_more_than_one.0)?;
        w.write_u64::<LittleEndian>(self.set_count.0)?;
        w.write_u64::<LittleEndian>(self.commit.0)?;
        w.write_u64::<LittleEndian>(self.inc_block.0)?;
        w.write_u64::<LittleEndian>(self.dec_block.0)?;
        w.write_u64::<LittleEndian>(self.new_block.0)?;
        w.write_u64::<LittleEndian>(self.new_block_in_range.0)?;
        w.write_u64::<LittleEndian>(self.root_size.0)?;
        w.write_u64::<LittleEndian>(self.copy_root.0)?;
        w.write_u64::<LittleEndian>(self.next_free_run.0)?;
        w.write_u64::<LittleEndian>(self.register_threshold_callback.0)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let destroy = Addr(r.read_u64::<LittleEndian>()?);
        let extend = Addr(r.read_u64::<LittleEndian>()?);
        let get_nr_blocks = Addr(r.read_u64::<LittleEndian>()?);
        let get_nr_free = Addr(r.read_u64::<LittleEndian>()?);
        let get_count = Addr(r.read_u64::<LittleEndian>()?);
        let count_is_more_than_one = Addr(r.read_u64::<LittleEndian>()?);
        let set_count = Addr(r.read_u64::<LittleEndian>()?);
        let commit = Addr(r.read_u64::<LittleEndian>()?);
        let inc_block = Addr(r.read_u64::<LittleEndian>()?);
        let dec_block = Addr(r.read_u64::<LittleEndian>()?);
        let new_block = Addr(r.read_u64::<LittleEndian>()?);
        let new_block_in_range = Addr(r.read_u64::<LittleEndian>()?);
        let root_size = Addr(r.read_u64::<LittleEndian>()?);
        let copy_root = Addr(r.read_u64::<LittleEndian>()?);
        let next_free_run = Addr(r.read_u64::<LittleEndian>()?);
        let register_threshold_callback = Addr(r.read_u64::<LittleEndian>()?);

        Ok(SpaceMap {
            destroy,
            extend,
            get_nr_blocks,
            get_nr_free,
            get_count,
            count_is_more_than_one,
            set_count,
            commit,
            inc_block,
            dec_block,
            new_block,
            new_block_in_range,
            root_size,
            copy_root,
            next_free_run,
            register_threshold_callback,
        })
    }
}

pub fn sm_destroy(fix: &mut Fixture, sm_ptr: Addr) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.call_at_with_errno(sm.destroy)
}

pub fn sm_extend(fix: &mut Fixture, sm_ptr: Addr, extra_blocks: u64) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, extra_blocks);
    fix.call_at_with_errno(sm.extend)
}

pub fn sm_get_nr_blocks(fix: &mut Fixture, sm_ptr: Addr) -> Result<u64> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_at_with_errno(sm.get_nr_blocks)?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn sm_get_nr_free(fix: &mut Fixture, sm_ptr: Addr) -> Result<u64> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_at_with_errno(sm.get_nr_free)?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn sm_get_count(fix: &mut Fixture, sm_ptr: Addr, block: u64) -> Result<u32> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 4)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, block);
    fix.vm.set_reg(A2, result_ptr.0);
    fix.call_at_with_errno(sm.get_count)?;

    Ok(fix.vm.mem.read_into::<u32>(result_ptr, PERM_READ)?)
}

pub fn sm_count_is_more_than_one(fix: &mut Fixture, sm_ptr: Addr, block: u64) -> Result<bool> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 4)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, block);
    fix.vm.set_reg(A2, result_ptr.0);
    fix.call_at_with_errno(sm.count_is_more_than_one)?;

    Ok(fix.vm.mem.read_into::<u32>(result_ptr, PERM_READ)? != 0)
}

pub fn sm_set_count(fix: &mut Fixture, sm_ptr: Addr, block: u64, count: u32) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, block);
    fix.vm.set_reg(A2, count as u64);
    fix.call_at_with_errno(sm.set_count)
}

pub fn sm_commit(fix: &mut Fixture, sm_ptr: Addr) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.call_at_with_errno(sm.commit)
}

pub fn sm_inc_block(fix: &mut Fixture, sm_ptr: Addr, b: u64, e: u64) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, e);
    fix.call_at_with_errno(sm.inc_block)
}

pub fn sm_dec_block(fix: &mut Fixture, sm_ptr: Addr, b: u64, e: u64) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, e);
    fix.call_at_with_errno(sm.dec_block)
}

pub fn sm_new_block(fix: &mut Fixture, sm_ptr: Addr) -> Result<u64> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_at_with_errno(sm.new_block)?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn sm_new_block_in_range(fix: &mut Fixture, sm_ptr: Addr, b: u64, e: u64) -> Result<u64> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, e);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A3, result_ptr.0);

    fix.call_at_with_errno(sm.new_block_in_range)?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn sm_get_root_size(fix: &mut Fixture, sm_ptr: Addr) -> Result<u64> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_at_with_errno(sm.root_size)?;

    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn sm_copy_root(fix: &mut Fixture, sm_ptr: Addr, bytes: &mut [u8]) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, bytes.len())?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.vm.set_reg(A2, bytes.len() as u64);
    fix.call_at_with_errno(sm.copy_root)?;

    fix.vm
        .mem
        .read_some(result_ptr, PERM_READ, |src| {
            bytes.copy_from_slice(src);
        })
        .map_err(|_| anyhow!("couldn't copy root"))?;

    Ok(())
}

pub fn sm_next_free_run(
    fix: &mut Fixture,
    sm_ptr: Addr,
    begin: u64,
    end: u64,
) -> Result<(u64, u64)> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    let (mut fix, result_begin_ptr) = auto_alloc(&mut *fix, 8)?;
    let (mut fix, result_end_ptr) = auto_alloc(&mut *fix, 8)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, begin);
    fix.vm.set_reg(A2, end);
    fix.vm.set_reg(A3, result_begin_ptr.0);
    fix.vm.set_reg(A4, result_end_ptr.0);

    fix.call_at_with_errno(sm.next_free_run)?;

    let result_begin = fix.vm.mem.read_into::<u64>(result_begin_ptr, PERM_READ)?;
    let result_end = fix.vm.mem.read_into::<u64>(result_end_ptr, PERM_READ)?;

    Ok((result_begin, result_end))
}

pub fn sm_register_threshold_callback(
    fix: &mut Fixture,
    sm_ptr: Addr,
    threshold: u64,
    func: Addr,
    context: Addr,
) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, threshold);
    fix.vm.set_reg(A2, func.0);
    fix.vm.set_reg(A3, context.0);
    fix.call_at_with_errno(sm.register_threshold_callback)
}

//-------------------------------
