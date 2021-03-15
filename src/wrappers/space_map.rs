use crate::decode::*;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;

use anyhow::Result;
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
    root_size: Addr,
    copy_root: Addr,
    register_threshold_callback: Addr,
}

impl Guest for SpaceMap {
    fn guest_len() -> usize {
        112
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
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
        w.write_u64::<LittleEndian>(self.root_size.0)?;
        w.write_u64::<LittleEndian>(self.copy_root.0)?;
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
        let root_size = Addr(r.read_u64::<LittleEndian>()?);
        let copy_root = Addr(r.read_u64::<LittleEndian>()?);
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
            root_size,
            copy_root,
            register_threshold_callback,
        })
    }
}

pub fn sm_inc_block(fix: &mut Fixture, sm_ptr: Addr, block: u64) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, block);
    fix.call_at_with_errno(sm.inc_block)?;
    Ok(())
}

pub fn sm_dec_block(fix: &mut Fixture, sm_ptr: Addr, block: u64) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.vm.set_reg(A1, block);
    fix.call_at_with_errno(sm.dec_block)?;
    Ok(())
}

pub fn sm_new_block(fix: &mut Fixture, sm_ptr: Addr) -> Result<u64> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;

    fix.vm.set_reg(A0, sm_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_at_with_errno(sm.new_block)?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
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

pub fn sm_commit(fix: &mut Fixture, sm_ptr: Addr) -> Result<()> {
    let sm = read_guest::<SpaceMap>(&fix.vm.mem, sm_ptr)?;
    fix.vm.set_reg(A0, sm_ptr.0);
    fix.call_at_with_errno(sm.commit)?;
    Ok(())
}

//-------------------------------
