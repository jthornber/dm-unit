use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::emulator::memory::*;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Cursor, Read, Write};

use Reg::*;

//-------------------------------

pub fn dm_pool_metadata_open(
    fix: &mut Fixture,
    bdev_ptr: Addr,
    data_block_size: u64,
    format: bool,
) -> Result<Addr> {
    fix.vm.set_reg(A0, bdev_ptr.0);
    fix.vm.set_reg(A1, data_block_size);
    fix.vm.set_reg(A2, if format { 1 } else { 0 });
    fix.call("dm_pool_metadata_open")?;

    // FIXME: check for ERR_PTR
    Ok(Addr(fix.vm.reg(A0)))
}

pub fn dm_pool_get_block_manager(fix: &mut Fixture, pmd: Addr) -> Result<Addr> {
    let bm_ptr = Addr(fix.vm.mem.read_some(pmd, PERM_READ, |bytes| {
        let mut r = Cursor::new(bytes);
        r.set_position(24);
        let bm_ptr = r.read_u64::<LittleEndian>().unwrap();
        bm_ptr
    })?);
    Ok(bm_ptr)
}

pub fn dm_pool_metadata_close(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_metadata_close")
}

pub type ThinId = u32;
pub fn dm_pool_create_thin(fix: &mut Fixture, pmd: Addr, thin_id: ThinId) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, thin_id as u64);
    fix.call_with_errno("dm_pool_create_thin")
}

pub fn dm_pool_create_snap(
    fix: &mut Fixture,
    pmd: Addr,
    thin_id: ThinId,
    origin_id: ThinId,
) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, thin_id as u64);
    fix.vm.set_reg(A2, origin_id as u64);
    fix.call_with_errno("dm_pool_create_snap")
}

pub fn dm_pool_delete_thin_device(fix: &mut Fixture, pmd: Addr, thin_id: ThinId) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, thin_id as u64);
    fix.call_with_errno("dm_pool_delete_thin_device")
}

pub fn dm_pool_commit_metadata(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_commit_metadata")
}

pub fn dm_pool_abort_metadata(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_abort_metadata")
}

pub fn dm_pool_set_metadata_transaction(
    fix: &mut Fixture,
    pmd: Addr,
    current_id: u64,
    new_id: u64,
) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, current_id);
    fix.vm.set_reg(A2, new_id);
    fix.call_with_errno("dm_pool_set_metadata_transaction")
}

pub fn dm_pool_get_metadata_transaction_id(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_get_metadata_transaction_id")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_pool_reserve_metadata_snap(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_reserve_metadata_snap")
}

pub fn dm_pool_release_metadata_snap(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_release_metadata_snap")
}

pub fn dm_pool_get_metadata_snap(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_get_metadata_snap")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_pool_open_thin_device(fix: &mut Fixture, pmd: Addr, thin_id: ThinId) -> Result<Addr> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, thin_id as u64);
    fix.vm.set_reg(A2, result_ptr.0);
    fix.call_with_errno("dm_pool_open_thin_device")?;
    Ok(Addr(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?))
}

pub fn dm_pool_close_thin_device(fix: &mut Fixture, td: Addr) -> Result<()> {
    fix.vm.set_reg(A0, td.0);
    fix.call_with_errno("dm_pool_close_thin_device")
}

pub fn dm_thin_dev_id(fix: &mut Fixture, td: Addr) -> Result<ThinId> {
    fix.vm.set_reg(A0, td.0);
    fix.call("dm_thin_dev_id")?;
    Ok(fix.vm.reg(A0) as u32)
}

pub struct LookupResult {
    pub block: u64,
    pub shared: bool,
}

impl Default for LookupResult {
    fn default() -> Self {
        LookupResult {
            block: 0,
            shared: false,
        }
    }
}

impl Guest for LookupResult {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.block)?;
        w.write_u8(if self.shared { 1u8 } else { 0u8 })?;
        w.write_all(&[0u8, 7])?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let block = r.read_u64::<LittleEndian>()?;
        let shared = r.read_u8()? != 0;
        Ok(LookupResult { block, shared })
    }
}

pub fn dm_thin_find_block(
    fix: &mut Fixture,
    td: Addr,
    block: u64,
    can_issue_io: bool,
) -> Result<LookupResult> {
    let (mut fix, result_ptr) =
        auto_guest::<LookupResult>(fix, &LookupResult::default(), PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, block);
    fix.vm.set_reg(A2, if can_issue_io { 1 } else { 0 });
    fix.vm.set_reg(A3, result_ptr.0);
    fix.call_with_errno("dm_thin_find_block")?;
    read_guest::<LookupResult>(&fix.vm.mem, result_ptr)
}

pub struct MappedRangeResult {
    pub thin_begin: u64,
    pub thin_end: u64,
    pub pool_begin: u64,
    pub maybe_shared: bool,
}

pub fn dm_thin_find_mapped_range(
    fix: &mut Fixture,
    td: Addr,
    begin: u64,
    end: u64,
) -> Result<MappedRangeResult> {
    let (mut fix, thin_begin_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    let (mut fix, thin_end_ptr) = auto_guest::<u64>(&mut fix, &0, PERM_READ | PERM_WRITE)?;
    let (mut fix, pool_begin_ptr) = auto_guest::<u64>(&mut fix, &0, PERM_READ | PERM_WRITE)?;
    let (mut fix, maybe_shared_ptr) = auto_guest::<u64>(&mut fix, &0, PERM_READ | PERM_WRITE)?;

    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, begin);
    fix.vm.set_reg(A2, end);
    fix.vm.set_reg(A3, thin_begin_ptr.0);
    fix.vm.set_reg(A4, thin_end_ptr.0);
    fix.vm.set_reg(A5, pool_begin_ptr.0);
    fix.vm.set_reg(A6, maybe_shared_ptr.0);

    fix.call_with_errno("dm_thin_find_mapped_range")?;

    let thin_begin = read_guest::<u64>(&fix.vm.mem, thin_begin_ptr)?;
    let thin_end = read_guest::<u64>(&fix.vm.mem, thin_end_ptr)?;
    let pool_begin = read_guest::<u64>(&fix.vm.mem, pool_begin_ptr)?;
    let maybe_shared = read_guest::<u64>(&fix.vm.mem, maybe_shared_ptr)? != 0;

    Ok(MappedRangeResult {
        thin_begin,
        thin_end,
        pool_begin,
        maybe_shared,
    })
}

pub fn dm_pool_alloc_data_block(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;

    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_alloc_data_block")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_thin_insert_block(
    fix: &mut Fixture,
    td: Addr,
    thin_block: u64,
    data_block: u64,
) -> Result<()> {
    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, thin_block);
    fix.vm.set_reg(A2, data_block);
    fix.call_with_errno("dm_thin_insert_block")
}

pub fn dm_thin_remove_block(fix: &mut Fixture, td: Addr, thin_block: u64) -> Result<()> {
    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, thin_block);
    fix.call_with_errno("dm_thin_remove_block")
}

pub fn dm_thin_remove_range(fix: &mut Fixture, td: Addr, begin: u64, end: u64) -> Result<()> {
    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, begin);
    fix.vm.set_reg(A2, end);
    fix.call_with_errno("dm_thin_remove_range")
}

pub fn dm_thin_changed_this_transaction(fix: &mut Fixture, td: Addr) -> Result<bool> {
    fix.vm.set_reg(A0, td.0);
    fix.call("dm_pool_clone_thin_device")?;
    Ok(fix.vm.reg(A0) != 0)
}

pub fn dm_pool_changed_thin_transaction(fix: &mut Fixture, pmd: Addr) -> Result<bool> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call("dm_pool_changed_thin_transaction")?;
    Ok(fix.vm.reg(A0) != 0)
}

pub fn dm_thin_aborted_changes(fix: &mut Fixture, td: Addr) -> Result<bool> {
    fix.vm.set_reg(A0, td.0);
    fix.call_with_errno("dm_thin_aborted_changes")?;
    Ok(fix.vm.reg(A0) != 0)
}

pub fn dm_thin_get_highest_mapped_block(fix: &mut Fixture, td: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_thin_get_highest_mapped_block")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_thin_get_mapped_count(fix: &mut Fixture, td: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, td.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_clone_thin_device")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_pool_get_free_block_count(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_get_free_block_count")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_pool_get_free_metadata_block_count(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_get_free_metadata_block_count")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_pool_get_metadata_dev_size(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_get_metadata_dev_size")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_pool_get_data_dev_size(fix: &mut Fixture, pmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_pool_get_data_dev_size")?;
    read_guest::<u64>(&fix.vm.mem, result_ptr)
}

pub fn dm_pool_block_is_shared(fix: &mut Fixture, pmd: Addr, b: u64) -> Result<bool> {
    let (mut fix, result_ptr) = auto_guest::<u64>(fix, &0, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, result_ptr.0);
    fix.call_with_errno("dm_pool_block_is_shared")?;
    Ok(read_guest::<u64>(&fix.vm.mem, result_ptr)? != 0)
}

pub fn dm_pool_inc_data_range(fix: &mut Fixture, pmd: Addr, begin: u64, end: u64) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, begin);
    fix.vm.set_reg(A2, end);
    fix.call_with_errno("dm_pool_inc_data_range")
}

pub fn dm_pool_dec_data_range(fix: &mut Fixture, pmd: Addr, begin: u64, end: u64) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, begin);
    fix.vm.set_reg(A2, end);
    fix.call_with_errno("dm_pool_dec_data_range")
}

pub fn dm_pool_resize_data_dev(fix: &mut Fixture, pmd: Addr, new_size: u64) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, new_size);
    fix.call_with_errno("dm_pool_resize_data_dev")
}

pub fn dm_pool_resize_metadata_dev(fix: &mut Fixture, pmd: Addr, new_size: u64) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.vm.set_reg(A1, new_size);
    fix.call_with_errno("dm_pool_resize_metadata_dev")
}

pub fn dm_pool_metadata_read_only(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_metadata_read_only")
}

pub fn dm_pool_metadata_read_write(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_metadata_read_write")
}

pub fn dm_pool_metadata_set_needs_check(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_metadata_set_needs_check")
}

pub fn dm_pool_metadata_needs_check(fix: &mut Fixture, pmd: Addr) -> Result<bool> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call_with_errno("dm_pool_clone_thin_device")?;
    Ok(fix.vm.reg(A0) != 0)
}

pub fn dm_pool_issue_prefetches(fix: &mut Fixture, pmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, pmd.0);
    fix.call("dm_pool_issue_prefetches")
}

//-------------------------------

// FIXME: not done yet
/*
int dm_pool_register_metadata_threshold(struct dm_pool_metadata *pmd,
                    dm_block_t threshold,
                    dm_sm_threshold_fn fn,
                    void *context);


                    */

/*
void dm_pool_register_pre_commit_callback(struct dm_pool_metadata *pmd,
                      dm_pool_pre_commit_fn fn,
                      void *context);


                      */

//-------------------------------
