use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};
use std::sync::{Arc, Mutex};

use Reg::*;

//-------------------------------

pub fn dm_cache_metadata_open(
    fix: &mut Fixture,
    bdev_ptr: Addr,
    data_block_sectors: u64,
    may_format: bool,
    policy_hint_size: u32,
    metadata_version: usize,
) -> Result<Addr> {
    fix.vm.set_reg(A0, bdev_ptr.0);
    fix.vm.set_reg(A1, data_block_sectors);
    fix.vm.set_reg(A2, if may_format { 1 } else { 0 });
    fix.vm.set_reg(A3, policy_hint_size as u64);
    fix.vm.set_reg(A4, metadata_version as u64);

    fix.call("dm_cache_metadata_open")?;

    // FIXME: check for ERR_PTR
    Ok(Addr(fix.vm.reg(A0)))
}

pub fn dm_cache_metadata_close(fix: &mut Fixture, cmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.call_with_errno("dm_cache_metadata_close")
}

pub fn dm_cache_resize(fix: &mut Fixture, cmd: Addr, nr_cblocks: u64) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, nr_cblocks);
    fix.call_with_errno("dm_cache_resize")
}

pub fn dm_cache_size(fix: &mut Fixture, cmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_cache_size")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_cache_discard_bitset_resize(
    fix: &mut Fixture,
    cmd: Addr,
    discard_block_sectors: u64,
    nr_discard_blocks: u64,
) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, discard_block_sectors);
    fix.vm.set_reg(A2, nr_discard_blocks);
    fix.call_with_errno("dm_cache_discard_bitset_resize")
}

pub fn dm_cache_set_discard(
    fix: &mut Fixture,
    cmd: Addr,
    discard_block: u64,
    discard: bool,
) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, discard_block);
    fix.vm.set_reg(A2, if discard { 1 } else { 0 });
    fix.call_with_errno("dm_cache_set_discard")
}

pub fn dm_cache_remove_mapping(fix: &mut Fixture, cmd: Addr, cache_block: u64) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, cache_block);
    fix.call_with_errno("dm_cache_remove_mapping")
}

pub fn dm_cache_insert_mapping(
    fix: &mut Fixture,
    cmd: Addr,
    cache_block: u64,
    origin_block: u64,
) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, cache_block);
    fix.vm.set_reg(A2, origin_block);
    fix.call_with_errno("dm_cache_insert_mapping")
}

pub fn dm_cache_changed_this_transaction(fix: &mut Fixture, cmd: Addr) -> Result<bool> {
    fix.vm.set_reg(A0, cmd.0);
    fix.call_with_errno("dm_cache_changed_this_transaction")?;
    Ok(if fix.vm.reg(A0) == 0 { false } else { true })
}

pub fn dm_cache_set_dirty_bits(
    _fix: &mut Fixture,
    _cmd: Addr,
    _bits: &bit_set::BitSet,
) -> Result<()> {
    todo!();
}

pub struct CacheStats {
    pub read_hits: u32,
    pub read_misses: u32,
    pub write_hits: u32,
    pub write_misses: u32,
}

impl Default for CacheStats {
    fn default() -> Self {
        CacheStats {
            read_hits: 0,
            read_misses: 0,
            write_hits: 0,
            write_misses: 0,
        }
    }
}

impl Guest for CacheStats {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u32::<LittleEndian>(self.read_hits)?;
        w.write_u32::<LittleEndian>(self.read_misses)?;
        w.write_u32::<LittleEndian>(self.write_hits)?;
        w.write_u32::<LittleEndian>(self.write_misses)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let read_hits = r.read_u32::<LittleEndian>()?;
        let read_misses = r.read_u32::<LittleEndian>()?;
        let write_hits = r.read_u32::<LittleEndian>()?;
        let write_misses = r.read_u32::<LittleEndian>()?;
        Ok(CacheStats {
            read_hits,
            read_misses,
            write_hits,
            write_misses,
        })
    }
}

pub fn dm_cache_metadata_get_stats(fix: &mut Fixture, cmd: Addr) -> Result<CacheStats> {
    let (mut fix, result_ptr) =
        auto_guest::<CacheStats>(fix, &CacheStats::default(), PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_with_errno("dm_cache_metadata_get_stats")?;

    read_guest::<CacheStats>(&fix.vm.mem, result_ptr)
}

pub fn dm_cache_metadata_set_stats(fix: &mut Fixture, cmd: Addr, stats: &CacheStats) -> Result<()> {
    let (mut fix, result_ptr) = auto_guest::<CacheStats>(fix, stats, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_with_errno("dm_cache_metadata_set_stats")
}

pub fn dm_cache_commit(fix: &mut Fixture, cmd: Addr, clean_shutdown: bool) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, if clean_shutdown { 1 } else { 0 });
    fix.call_with_errno("dm_cache_commit")
}

pub fn dm_cache_get_free_metadata_block_count(fix: &mut Fixture, cmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_cache_get_free_metadata_block_count")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_cache_get_metadata_dev_size(fix: &mut Fixture, cmd: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_cache_get_metadata_dev_size")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_cache_write_hints(_fix: &mut Fixture, _cmd: Addr, _policy: Addr) -> Result<()> {
    todo!();
}

fn bool_query(fix: &mut Fixture, cmd: Addr, symbol: &str) -> Result<bool> {
    let (mut fix, result_ptr) = auto_alloc(fix, 4)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno(symbol)?;
    if fix.vm.mem.read_into::<u32>(result_ptr, PERM_READ)? == 0 {
        Ok(false)
    } else {
        Ok(true)
    }
}

pub fn dm_cache_metadata_all_clean(fix: &mut Fixture, cmd: Addr) -> Result<bool> {
    bool_query(fix, cmd, "dm_cache_metadata_all_clean")
}

pub fn dm_cache_metadata_needs_check(fix: &mut Fixture, cmd: Addr) -> Result<bool> {
    bool_query(fix, cmd, "dm_cache_metadata_needs_check")
}

pub fn dm_cache_metadata_set_needs_check(fix: &mut Fixture, cmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.call_with_errno("dm_cache_metadata_set_needs_check")
}

pub fn dm_cache_metadata_set_read_only(fix: &mut Fixture, cmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.call_with_errno("dm_cache_metadata_set_read_only")
}

pub fn dm_cache_metadata_set_read_write(fix: &mut Fixture, cmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.call_with_errno("dm_cache_metadata_set_read_write")
}

pub fn dm_cache_metadata_abort(fix: &mut Fixture, cmd: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.call_with_errno("dm_cache_metadata_abort")
}

#[derive(Clone, Debug)]
pub struct CacheMapping {
    pub cblock: u64,
    pub oblock: u64,
    pub dirty: bool,
    pub hint: Option<u32>,
}

pub fn dm_cache_load_mappings(fix: &mut Fixture, cmd: Addr) -> Result<Vec<CacheMapping>> {
    let (mut fix, callback_ptr) = auto_ebreak(fix)?;

    type Mappings = Vec<CacheMapping>;
    let mappings: Mappings = Vec::new();
    fix.contexts.insert(callback_ptr, mappings);

    let callback = move |fix: &mut Fixture| {
        let _context = fix.vm.reg(A0);
        let oblock = fix.vm.reg(A1);
        let cblock = fix.vm.reg(A2);
        let dirty = fix.vm.reg(A3);
        let hint = fix.vm.reg(A4) as u32;
        let hint_valid = fix.vm.reg(A5);

        let dirty = if dirty == 0 { false } else { true };
        let hint = if hint_valid == 0 { None } else { Some(hint) };

        {
            let mappings = fix.contexts.get_mut::<Mappings>(&callback_ptr).unwrap();
            mappings.push(CacheMapping {
                cblock,
                oblock,
                dirty,
                hint,
            });
        }
        fix.vm.ret(0);
        Ok(())
    };

    fix.bp_at_addr(callback_ptr, Arc::new(Mutex::new(callback)));

    fix.vm.set_reg(A0, cmd.0);

    // I want to keep the policy separate from the metadata tests.  So we
    // pass in a NULL policy ptr, and stub hints_array_available() which
    // is the only use of it.
    fix.vm.set_reg(A1, 0);
    fix.vm.set_reg(A2, callback_ptr.0);
    fix.stub("hints_array_available", 0)?;
    fix.vm.set_reg(A3, 0);

    fix.call_with_errno("dm_cache_load_mappings")?;

    let mappings = Box::into_inner(fix.contexts.remove::<Mappings>(&callback_ptr));
    Ok(mappings)
}

/*
pub fn dm_cache_load_discards(fix: &mut Fixture, cmd: Addr) -> Result<FixedBitSet> {
    let nr_dblocks = todo!();
    let discards: Box<RefCell<FixedBitSet>> = Box::new(FixedBitSet::with_capacity(nr_dblocks));

    let (mut fix, callback_ptr) = auto_ebreak(fix)?;
    fix.add_context(callback_ptr.0, discards);

    let callback = move |fix: &mut Fixture| {
        let _context = fix.vm.reg(A0);
        let _dblock_size = fix.vm.reg(A1);
        let dblock = fix.vm.reg(A2);
        let discarded = fix.vm.reg(A3);

        {
            let discards = fix.rm_context(&callback_ptr.0);
            let mut inner = discards
                .downcast_ref::<RefCell<Vec<CacheMapping>>>()
                .unwrap()
                .borrow_mut();
            inner.push(CacheMapping {
                cblock,
                oblock,
                dirty,
                hint,
            });
            drop(inner);
            fix.add_context(callback_ptr.0, mappings);
        }
        fix.vm.ret(0);
        Ok(())
    };

    fix.bp_at_addr(callback_ptr, Box::new(callback));

    fix.vm.set_reg(A0, cmd.0);

    // I want to keep the policy separate from the metadata tests.  So we
    // pass in a NULL policy ptr, and stub hints_array_available() which
    // is the only use of it.
    fix.vm.set_reg(A1, 0);
    fix.vm.set_reg(A2, callback_ptr.0);
    fix.stub("hints_array_available", 0)?;
    fix.vm.set_reg(A3, 0);

    fix.call_with_errno("dm_cache_load_mappings")?;

    let context = fix.rm_context(&callback_ptr.0);
    let mappings = context.downcast_ref::<RefCell<Vec<CacheMapping>>>().unwrap().borrow();

    // FIXME: redundant copy
    Ok(mappings.to_vec())
}
*/
/*
typedef int (*load_discard_fn)(void *context, sector_t discard_block_size,
                   dm_dblock_t dblock, bool discarded);
int dm_cache_load_discards(struct dm_cache_metadata *cmd,
               load_discard_fn fn, void *context);
*/

//-------------------------------
