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

pub fn dm_cache_set_dirty_bits(_fix: &mut Fixture, _cmd: Addr, _bits: &bit_set::BitSet) -> Result<()> {
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

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u32::<LittleEndian>(self.read_hits)?;
        w.write_u32::<LittleEndian>(self.read_misses)?;
        w.write_u32::<LittleEndian>(self.write_hits)?;
        w.write_u32::<LittleEndian>(self.write_misses)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let read_hits = r.read_u32::<LittleEndian>()?;
        let read_misses = r.read_u32::<LittleEndian>()?;
        let write_hits = r.read_u32::<LittleEndian>()?;
        let write_misses = r.read_u32::<LittleEndian>()?;
        Ok(CacheStats { read_hits, read_misses, write_hits, write_misses })
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
    let (mut fix, result_ptr) =
       auto_guest::<CacheStats>(fix, stats, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, result_ptr.0);

    fix.call_with_errno("dm_cache_metadata_set_stats")
}

pub fn dm_cache_commit(fix: &mut Fixture, cmd: Addr, clean_shutdown: bool) -> Result<()> {
    fix.vm.set_reg(A0, cmd.0);
    fix.vm.set_reg(A1, if clean_shutdown { 1 } else { 0} );
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
    Ok(if fix.vm.mem.read_into::<u32>(result_ptr, PERM_READ)? == 0 { false } else { true })
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

/*
typedef int (*load_discard_fn)(void *context, sector_t discard_block_size,
                   dm_dblock_t dblock, bool discarded);
int dm_cache_load_discards(struct dm_cache_metadata *cmd,
               load_discard_fn fn, void *context);

typedef int (*load_mapping_fn)(void *context, dm_oblock_t oblock,
                   dm_cblock_t cblock, bool dirty,
                   uint32_t hint, bool hint_valid);
int dm_cache_load_mappings(struct dm_cache_metadata *cmd,
               struct dm_cache_policy *policy,
               load_mapping_fn fn,
               void *context);
*/

//-------------------------------
