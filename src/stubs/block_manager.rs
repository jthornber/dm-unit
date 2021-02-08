use crate::decode::Reg;
use crate::fixture::*;
use crate::memory::*;
use crate::memory::{Addr, PERM_READ, PERM_WRITE};

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use crc32c::crc32c;
use log::{info, warn};
use std::collections::BTreeMap;
use std::io;
use std::io::{Read, Write};

use Reg::*;

//-------------------------------

struct GBlock {
    bm: Addr,
    loc: u64,
    data: Vec<u8>,
}

impl Guest for GBlock {
    fn guest_len() -> usize {
        8 + 8 + 4096
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        // I'm only supporting 4k blocks atm, since that's all we use.
        assert!(self.data.len() == 4096);

        w.write_u64::<LittleEndian>(self.bm.0)?;
        w.write_u64::<LittleEndian>(self.loc)?;
        w.write_all(&self.data)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let bm = Addr(r.read_u64::<LittleEndian>()?);
        let loc = r.read_u64::<LittleEndian>()?;
        let mut data = vec![0; 4096];
        r.read_exact(&mut data)?;

        Ok(GBlock { bm, loc, data })
    }
}

enum BlockData {
    Host(Vec<u8>),
    ExclusiveGuest(Addr),
    SharedGuest(Addr, u32),
}

#[allow(dead_code)]
struct Block {
    bm: Addr,
    loc: u64,
    block_size: u64,
    dirty: bool,
    data: BlockData,
}

impl Block {
    fn new(bm: Addr, loc: u64, block_size: u64) -> Self {
        Block {
            bm,
            loc,
            block_size,
            dirty: false,
            data: BlockData::Host(vec![0; block_size as usize]),
        }
    }

    // Data must be on the host
    fn zero(&mut self) -> Result<()> {
        use BlockData::*;
        match &mut self.data {
            Host(bytes) => {
                for b in bytes {
                    *b = 0u8;
                }
            }
            _ => {
                return Err(anyhow!("can't zero a held block"));
            }
        }
        Ok(())
    }

    fn to_shared(&mut self, mem: &mut Memory) -> Result<Addr> {
        use BlockData::*;
        let g_ptr = match &mut self.data {
            Host(bytes) => {
                let gb = GBlock {
                    bm: self.bm,
                    loc: self.loc,
                    data: bytes.clone(),
                };
                let g_ptr = alloc_guest(mem, &gb, PERM_READ)?;
                self.data = SharedGuest(g_ptr, 1);
                g_ptr
            }
            SharedGuest(g_ptr, count) => {
                *count += 1;
                *g_ptr
            }
            ExclusiveGuest(_) => {
                return Err(anyhow!(
                    "Request to read lock block when it is already write locked"
                ));
            }
        };

        Ok(g_ptr)
    }

    fn to_exclusive(&mut self, mem: &mut Memory) -> Result<Addr> {
        use BlockData::*;
        match &mut self.data {
            Host(bytes) => {
                let gb = GBlock {
                    bm: self.bm,
                    loc: self.loc,
                    data: bytes.clone(),
                };
                let g_ptr = alloc_guest(mem, &gb, PERM_READ | PERM_WRITE)?;
                self.dirty = true;
                self.data = ExclusiveGuest(g_ptr);
                Ok(g_ptr)
            }
            _ => Err(anyhow!("Requenst to write lock a block when already held")),
        }
    }

    fn unlock(&mut self, mem: &mut Memory) -> Result<()> {
        use BlockData::*;
        match &mut self.data {
            Host(_bytes) => Err(anyhow!(
                "request to unlock block {}, but it is not locked.",
                self.loc
            )),
            SharedGuest(g_ptr, count) if *count == 1 => {
                let gb = free_guest::<GBlock>(mem, *g_ptr)?;
                self.data = Host(gb.data);
                Ok(())
            }
            SharedGuest(_g_ptr, count) => {
                *count -= 1;
                Ok(())
            }
            ExclusiveGuest(g_ptr) => {
                let gb = free_guest::<GBlock>(mem, *g_ptr)?;
                self.data = Host(gb.data);
                Ok(())
            }
        }
    }
}

#[allow(dead_code)]
pub struct BlockManager {
    block_size: u64,
    nr_blocks: u64,
    blocks: BTreeMap<u64, Block>,
    read_only: bool,

    nr_read_locks: u64,
    nr_write_locks: u64,
}

pub fn bm_create(fix: &mut Fixture) -> Result<()> {
    let bdev_ptr = fix.vm.reg(A0);
    let block_size = fix.vm.reg(A1);
    let _max_held_per_thread = fix.vm.reg(A2);

    let nr_blocks = fix.vm.mem.read_into::<u64>(Addr(bdev_ptr), PERM_READ)?;

    let bm = Box::new(BlockManager {
        block_size,
        nr_blocks,
        blocks: BTreeMap::new(),
        read_only: false,
        nr_read_locks: 0,
        nr_write_locks: 0,
    });

    let guest_addr = fix.vm.mem.alloc(4)?;
    fix.user_data.insert(guest_addr, bm);

    fix.vm.ret(guest_addr.0);
    Ok(())
}

pub fn bm_destroy(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.remove::<BlockManager>(Addr(bm_ptr))?;

    info!(
        "bm: nr_blocks = {}, nr_read_locks = {}, nr_write_locks = {}",
        bm.blocks.len(),
        bm.nr_read_locks,
        bm.nr_write_locks,
    );

    let mut held = false;
    for (index, b) in &bm.blocks {
        use BlockData::*;
        match b.data {
            ExclusiveGuest(_) => {
                warn!("Block {} still held", index);
                held = true;
            }
            SharedGuest(_, _) => {
                warn!("Block {} still held", index);
                held = true;
            }
            _ => {}
        }
    }

    if held {
        return Err(anyhow!(
            "dm_block_manager_destroy() called with blocks still held"
        ));
    }

    fix.vm.mem.free(Addr(bm_ptr))?;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_block_size(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let block_size = {
        let bm = fix.user_data.get_ref::<BlockManager>(bm_ptr)?;
        bm.block_size
    };
    fix.vm.ret(block_size);
    Ok(())
}

pub fn bm_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let nr_blocks = {
        let bm = fix.user_data.get_ref::<BlockManager>(bm_ptr)?;
        bm.nr_blocks
    };
    fix.vm.ret(nr_blocks);
    Ok(())
}

pub fn bm_read_lock(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let b = fix.vm.reg(A1);
    let _v_ptr = fix.vm.reg(A2);
    let result_ptr = fix.vm.reg(A3);

    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    let guest_addr = match bm.blocks.get_mut(&b) {
        Some(block) => block.to_shared(&mut fix.vm.mem)?,
        None => {
            let mut block = Block::new(Addr(bm_ptr), b, bm.block_size);
            let guest_addr = block.to_shared(&mut fix.vm.mem)?;
            bm.blocks.insert(b, block);
            guest_addr
        }
    };

    // fill out result ptr
    fix.vm
        .mem
        .write(Addr(result_ptr), &guest_addr.0.to_le_bytes(), PERM_WRITE)?;

    // return success
    bm.nr_read_locks += 1;
    fix.vm.ret(0);
    Ok(())
}

fn write_lock_(fix: &mut Fixture, zero: bool) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let b = fix.vm.reg(A1);
    let _v_ptr = fix.vm.reg(A2);
    let result_ptr = fix.vm.reg(A3);

    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;

    let guest_addr: Addr = if zero {
        match bm.blocks.get_mut(&b) {
            Some(block) => {
                block.zero()?;
                block.to_exclusive(&mut fix.vm.mem)?
            }
            None => {
                let mut block = Block::new(Addr(bm_ptr), b, bm.block_size);
                block.zero()?;
                let guest_addr = block.to_exclusive(&mut fix.vm.mem)?;
                bm.blocks.insert(b, block);
                guest_addr
            }
        }
    } else {
        match bm.blocks.get_mut(&b) {
            Some(block) => block.to_exclusive(&mut fix.vm.mem)?,
            None => {
                let mut block = Block::new(Addr(bm_ptr), b, bm.block_size);
                let guest_addr = block.to_exclusive(&mut fix.vm.mem)?;
                bm.blocks.insert(b, block);
                guest_addr
            }
        }
    };

    // fill out result ptr
    fix.vm
        .mem
        .write(Addr(result_ptr), &guest_addr.0.to_le_bytes(), PERM_WRITE)?;

    // return success
    bm.nr_write_locks += 1;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_write_lock(fix: &mut Fixture) -> Result<()> {
    write_lock_(fix, false)
}

pub fn bm_write_lock_zero(fix: &mut Fixture) -> Result<()> {
    write_lock_(fix, true)
}

pub fn bm_unlock(fix: &mut Fixture) -> Result<()> {
    let block_ptr = fix.vm.reg(A0);

    // FIXME: we unpack gb twice, once here, and once as part of the unlock op.
    let gb = read_guest::<GBlock>(&mut fix.vm.mem, Addr(block_ptr))?;
    let bm = fix.user_data.get_mut::<BlockManager>(gb.bm)?;
    match bm.blocks.get_mut(&gb.loc) {
        Some(b) => {
            b.unlock(&mut fix.vm.mem)?;
        }
        None => {
            return Err(anyhow!(
                "unable to find block {}, it has never been locked",
                gb.loc
            ));
        }
    }

    fix.vm.ret(0);
    Ok(())
}

pub fn bm_block_location(fix: &mut Fixture) -> Result<()> {
    let block_ptr = fix.vm.reg(A0);
    // FIXME: this needlessly copies the data across.
    let gb = read_guest::<GBlock>(&mut fix.vm.mem, Addr(block_ptr))?;
    fix.vm.ret(gb.loc);
    Ok(())
}

pub fn bm_block_data(fix: &mut Fixture) -> Result<()> {
    let block_ptr = fix.vm.reg(A0);
    fix.vm.ret(block_ptr + 16);
    Ok(())
}

pub fn bm_flush(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;

    // Run through the blocks, clearing the dirty flags on those that
    // aren't held.  This would be a good place to put a journal so we
    // can double check transactionality.
    use BlockData::*;
    for (_, b) in &mut bm.blocks {
        match b {
            Block {
                dirty,
                data: Host(_),
                ..
            } => {
                *dirty = false;
            }
            _ => {
                // Noop
            }
        }
    }

    fix.vm.ret(0);
    Ok(())
}

// Our prefetch does nothing
pub fn bm_prefetch(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let _bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    let _loc = fix.vm.reg(A1);

    fix.vm.ret(0);
    Ok(())
}

pub fn bm_is_read_only(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    let result = if bm.read_only { 1 } else { 0 };
    fix.vm.ret(result);
    Ok(())
}

pub fn bm_set_read_only(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    bm.read_only = true;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_set_read_write(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    bm.read_only = false;
    fix.vm.ret(0);
    Ok(())
}

pub fn bm_checksum(fix: &mut Fixture) -> Result<()> {
    let data = Addr(fix.vm.reg(A0));
    let len = fix.vm.reg(A1);
    let init_xor = fix.vm.reg(A2) as u32;

    let mut buf = vec![0u8; len as usize];
    fix.vm.mem.read(data, &mut buf, PERM_READ)?;
    let mut csum = crc32c(&buf) ^ 0xffffffff;
    csum ^= init_xor;

    fix.vm.ret(csum as u64);
    Ok(())
}

//-------------------------------
