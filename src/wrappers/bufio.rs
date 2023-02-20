use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};

use Reg::*;

//-------------------------------

pub struct ListHead {
    pub next: Addr,
    pub prev: Addr,
}

impl Default for ListHead {
    fn default() -> Self {
        Self {
            next: Addr(0),
            prev: Addr(0),
        }
    }
}

impl Guest for ListHead {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.next.0)?;
        w.write_u64::<LittleEndian>(self.prev.0)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let next = Addr(r.read_u64::<LittleEndian>()?);
        let prev = Addr(r.read_u64::<LittleEndian>()?);

        Ok(ListHead { next, prev })
    }
}

pub struct LruEntry {
    pub list: ListHead,
    pub referenced: u32,
}

impl Default for LruEntry {
    fn default() -> Self {
        Self {
            list: ListHead::default(),
            referenced: 0,
        }
    }
}

impl Guest for LruEntry {
    fn guest_len() -> usize {
        24
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        self.list.pack(w)?;
        w.write_u32::<LittleEndian>(self.referenced)?;
        w.write_u32::<LittleEndian>(0)?; // Padding
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let list = ListHead::unpack(r)?;
        let referenced = r.read_u32::<LittleEndian>()?;
        let _padding = r.read_u32::<LittleEndian>()?;

        Ok(LruEntry { list, referenced })
    }
}

pub struct Lru {
    pub cursor: Addr,
    pub count: u64,
}

impl Default for Lru {
    fn default() -> Self {
        Self {
            cursor: Addr(0),
            count: 0,
        }
    }
}

impl Guest for Lru {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.cursor.0)?;
        w.write_u64::<LittleEndian>(self.count)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let cursor = Addr(r.read_u64::<LittleEndian>()?);
        let count = r.read_u64::<LittleEndian>()?;
        Ok(Self { cursor, count })
    }
}

pub fn lru_init(fix: &mut Fixture, lru: Addr) -> Result<()> {
    fix.vm.set_reg(A0, lru.0);
    fix.call("lru_init")?;
    Ok(())
}

pub fn lru_exit(fix: &mut Fixture, lru: Addr) -> Result<()> {
    fix.vm.set_reg(A0, lru.0);
    fix.call("lru_destroy")?;
    Ok(())
}

// This is a trivial function that gets inlined.  Instead of
// calling the C version we read the lru structure from the
// guest and access the count field.
pub fn lru_count(fix: &mut Fixture, lru: Addr) -> Result<u64> {
    let lru = read_guest::<Lru>(&fix.vm.mem, lru)?;
    Ok(lru.count)
}

pub fn lru_insert(fix: &mut Fixture, lru: Addr, entry: Addr) -> Result<()> {
    fix.vm.set_reg(A0, lru.0);
    fix.vm.set_reg(A1, entry.0);
    fix.call("lru_insert")?;
    Ok(())
}

pub fn lru_remove(fix: &mut Fixture, lru: Addr, entry: Addr) -> Result<()> {
    fix.vm.set_reg(A0, lru.0);
    fix.vm.set_reg(A1, entry.0);
    fix.call("lru_insert")?;
    Ok(())
}

pub fn lru_reference(fix: &mut Fixture, entry: Addr) -> Result<()> {
    fix.vm.set_reg(A0, entry.0);
    fix.call("lru_reference")?;
    Ok(())
}

pub fn lru_evict(fix: &mut Fixture, lru: Addr, pred: Addr, context: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, lru.0);
    fix.vm.set_reg(A1, pred.0);
    fix.vm.set_reg(A2, context.0);
    fix.call("lru_evict")?;
    Ok(Addr(fix.vm.reg(A0)))
}

//-------------------------------

pub struct Buffer {
    pub lru: LruEntry,
    pub block: u64,
    pub hold_count: u32,
    pub last_accessed: u64,
    pub list_mode: LruKind,
}

impl Guest for Buffer {
    fn guest_len() -> usize {
        152
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        self.lru.pack(w)?;
        w.write_u64::<LittleEndian>(self.block)?;
        w.write_all(&[0; 40])?;
        w.write_u32::<LittleEndian>(self.hold_count)?;
        w.write_u64::<LittleEndian>(self.last_accessed)?;
        w.write_u8(encode_kind(self.list_mode) as u8)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let lru = LruEntry::unpack(r)?;
        let block = r.read_u64::<LittleEndian>()?;
        r.read_exact(&mut [0; 40])?;
        let hold_count = r.read_u32::<LittleEndian>()?;
        let last_accessed = r.read_u64::<LittleEndian>()?;
        let list_mode = r.read_u8()?;

        Ok(Self {
            lru,
            block,
            hold_count,
            last_accessed,
            list_mode: if list_mode == 0 {
                LruKind::Clean
            } else {
                LruKind::Dirty
            },
        })
    }
}

//-------------------------------

pub const BUFFER_CACHE_SIZE: usize = 4640;

#[derive(Clone, Copy)]
pub enum LruKind {
    Clean,
    Dirty,
}

pub const LIST_CLEAN: u64 = 0;
pub const LIST_DIRTY: u64 = 1;

pub fn encode_kind(k: LruKind) -> u64 {
    use LruKind::*;

    match k {
        Clean => LIST_CLEAN,
        Dirty => LIST_DIRTY,
    }
}

pub fn cache_init(fix: &mut Fixture, cache: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.call("cache_init")?;
    Ok(())
}

pub fn cache_exit(fix: &mut Fixture, cache: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.call("cache_destroy")?;
    Ok(())
}

pub fn cache_count(fix: &mut Fixture, cache: Addr, k: LruKind) -> Result<usize> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, encode_kind(k));
    fix.call("cache_count")?;
    Ok(fix.vm.reg(A0) as usize)
}

pub fn cache_total(fix: &mut Fixture, cache: Addr) -> Result<usize> {
    fix.vm.set_reg(A0, cache.0);
    fix.call("cache_total")?;
    Ok(fix.vm.reg(A0) as usize)
}

pub fn cache_get(fix: &mut Fixture, cache: Addr, block: u64) -> Result<Addr> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, block);
    fix.call("cache_get")?;
    Ok(Addr(fix.vm.reg(A0)))
}

pub fn cache_find(
    fix: &mut Fixture,
    cache: Addr,
    k: LruKind,
    pred: Addr,
    context: Addr,
) -> Result<Addr> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, encode_kind(k));
    fix.vm.set_reg(A2, pred.0);
    fix.vm.set_reg(A3, context.0);

    fix.call("cache_find")?;

    Ok(Addr(fix.vm.reg(A0)))
}

pub fn cache_put(fix: &mut Fixture, cache: Addr, b: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, b.0);

    fix.call("cache_put")?;

    Ok(())
}

pub fn cache_evict(
    fix: &mut Fixture,
    cache: Addr,
    k: LruKind,
    pred: Addr,
    context: Addr,
) -> Result<Addr> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, encode_kind(k));
    fix.vm.set_reg(A2, pred.0);
    fix.vm.set_reg(A3, context.0);

    fix.call("cache_evict")?;

    Ok(Addr(fix.vm.reg(A0)))
}

pub fn cache_mark(fix: &mut Fixture, cache: Addr, b: Addr, k: LruKind) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, b.0);
    fix.vm.set_reg(A2, encode_kind(k));

    fix.call("cache_mark")?;

    Ok(())
}

pub fn cache_mark_many(
    fix: &mut Fixture,
    cache: Addr,
    old_k: LruKind,
    new_k: LruKind,
    pred: Addr,
    context: Addr,
) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, encode_kind(old_k));
    fix.vm.set_reg(A2, encode_kind(new_k));
    fix.vm.set_reg(A3, pred.0);
    fix.vm.set_reg(A4, context.0);

    fix.call("cache_mark_many")?;

    Ok(())
}

pub fn cache_iterate(
    fix: &mut Fixture,
    cache: Addr,
    k: LruKind,
    iter_fn: Addr,
    context: Addr,
) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, encode_kind(k));
    fix.vm.set_reg(A2, iter_fn.0);
    fix.vm.set_reg(A3, context.0);

    fix.call("cache_iterate")?;

    Ok(())
}

pub fn cache_insert(fix: &mut Fixture, cache: Addr, b: Addr) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, b.0);

    fix.call("cache_insert")?;

    Ok(())
}

pub fn cache_remove(fix: &mut Fixture, cache: Addr, b: Addr) -> Result<bool> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, b.0);

    fix.call("cache_remove")?;

    Ok(fix.vm.reg(A0) != 0)
}

pub fn cache_remove_range(
    fix: &mut Fixture,
    cache: Addr,
    b: u64,
    e: u64,
    pred: Addr,
    release: Addr,
) -> Result<()> {
    fix.vm.set_reg(A0, cache.0);
    fix.vm.set_reg(A1, b);
    fix.vm.set_reg(A2, e);
    fix.vm.set_reg(A3, pred.0);
    fix.vm.set_reg(A4, release.0);

    fix.call("cache_remove_range")?;

    Ok(())
}

//-------------------------------
