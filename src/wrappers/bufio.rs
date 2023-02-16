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
