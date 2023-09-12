use crate::emulator::memory::*;
use crate::emulator::memory::{Addr, PERM_READ};

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Cursor, Read, Write};

//-------------------------------

// FIXME: use read_some rather than copying all the time

// Guest types must always consume the same amount of contiguous guest
// memory.
pub trait Guest {
    fn guest_len() -> usize;
    fn pack<W: Write>(&self, w: &mut W, loc: Addr) -> io::Result<()>;
    fn unpack<R: Read>(r: &mut R) -> io::Result<Self>
    where
        Self: std::marker::Sized;
}

// Allocates space on the guest and copies 'bytes' into it.
pub fn alloc_guest<G: Guest>(mem: &mut Memory, v: &G, perms: u8) -> Result<Addr> {
    let ptr = mem.alloc_with(G::guest_len(), perms, |ptr: Addr, bytes: &mut [u8]| {
        let mut w = Cursor::new(bytes);
        v.pack(&mut w, ptr).map_err(|_| MemErr::OutOfBounds {})?;
        Ok(())
    })?;

    Ok(ptr)
}

// Copies data from the guest to host.
pub fn read_guest<G: Guest>(mem: &Memory, ptr: Addr) -> Result<G> {
    let len = G::guest_len();
    let mut bytes = vec![0; len];
    mem.read(ptr, &mut bytes, PERM_READ)?;
    let mut r = Cursor::new(&bytes);
    let v = G::unpack(&mut r)?;
    Ok(v)
}

/// Copies data from host to guest
pub fn write_guest<G: Guest>(mem: &mut Memory, ptr: Addr, v: &G) -> Result<()> {
    let mut bytes = vec![0; G::guest_len()];
    let mut w = Cursor::new(&mut bytes);
    v.pack(&mut w, ptr)?;
    mem.write(ptr, &bytes, 0)?;
    Ok(())
}

// Reads and frees a guest value.
pub fn free_guest<G: Guest>(mem: &mut Memory, ptr: Addr) -> Result<G> {
    let v = read_guest(mem, ptr)?;
    mem.free(ptr)?;
    Ok(v)
}

impl Guest for u64 {
    fn guest_len() -> usize {
        8
    }

    fn pack<W: Write>(&self, w: &mut W, _loc: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(*self)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        r.read_u64::<LittleEndian>()
    }
}

//-------------------------------
