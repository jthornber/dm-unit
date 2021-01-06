use std::fmt;
use std::result;
use thiserror::Error;

use crate::primitive::Primitive;

/// An address used within the guest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Addr(pub u64);

impl fmt::LowerHex for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.0;
        fmt::LowerHex::fmt(&val, f)
    }
}

/// Indicates memory errors such as referencing unallocated memory.  Or bad permissions.
#[derive(Error, Debug)]
pub enum MemErr {
    #[error("Bad memory permissions at {0:?}, wanted {1}")]
    BadPerms(Addr, u8),

    #[error("Address out of bounds")]
    OutOfBounds,

    #[error("Unable to allocate enough space")]
    OutOfSpace,
}

pub type Result<T> = result::Result<T, MemErr>;

// FIXME: use an enum, or bitset or something
pub const PERM_READ: u8 = 1;
pub const PERM_WRITE: u8 = 1 << 1;
pub const PERM_EXEC: u8 = 1 << 2;
pub const PERM_WRITTEN: u8 = 1 << 3;   // FIXME: this is more of a flag than a perm

/// Manages memory for the vm.  Tracks permissions at the byte level.
/// Checks memory has been initialised before it's read.
pub struct Memory {
    perms: Vec<u8>,
    mem: Vec<u8>,
}

// FIXME: implement snapshotting.
impl Memory {
    pub fn new(len: u64) -> Self {
        Memory {
            perms: vec![0u8; len as usize],
            mem: vec![0u8; len as usize],
        }
    }

    pub fn len(&self) -> u64 {
        self.mem.len() as u64
    }

    /// Overwrites the perms for the address range.
    pub fn set_perms(&mut self, start: Addr, len: u64, perms: u8) -> Result<()> {
        for b in start.0..(start.0 + len) {
            self.perms[b as usize] = perms;
        }

        Ok(())
    }

    /// Or's in the perms.
    pub fn add_perms(&mut self, start: Addr, len: u64, perms: u8) -> Result<()> {
        for b in start.0..(start.0 + len) {
            self.perms[b as usize] |= perms;
        }

        Ok(())
    }

    /// Confirms that all the bits in 'perm' are set for every byte
    /// in the given range.
    pub fn check_perms(&self, start: Addr, len: u64, perm: u8) -> Result<()> {
        let end = start.0.checked_add(len);
        if end.is_none() {
            return Err(MemErr::OutOfBounds);
        }

        for b in start.0..(start.0 + len) {
            if (self.perms[b as usize] & perm) != perm {
                return Err(MemErr::BadPerms(Addr(b), perm));
            }
        }
        Ok(())
    }

    /// Reads bytes from a memory range.  Fails if the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn read(&self, start: Addr, bytes: &mut [u8], perm: u8) -> Result<()> {
        self.check_perms(start, bytes.len() as u64, perm)?;
        bytes.copy_from_slice(
            &self.mem[(start.0 as usize)..((start.0 + bytes.len() as u64) as usize)],
        );
        Ok(())
    }

    /// Writes bytes to a memory range.  Fails in the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn write(&mut self, start: Addr, bytes: &[u8], perm: u8) -> Result<()> {
        self.check_perms(start, bytes.len() as u64, perm)?;
        self.mem[(start.0 as usize)..((start.0 + bytes.len() as u64) as usize)]
            .copy_from_slice(bytes);

        // FIXME: checking perms and adding in the WRITTEN flag could be
        // done in a single pass.  Alternatively wait until we're using
        // page level perms.
        self.add_perms(start, bytes.len() as u64, PERM_WRITTEN)
    }

    /// Accesses a primitive, loc must be 4 byte aligned.  `perm` checked.
    pub fn read_into<T: Primitive>(&mut self, loc: Addr, perm: u8) -> Result<T> {
        let mut dest = [0u8; 16];
        self.read(loc, &mut dest[..::core::mem::size_of::<T>()], perm)?;

        Ok(unsafe { core::ptr::read_unaligned(dest.as_ptr() as *const T) })
    }

/*
    fn find_free(&mut self, size: u64, align: u64) -> Result<Addr> {
        let mut i = 0;
        'outer: loop {
            if i > self.mem.len() {
                break;
            }
            
            if self.perms[i] == 0 {
                // make sure we're aligned.
                
                // see if the block is big enough
                
                
                

            } else {
                i = i + 1;
            }
        }

        Err(MemErr::OutOfSpace)
    }
    
    /// Alloc searches for a block of memory that doesn't have any perms set.
    /// This is very inefficiently implemented atm.   
    pub fn alloc(&mut self, size: u64, align: u64, perm: u8) -> Result<Addr> {
        let ptr = self.find_free(size, align)?;
        self.set_perms(ptr, size, perm);
        Ok(ptr)
    }
    */
}
