use std::result;

/// An address used within the guest.
pub struct Addr(u32);

/// Indicates memory errors such as referencing unallocated memory.  Or bad permissions.
pub enum MemErr {
    BadPerms(Addr, u8),
    OutOfBounds,
}

pub type Result<T> = result::Result<T, MemErr>;

pub const PERM_READ: u8 = 1;
pub const PERM_WRITE: u8 = 1 << 1;
pub const PERM_EXEC: u8 = 1 << 2;
pub const PERM_WRITTEN: u8 = 1 << 3;

/// Manages memory for the vm.  Tracks permissions at the byte level.
/// Checks memory has been initialised before it's read.
pub struct Memory {
    perms: Vec<u8>,
    mem: Vec<u8>,
}

// FIXME: implement snapshotting.
impl Memory {
    pub fn new(len: u32) -> Self {
        Memory {
            perms: vec![0u8; len as usize],
            mem: vec![0u8; len as usize],
        }
    }

    /// Overwrites the perms for the address range.
    pub fn set_perms(&mut self, start: &Addr, len: u32, perms: u8) -> Result<()> {
        for b in start.0..(start.0 + len) {
            self.perms[b as usize] = perms;
        }

        Ok(())
    }

    /// Or's in the perms.
    pub fn add_perms(&mut self, start: &Addr, len: u32, perms: u8) -> Result<()> {
        for b in start.0..(start.0 + len) {
            self.perms[b as usize] |= perms;
        }

        Ok(())
    }

    /// Confirms that all the bits in 'perm' are set for every byte
    /// in the given range.
    pub fn check_perms(&self, start: &Addr, len: u32, perm: u8) -> Result<()> {
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
    pub fn read(&self, start: &Addr, len: u32, perm: u8) -> Result<&[u8]> {
        self.check_perms(start, len, perm)?;
        Ok(&self.mem[(start.0 as usize)..((start.0 + len) as usize)])
    }

    //// Writes bytes to a memory range.  Fails in the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn write(&mut self, start: &Addr, bytes: &[u8], perm: u8) -> Result<()> {
        self.check_perms(start, bytes.len() as u32, perm)?;
        self.mem[(start.0 as usize)..((start.0 + bytes.len() as u32) as usize)].copy_from_slice(bytes);

        // FIXME: checking perms and adding in the WRITTEN flag could be
        // done in a single pass.  Alternatively wait until we're using
        // page level perms.
        self.add_perms(start, bytes.len() as u32, PERM_WRITTEN)
    }
}

