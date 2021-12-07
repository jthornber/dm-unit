use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::OpenOptions;
use std::io;
use std::io::Seek;
use std::io::{Read, Write};
use std::path::Path;
use std::sync::Mutex;
use thinp::io_engine;
use thinp::io_engine::{IoEngine, BLOCK_SIZE};
use thiserror::Error;

use crate::emulator::memory;
use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::emulator::vm::*;
use crate::fixture::*;
use crate::guest::*;
use crate::snapshot::Snapshot;

//-------------------------------

// We need to be able to differentiate between a serious error, such
// as bad memory access, and something that the client code can handle,
// such as index out of bounds.
#[derive(Error, Debug)]
pub enum BMError {
    #[error("memory error")]
    MemErr(memory::MemErr),

    #[error("bad arg")]
    BadArg(String),

    #[error("validator mismatch")]
    ValidatorMismatch,

    #[error("validator check failed")]
    ValidatorCheckFailed,

    #[error("validator prep failed")]
    ValidatorPrepFailed,

    #[error("block out of bounds")]
    BlockOutOfBounds(u64),

    #[error("vm error")]
    VMErr,

    #[error("unflushed data")]
    UnflushedData,

    #[error("bad lock operation")]
    BadLock(u64),

    #[error("IO error")]
    IoErr(std::io::Error),
}

pub type Result<T> = core::result::Result<T, BMError>;

//-------------------------------

#[allow(dead_code)]
#[derive(Clone)]
struct Validator {
    name: Addr,
    prepare: Addr,
    check: Addr,
}

impl Guest for Validator {
    fn guest_len() -> usize {
        24
    }

    fn pack<W: Write>(&self, _w: &mut W, _ptr: Addr) -> io::Result<()> {
        todo!();
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let name = Addr(r.read_u64::<LittleEndian>()?);
        let prepare = Addr(r.read_u64::<LittleEndian>()?);
        let check = Addr(r.read_u64::<LittleEndian>()?);

        Ok(Validator {
            name,
            prepare,
            check,
        })
    }
}

//-------------------------------

#[derive(Clone)]
pub struct GBlock {
    pub bm_ptr: Addr,
    pub loc: u64,

    // We hold the data in a separate allocation so the same Vec can be
    // bounced between the host and guest.
    pub data: Addr,
}

impl Guest for GBlock {
    fn guest_len() -> usize {
        24
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.bm_ptr.0)?;
        w.write_u64::<LittleEndian>(self.loc)?;
        w.write_u64::<LittleEndian>(self.data.0)
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let bm_ptr = Addr(r.read_u64::<LittleEndian>()?);
        let loc = r.read_u64::<LittleEndian>()?;
        let data = Addr(r.read_u64::<LittleEndian>()?);

        Ok(GBlock { bm_ptr, loc, data })
    }
}

//-------------------------------

#[derive(Clone)]
pub enum Lock {
    // Locked for read, the block may be dirty from a prior write.
    Read {
        dirty: bool,
        validator: Addr,
        count: usize,
        guest_ptr: Addr,
    },

    // Locked for write, obviously dirty.
    Write {
        validator: Addr,
        guest_ptr: Addr,
    },

    // Dirty data is not locked, but still resides in the guest.
    Dirty {
        validator: Addr,
        guest_ptr: Addr,
    },

    // Clean data is moved back to the host.
    Clean {
        // indicates whether the block is in memory, or just on disk
        resident: bool,
        validator: Addr,
        data: Vec<u8>,
    },
}

#[derive(Clone)]
pub struct BMInner {
    bm_ptr: Addr,
    nr_blocks: u64,
    locks: BTreeMap<u64, Lock>,
    dirty: BTreeSet<u64>,

    pub nr_read_locks: u64,
    pub nr_write_locks: u64,
    pub nr_prepares: u64,
    pub nr_disk_reads: u64,
}

impl BMInner {
    fn new(nr_blocks: u64, bm_ptr: Addr) -> Self {
        BMInner {
            bm_ptr,
            nr_blocks,
            locks: BTreeMap::new(),
            dirty: BTreeSet::new(),
            nr_read_locks: 0,
            nr_write_locks: 0,
            nr_prepares: 0,
            nr_disk_reads: 0,
        }
    }

    fn need_validate(&self, v1: Addr, v2: Addr) -> Result<bool> {
        match (v1.0, v2.0) {
            (0, 0) => Ok(false),
            (0, _) => Ok(true),
            (l, 0) => {
                debug!("validator mismatch 0x{:x} -> 0x0", l);
                Err(BMError::ValidatorMismatch)
            }
            (l, r) => {
                if l != r {
                    debug!("validator mismatch, 0x{:x} -> 0x{:x}", l, r);
                    Err(BMError::ValidatorMismatch)
                } else {
                    Ok(false)
                }
            }
        }
    }

    fn v_check(&self, fix: &mut Fixture, guest_ptr: Addr, v_ptr: Addr) -> Result<()> {
        use Reg::*;

        if v_ptr.is_null() {
            return Ok(());
        }

        // Call the prep function in the guest
        fix.vm.set_reg(A0, v_ptr.0);
        fix.vm.set_reg(A1, guest_ptr.0);
        fix.vm.set_reg(A2, 4096);

        let v = read_guest::<Validator>(&fix.vm.mem, v_ptr).map_err(|e| BMError::MemErr(e))?;

        if v.check.is_null() {
            return Ok(());
        }
        fix.call_at(v.check).map_err(|e| BMError::VMErr)?;

        match fix.vm.reg(A0) as i64 as i32 {
            // r if r < 0 => Err(anyhow!("validator check failed: {}", error_string(-r))),
            r if r != 0 => Err(BMError::ValidatorCheckFailed),
            _ => Ok(()),
        }
    }

    fn check_bounds(&self, loc: u64) -> Result<()> {
        if loc < self.nr_blocks {
            Ok(())
        } else {
            Err(BMError::BlockOutOfBounds(loc))
        }
    }

    fn check_bounds_io(&self, loc: u64) -> io::Result<()> {
        if loc < self.nr_blocks {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "block out of bounds".to_string(),
            ))
        }
    }

    fn v_prep(&mut self, fix: &mut Fixture, guest_ptr: Addr, v_ptr: Addr) -> Result<()> {
        use Reg::*;

        if v_ptr.is_null() {
            return Ok(());
        }

        // Call the prep function in the guest
        fix.vm.set_reg(A0, v_ptr.0);
        fix.vm.set_reg(A1, guest_ptr.0);
        fix.vm.set_reg(A2, 4096);

        let v = read_guest::<Validator>(&fix.vm.mem, v_ptr).map_err(|e| BMError::MemErr(e))?;
        if !v.prepare.is_null() {
            fix.call_at(v.prepare).map_err(|_| BMError::VMErr)?;
        }

        self.nr_prepares += 1;
        Ok(())
    }

    fn read_lock(&mut self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.check_bounds(loc)?;
        match self.locks.remove(&loc) {
            Some(Lock::Read {
                dirty,
                validator,
                count,
                guest_ptr,
            }) => {
                // Already read locked, just increment the reference count,
                // and return the previous guest ptr.
                if self.need_validate(validator, v_ptr)? {
                    self.v_check(fix, guest_ptr, v_ptr)?;
                }
                self.locks.insert(
                    loc,
                    Lock::Read {
                        dirty,
                        validator,
                        count: count + 1,
                        guest_ptr,
                    },
                );
                self.nr_read_locks += 1;
                Ok(guest_ptr)
            }
            Some(l @ Lock::Write { .. }) => {
                self.locks.insert(loc, l);
                Err(BMError::BadLock(loc))
            }
            Some(Lock::Dirty {
                validator,
                guest_ptr,
            }) => {
                let gb =
                    read_guest::<GBlock>(&fix.vm.mem, guest_ptr).map_err(|e| BMError::MemErr(e))?;
                fix.vm
                    .mem
                    .change_perms(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), PERM_READ)
                    .map_err(|e| BMError::MemErr(e))?;
                self.locks.insert(
                    loc,
                    Lock::Read {
                        dirty: true,
                        validator,
                        count: 1,
                        guest_ptr,
                    },
                );
                self.nr_read_locks += 1;
                Ok(guest_ptr)
            }
            Some(Lock::Clean {
                resident,
                validator,
                data,
            }) => {
                let data = fix
                    .vm
                    .mem
                    .alloc_aligned(data, PERM_READ, 4096)
                    .map_err(|e| BMError::MemErr(e))?;

                // Create guest ptr.
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)
                    .map_err(|e| BMError::MemErr(e))?;

                if self.need_validate(validator, v_ptr)? {
                    self.v_check(fix, guest_ptr, v_ptr)?;
                }

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Read {
                        dirty: false,
                        validator: v_ptr,
                        count: 1,
                        guest_ptr,
                    },
                );
                self.nr_read_locks += 1;
                if !resident {
                    self.nr_disk_reads += 1;
                }
                Ok(guest_ptr)
            }
            None => {
                // This block has never been touched, this should only
                // happen with the superblock, where we take all zeroes
                // to mean we want to format it.
                if loc != 0 {
                    return Err(BMError::BadLock(loc));
                }

                let data = fix
                    .vm
                    .mem
                    .alloc_aligned(vec![0; BLOCK_SIZE], PERM_READ, 4096)
                    .map_err(|e| BMError::MemErr(e))?;

                // Create guest ptr.
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)
                    .map_err(|e| BMError::MemErr(e))?;

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Read {
                        dirty: false,
                        validator: v_ptr,
                        count: 1,
                        guest_ptr,
                    },
                );
                self.nr_read_locks += 1;
                Ok(guest_ptr)
            }
        }
    }

    fn write_lock_(
        &mut self,
        fix: &mut Fixture,
        loc: u64,
        v_ptr: Addr,
        zero: bool,
    ) -> Result<Addr> {
        self.check_bounds(loc)?;
        match self.locks.remove(&loc) {
            Some(l @ Lock::Read { .. }) => {
                self.locks.insert(loc, l);
                Err(BMError::BlockOutOfBounds(loc))
            }
            Some(l @ Lock::Write { .. }) => {
                self.locks.insert(loc, l);
                Err(BMError::BadLock(loc))
            }
            Some(Lock::Dirty {
                validator,
                guest_ptr,
            }) => {
                if self.need_validate(validator, v_ptr)? {
                    self.v_check(fix, guest_ptr, v_ptr)?;
                }
                let gb = read_guest::<GBlock>(&mut fix.vm.mem, guest_ptr)
                    .map_err(|e| BMError::MemErr(e))?;
                fix.vm
                    .mem
                    .change_perms(
                        gb.data,
                        Addr(gb.data.0 + BLOCK_SIZE as u64),
                        PERM_READ | PERM_WRITE,
                    )
                    .map_err(|e| BMError::MemErr(e))?;

                if zero {
                    fix.vm
                        .mem
                        .zero(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), PERM_WRITE)
                        .map_err(|e| BMError::MemErr(e))?;
                }
                self.locks.insert(
                    loc,
                    Lock::Write {
                        validator,
                        guest_ptr,
                    },
                );
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
            Some(Lock::Clean {
                resident,
                validator: _maybe_validator,
                data,
            }) => {
                if zero {
                    unsafe {
                        std::ptr::write_bytes(data.as_ptr() as *mut u8, 0, BLOCK_SIZE);
                    }
                }

                // Create guest ptr.
                let data = fix
                    .vm
                    .mem
                    .alloc_aligned(data, PERM_READ | PERM_WRITE, 4096)
                    .map_err(|e| BMError::MemErr(e))?;
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)
                    .map_err(|e| BMError::MemErr(e))?;

                // insert lock
                // FIXME: check validator and maybe_validator are compatible
                self.locks.insert(
                    loc,
                    Lock::Write {
                        validator: v_ptr,
                        guest_ptr,
                    },
                );
                self.nr_write_locks += 1;
                if !resident {
                    self.nr_disk_reads += 1;
                }
                Ok(guest_ptr)
            }
            None => {
                // This block has never been touched, so the zero flag must be set.
                if !zero {
                    return Err(BMError::BadLock(loc));
                }

                // This block has never been touched, so we'll initialise
                // with zeroes.
                let data = fix
                    .vm
                    .mem
                    .alloc_aligned(vec![0; BLOCK_SIZE], PERM_READ | PERM_WRITE, 4096)
                    .map_err(|e| BMError::MemErr(e))?;

                // Create guest ptr.
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)
                    .map_err(|e| BMError::MemErr(e))?;

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Write {
                        validator: v_ptr,
                        guest_ptr,
                    },
                );
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
        }
    }

    fn write_lock(&mut self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.write_lock_(fix, loc, v_ptr, false)
    }

    fn write_lock_zero(&mut self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.write_lock_(fix, loc, v_ptr, true)
    }

    fn unlock(&mut self, fix: &mut Fixture, gb_ptr: Addr) -> Result<()> {
        let gb = read_guest::<GBlock>(&fix.vm.mem, gb_ptr).map_err(|e| BMError::MemErr(e))?;
        match self.locks.remove(&gb.loc) {
            Some(Lock::Read {
                dirty,
                validator,
                count,
                guest_ptr,
            }) => {
                if count > 1 {
                    // There are other holders, re insert.
                    self.locks.insert(
                        gb.loc,
                        Lock::Read {
                            dirty,
                            validator,
                            count: count - 1,
                            guest_ptr,
                        },
                    );
                    Ok(())
                } else if dirty {
                    // Remove read/write permissions
                    fix.vm
                        .mem
                        .change_perms(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), 0)
                        .map_err(|e| BMError::MemErr(e))?;
                    self.dirty.insert(gb.loc);
                    self.locks.insert(
                        gb.loc,
                        Lock::Dirty {
                            validator,
                            guest_ptr,
                        },
                    );
                    Ok(())
                } else {
                    let data = fix.vm.mem.free(gb.data).map_err(|e| BMError::MemErr(e))?;
                    fix.vm.mem.free(gb_ptr).map_err(|e| BMError::MemErr(e))?;
                    self.locks.insert(
                        gb.loc,
                        Lock::Clean {
                            resident: true,
                            validator: validator,
                            data,
                        },
                    );
                    Ok(())
                }
            }
            Some(Lock::Write {
                validator,
                guest_ptr,
            }) => {
                // Remove read/write permissions
                fix.vm
                    .mem
                    .change_perms(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), 0)
                    .map_err(|e| BMError::MemErr(e))?;
                self.dirty.insert(gb.loc);
                self.locks.insert(
                    gb.loc,
                    Lock::Dirty {
                        validator,
                        guest_ptr,
                    },
                );
                Ok(())
            }
            Some(Lock::Dirty { .. }) => Err(BMError::BadLock(gb.loc)),
            Some(Lock::Clean { .. }) => Err(BMError::BadLock(gb.loc)),
            None => Err(BMError::BadLock(gb.loc)),
        }
    }

    fn unlock_move(&mut self, fix: &mut Fixture, gb_ptr: Addr, new_location: u64) -> Result<()> {
        let loc = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)
            .map_err(|e| BMError::MemErr(e))?
            .loc;
        self.unlock(fix, gb_ptr)?;

        match self.locks.remove(&loc) {
            Some(Lock::Read { .. }) => {
                // Still held, so we have to create a new buffer and do a memcpy
                // FIXME: erroring for now, since I don't think this can happen
                todo!();
            }
            Some(Lock::Write { .. }) => Err(BMError::BadLock(loc)),
            Some(Lock::Dirty {
                validator,
                guest_ptr,
            }) => {
                // flush this block
                let gb =
                    read_guest::<GBlock>(&fix.vm.mem, guest_ptr).map_err(|e| BMError::MemErr(e))?;
                fix.vm
                    .mem
                    .change_perms(
                        gb.data,
                        Addr(gb.data.0 + BLOCK_SIZE as u64),
                        PERM_READ | PERM_WRITE,
                    )
                    .map_err(|e| BMError::MemErr(e))?;
                self.v_prep(fix, guest_ptr, validator)?;

                let data = fix.vm.mem.free(gb.data).map_err(|e| BMError::MemErr(e))?;

                // we deliberately don't count the cpu cost of this copy since
                // it wouldn't be incurred with bufio.
                let data_copy = data.clone();
                self.dirty.remove(&gb.loc);
                self.locks.insert(
                    gb.loc,
                    Lock::Clean {
                        resident: false,
                        validator: validator,
                        data,
                    },
                );
                self.locks.insert(
                    new_location,
                    Lock::Clean {
                        resident: true,
                        validator: validator,
                        data: data_copy,
                    },
                );
                Ok(())
            }
            Some(l @ Lock::Clean { .. }) => {
                self.locks.insert(loc, l.clone());
                self.locks.insert(new_location, l);
                Ok(())
            }
            None => Err(BMError::BadLock(loc)),
        }
    }

    fn flush(&mut self, fix: &mut Fixture) -> Result<()> {
        let mut dirty = BTreeSet::new();
        std::mem::swap(&mut dirty, &mut self.dirty);

        // Call prep on all dirty, unlocked blocks
        for loc in dirty {
            match self.locks.remove(&loc).unwrap() {
                Lock::Dirty {
                    validator,
                    guest_ptr,
                } => {
                    // We need to make sure the data has write permissions for the prep to
                    // work (it might have been read locked last).
                    let gb = read_guest::<GBlock>(&fix.vm.mem, guest_ptr)
                        .map_err(|e| BMError::MemErr(e))?;
                    fix.vm
                        .mem
                        .change_perms(
                            gb.data,
                            Addr(gb.data.0 + BLOCK_SIZE as u64),
                            PERM_READ | PERM_WRITE,
                        )
                        .map_err(|e| BMError::MemErr(e))?;
                    self.v_prep(fix, guest_ptr, validator)?;

                    let data = fix.vm.mem.free(gb.data).map_err(|e| BMError::MemErr(e))?;
                    self.locks.insert(
                        gb.loc,
                        Lock::Clean {
                            resident: true,
                            validator: validator,
                            data,
                        },
                    );
                }
                _ => {
                    // can't happen
                    assert!(false);
                }
            }
        }

        Ok(())
    }

    fn write_to_disk(&self, path: &Path) -> Result<()> {
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)
            .map_err(|e| BMError::IoErr(e))?;
        let zeroes = [0u8; 4096];

        for b in 0..self.nr_blocks {
            file.seek(io::SeekFrom::Start(b * BLOCK_SIZE as u64))
                .map_err(|e| BMError::IoErr(e))?;
            match self.locks.get(&b) {
                Some(Lock::Clean { data, .. }) => {
                    file.write_all(&data).map_err(|e| BMError::IoErr(e))?;
                }
                Some(_) => {
                    return Err(BMError::UnflushedData);
                }
                None => {
                    file.write_all(&zeroes).map_err(|e| BMError::IoErr(e))?;
                }
            }
        }
        Ok(())
    }

    /// At times we know which blocks are live data (eg, after a thin check),
    /// this method let's us throw away unused data.
    fn forget(&mut self, b: u64) -> Result<()> {
        self.check_bounds(b)?;
        /*
        match self.locks.remove(&b) {
            Some(Lock::Clean { .. }) => {
                debug!("forgetting block {}", b);
                Ok(())
            }
            Some(Lock::Dirty { .. }) => Err(anyhow!("cannot forget a block that is dirty")),
            Some(_) => Err(anyhow!("cannot forget a block that is locked")),
            None => Ok(()),
        }
        */
        Ok(())
    }

    fn set_read_only(&mut self, _ro: bool) {
        todo!();
    }

    fn is_read_only(&self) -> bool {
        // FIXME: finish
        false
    }

    //----------------------------------------------
    // These are the io engine methods, except they
    // take a mut self.
    //----------------------------------------------

    fn read(&mut self, b: u64) -> io::Result<io_engine::Block> {
        self.check_bounds_io(b)?;

        match self.locks.get(&b) {
            Some(Lock::Read { .. }) => Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                "read lock held by guest".to_string(),
            )),
            Some(Lock::Write { .. }) => Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                "write lock held by guest".to_string(),
            )),
            Some(Lock::Dirty { .. }) => Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                "block has not been flushed".to_string(),
            )),
            Some(Lock::Clean { data, .. }) => {
                let r = io_engine::Block::new(b);
                r.get_data().copy_from_slice(data);
                Ok(r)
            }
            None => {
                // Block isn't present, this should really only happen when reading the superblocks, where
                // we take all zeroes to mean 'format this device'.
                Ok(io_engine::Block::zeroed(b))
            }
        }
    }

    fn write(&mut self, block: &io_engine::Block) -> io::Result<()> {
        self.check_bounds_io(block.loc)?;

        match self.locks.get_mut(&block.loc) {
            Some(Lock::Read { .. }) => Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                "read lock held by guest".to_string(),
            )),
            Some(Lock::Write { .. }) => Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                "write lock held by guest".to_string(),
            )),
            Some(Lock::Dirty { .. }) => Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                "block has not been flushed".to_string(),
            )),
            Some(Lock::Clean { data, validator, .. }) => {
                data.copy_from_slice(&block.get_data());

                // force revalidation
                *validator = Addr(0);
                Ok(())
            }
            None => {
                // Block isn't present, so we'll create a new one.
                self.locks.insert(
                    block.loc,
                    Lock::Clean {
                        resident: true,
                        validator: Addr(0),
                        data: block.get_data().to_vec(),
                    },
                );
                Ok(())
            }
        }
    }
}

pub struct BlockManager {
    inner: Mutex<BMInner>,
}

impl Snapshot for BlockManager {
    fn snapshot(&self) -> Self {
        let inner = self.inner.lock().unwrap();
        BlockManager {
            inner: Mutex::new(inner.clone()),
        }
    }
}

impl BlockManager {
    pub fn new(nr_blocks: u64, bm_ptr: Addr) -> Self {
        BlockManager {
            inner: Mutex::new(BMInner::new(nr_blocks, bm_ptr)),
        }
    }

    pub fn residency(&self) -> usize {
        let inner = self.inner.lock().unwrap();
        inner.locks.len()
    }

    pub fn read_lock(&self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        let mut inner = self.inner.lock().unwrap();
        inner.read_lock(fix, loc, v_ptr)
    }

    pub fn write_lock(&self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        let mut inner = self.inner.lock().unwrap();
        inner.write_lock(fix, loc, v_ptr)
    }

    pub fn write_lock_zero(&self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        let mut inner = self.inner.lock().unwrap();
        inner.write_lock_zero(fix, loc, v_ptr)
    }

    // Returns true if ptr was freed, ie. no further holders of the lock.
    pub fn unlock(&self, fix: &mut Fixture, gb_ptr: Addr) -> Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.unlock(fix, gb_ptr)
    }

    pub fn unlock_move(&self, fix: &mut Fixture, gb_ptr: Addr, new_location: u64) -> Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.unlock_move(fix, gb_ptr, new_location)
    }

    pub fn get_nr_read_locks(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        inner.nr_read_locks
    }

    pub fn get_nr_write_locks(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        inner.nr_write_locks
    }

    pub fn get_nr_disk_reads(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        inner.nr_disk_reads
    }

    pub fn get_nr_held_blocks(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        let mut count = 0;
        for (b, lock) in &inner.locks {
            match lock {
                Lock::Read { .. } => {
                    debug!("read lock held for {}", b);
                    count += 1;
                }
                Lock::Write { .. } => {
                    debug!("write lock held for {}", b);
                    count += 1;
                }
                _ => {}
            }
        }
        count
    }

    pub fn flush(&self, fix: &mut Fixture) -> Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.flush(fix)
    }

    pub fn set_read_only(&self, ro: bool) {
        let mut inner = self.inner.lock().unwrap();
        inner.set_read_only(ro);
    }

    pub fn is_read_only(&self) -> bool {
        let inner = self.inner.lock().unwrap();
        inner.is_read_only()
    }

    pub fn forget(&self, b: u64) -> Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.forget(b)
    }

    pub fn write_to_disk(&self, path: &Path) -> Result<()> {
        let inner = self.inner.lock().unwrap();
        inner.write_to_disk(path)
    }
}

impl IoEngine for BlockManager {
    fn get_nr_blocks(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        inner.nr_blocks
    }

    fn get_batch_size(&self) -> usize {
        1024
    }

    fn read(&self, b: u64) -> io::Result<io_engine::Block> {
        let mut inner = self.inner.lock().unwrap();
        inner.read(b)
    }

    fn write(&self, block: &io_engine::Block) -> io::Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.write(block)
    }

    fn read_many(&self, blocks: &[u64]) -> io::Result<Vec<io::Result<io_engine::Block>>> {
        let mut inner = self.inner.lock().unwrap();
        let mut rvec = Vec::with_capacity(blocks.len());
        for b in blocks {
            rvec.push(inner.read(*b));
        }

        Ok(rvec)
    }

    fn write_many(&self, blocks: &[io_engine::Block]) -> io::Result<Vec<io::Result<()>>> {
        let mut rvec = Vec::with_capacity(blocks.len());
        for b in blocks {
            rvec.push(self.write(b));
        }

        Ok(rvec)
    }
}

//-------------------------------
