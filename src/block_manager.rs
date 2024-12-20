use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use std::collections::BTreeMap;
use std::fs::OpenOptions;
use std::io;
use std::io::Seek;
use std::io::{Read, Write};
use std::path::Path;
use std::sync::Mutex;
use thinp::io_engine;
use thinp::io_engine::{IoEngine, BLOCK_SIZE};

//-------------------------------

#[allow(dead_code)]
struct Validator {
    name: Addr,
    prepare: Addr,
    check: Addr,
}

impl Guest for Validator {
    fn guest_len() -> usize {
        24
    }

    fn pack<W: Write>(&self, _w: &mut W, _loc: Addr) -> io::Result<()> {
        todo!();
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
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

    fn pack<W: Write>(&self, w: &mut W, _loc: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.bm_ptr.0)?;
        w.write_u64::<LittleEndian>(self.loc)?;
        w.write_u64::<LittleEndian>(self.data.0)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
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
        // The validator pointer specified by the guest.
        //
        // - For blocks initialized without a validator (i.e., when the
        //   in-kernel dm_block_validator pointer is null), this field
        //   is represented as Some(Addr(0)).
        // - For blocks written by the host through the IoEngine interface,
        //   this field is represented as None, as the layout is unknown to
        //   the kernel.
        //
        // Reading or writing a block with a different validator, including
        // Some(Addr(0)), is not allowed (*). Clean blocks written by the host
        // should be checked by the guest validator while locking, to ensrue
        // the host written data is compliant.
        //
        // (*) The dm_bm_validate_buffer() in dm-block-manager allows users to
        // read a block without a validator and then change the validator pointer
        // from null to non-null if the checksum matches. However, this capability
        // is not practical thus it is removed in the stub implementation.
        validator: Option<Addr>,
        data: Vec<u8>,
    },
}

pub struct BMInner {
    bm_ptr: Addr,
    nr_blocks: u64,
    locks: BTreeMap<u64, Lock>,

    pub nr_read_locks: u64,
    pub nr_write_locks: u64,
    pub nr_prepares: u64,
    pub nr_disk_reads: u64,
}

impl Drop for BMInner {
    fn drop(&mut self) {
        debug!("{} prepares", self.nr_prepares);
    }
}

impl BMInner {
    fn new(nr_blocks: u64, bm_ptr: Addr) -> Self {
        BMInner {
            bm_ptr,
            nr_blocks,
            locks: BTreeMap::new(),
            nr_read_locks: 0,
            nr_write_locks: 0,
            nr_prepares: 0,
            nr_disk_reads: 0,
        }
    }

    fn free_gb(mem: &mut Memory, gb_ptr: Addr) -> Result<()> {
        let gb = read_guest::<GBlock>(mem, gb_ptr)?;
        mem.free(gb.data)?;
        mem.free(gb_ptr)?;
        Ok(())
    }

    /// Clears the locks including guest ptrs from memory.
    fn clear_all_locks(&mut self, mem: &mut Memory) -> Result<()> {
        use Lock::*;

        let mut locks = BTreeMap::new();
        std::mem::swap(&mut locks, &mut self.locks);

        for (_, l) in locks {
            match l {
                Read { guest_ptr, .. } => {
                    Self::free_gb(mem, guest_ptr)?;
                }
                Write { guest_ptr, .. } => {
                    Self::free_gb(mem, guest_ptr)?;
                }
                Dirty { guest_ptr, .. } => {
                    Self::free_gb(mem, guest_ptr)?;
                }

                // Clean data is moved back to the host.
                Clean { .. } => { // do nothing},
                }
            }
        }

        Ok(())
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

        let v = read_guest::<Validator>(&fix.vm.mem, v_ptr)?;
        fix.call_at_with_errno(v.check)
    }

    fn check_bounds(&self, loc: u64) -> io::Result<()> {
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

        let v = read_guest::<Validator>(&fix.vm.mem, v_ptr)?;
        if !v.prepare.is_null() {
            fix.call_at(v.prepare)?;
        }

        self.nr_prepares += 1;
        Ok(())
    }

    fn read_lock(&mut self, fix: &mut Fixture, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.check_bounds(loc)?;
        let lock = self.locks.remove(&loc);
        match lock {
            Some(Lock::Read {
                dirty,
                validator,
                count,
                guest_ptr,
            }) => {
                if validator != v_ptr {
                    self.locks.insert(loc, lock.unwrap());
                    error!("validator mismatch for block {}", loc);
                    return Err(anyhow::Error::new(CallError::new(
                        "read_lock",
                        -libc::EINVAL,
                    )));
                }

                // Already read locked, just increment the reference count,
                // and return the previous guest ptr.
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
                Err(anyhow!(
                    "Can't read lock block since it's already write locked"
                ))
            }
            Some(Lock::Dirty {
                validator,
                guest_ptr,
            }) => {
                if validator != v_ptr {
                    self.locks.insert(loc, lock.unwrap());
                    error!("validator mismatch for block {}", loc);
                    return Err(anyhow::Error::new(CallError::new(
                        "read_lock",
                        -libc::EINVAL,
                    )));
                }

                let gb = read_guest::<GBlock>(&fix.vm.mem, guest_ptr)?;
                fix.vm
                    .mem
                    .change_perms(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), PERM_READ)?;
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
                validator: maybe_validator,
                data,
            }) => {
                if let Some(v) = maybe_validator {
                    if v != v_ptr {
                        self.locks.insert(
                            loc,
                            Lock::Clean {
                                resident,
                                validator: maybe_validator,
                                data,
                            },
                        );
                        error!("validator mismatch for block {}", loc);
                        return Err(anyhow::Error::new(CallError::new(
                            "read_lock",
                            -libc::EINVAL,
                        )));
                    }
                }

                let data = fix.vm.mem.alloc_aligned(data, PERM_READ, 4096)?;

                // Create guest ptr.
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)?;

                if maybe_validator.is_none() {
                    self.v_check(fix, guest_ptr, v_ptr).or_else(|e| {
                        fix.vm.mem.free(guest_ptr)?;
                        let data = fix.vm.mem.free(data)?;
                        self.locks.insert(
                            loc,
                            Lock::Clean {
                                resident,
                                validator: maybe_validator,
                                data,
                            },
                        );
                        Err(e)
                    })?;
                }

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Read {
                        dirty: false,
                        validator: v_ptr, // FIXME: check compatible with maybe_validator
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
                    return Err(anyhow!("request to read an uninitialised block: {}", loc));
                }

                let data = fix
                    .vm
                    .mem
                    .alloc_aligned(vec![0; BLOCK_SIZE], PERM_READ, 4096)?;

                // Create guest ptr.
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)?;

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
        let lock = self.locks.remove(&loc);
        match lock {
            Some(l @ Lock::Read { .. }) => {
                self.locks.insert(loc, l);
                Err(anyhow!(
                    "Can't write lock block since it's already read locked"
                ))
            }
            Some(l @ Lock::Write { .. }) => {
                self.locks.insert(loc, l);
                Err(anyhow!(
                    "Can't write lock block since it's already write locked"
                ))
            }
            Some(Lock::Dirty {
                validator,
                guest_ptr,
            }) => {
                if !zero && validator != v_ptr {
                    self.locks.insert(loc, lock.unwrap());
                    error!("validator mismatch for block {}", loc);
                    return Err(anyhow::Error::new(CallError::new(
                        "write_lock",
                        -libc::EINVAL,
                    )));
                }

                let gb = read_guest::<GBlock>(&fix.vm.mem, guest_ptr)?;
                fix.vm.mem.change_perms(
                    gb.data,
                    Addr(gb.data.0 + BLOCK_SIZE as u64),
                    PERM_READ | PERM_WRITE,
                )?;

                if zero {
                    fix.vm
                        .mem
                        .zero(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), PERM_WRITE)?;
                }
                self.locks.insert(
                    loc,
                    Lock::Write {
                        validator: v_ptr, // will switch the validator on zeroing
                        guest_ptr,
                    },
                );
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
            Some(Lock::Clean {
                resident,
                validator: maybe_validator,
                data,
            }) => {
                if zero {
                    unsafe {
                        std::ptr::write_bytes(data.as_ptr() as *mut u8, 0, BLOCK_SIZE);
                    }
                } else if let Some(v) = maybe_validator {
                    if v != v_ptr {
                        self.locks.insert(
                            loc,
                            Lock::Clean {
                                resident,
                                validator: maybe_validator,
                                data,
                            },
                        );
                        error!("validator mismatch for block {}", loc);
                        return Err(anyhow::Error::new(CallError::new(
                            "write_lock",
                            -libc::EINVAL,
                        )));
                    }
                }

                // Create guest ptr.
                let data = fix
                    .vm
                    .mem
                    .alloc_aligned(data, PERM_READ | PERM_WRITE, 4096)?;
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)?;
                if !zero && maybe_validator.is_none() {
                    self.v_check(fix, guest_ptr, v_ptr).or_else(|e| {
                        fix.vm.mem.free(guest_ptr)?;
                        let data = fix.vm.mem.free(data)?;
                        self.locks.insert(
                            loc,
                            Lock::Clean {
                                resident,
                                validator: maybe_validator,
                                data,
                            },
                        );
                        Err(e)
                    })?;
                }

                // insert lock
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
                    return Err(anyhow!(
                        "request to write an uninitialised block without zero flag: {}",
                        loc
                    ));
                }

                // This block has never been touched, so we'll initialise
                // with zeroes.
                let data =
                    fix.vm
                        .mem
                        .alloc_aligned(vec![0; BLOCK_SIZE], PERM_READ | PERM_WRITE, 4096)?;

                // Create guest ptr.
                let gb = GBlock {
                    bm_ptr: self.bm_ptr,
                    loc,
                    data,
                };
                let guest_ptr = alloc_guest::<GBlock>(&mut fix.vm.mem, &gb, PERM_READ)?;

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
        let gb = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)?;
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
                        .change_perms(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), 0)?;
                    self.locks.insert(
                        gb.loc,
                        Lock::Dirty {
                            validator,
                            guest_ptr,
                        },
                    );
                    Ok(())
                } else {
                    let data = fix.vm.mem.free(gb.data)?;
                    fix.vm.mem.free(gb_ptr)?;
                    self.locks.insert(
                        gb.loc,
                        Lock::Clean {
                            resident: true,
                            validator: Some(validator),
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
                    .change_perms(gb.data, Addr(gb.data.0 + BLOCK_SIZE as u64), 0)?;
                self.locks.insert(
                    gb.loc,
                    Lock::Dirty {
                        validator,
                        guest_ptr,
                    },
                );
                Ok(())
            }
            Some(l @ Lock::Dirty { .. }) => {
                self.locks.insert(gb.loc, l);
                Err(anyhow!("block {} is not locked", gb.loc))
            }
            Some(l @ Lock::Clean { .. }) => {
                self.locks.insert(gb.loc, l);
                Err(anyhow!("block {} is not locked", gb.loc))
            }
            None => Err(anyhow!("block {} has never been locked", gb.loc)),
        }
    }

    fn unlock_move(&mut self, fix: &mut Fixture, gb_ptr: Addr, new_location: u64) -> Result<()> {
        let loc = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)?.loc;
        self.unlock(fix, gb_ptr)?;

        match self.locks.remove(&loc) {
            Some(Lock::Read { .. }) => {
                // Still held, so we have to create a new buffer and do a memcpy
                // FIXME: erroring for now, since I don't think this can happen
                Err(anyhow!("oh ... it can happen"))
            }
            Some(Lock::Write { .. }) => Err(anyhow!("block {} is still write locked somehow", loc)),
            Some(Lock::Dirty {
                validator,
                guest_ptr,
            }) => {
                // flush this block
                let gb = read_guest::<GBlock>(&fix.vm.mem, guest_ptr)?;
                fix.vm.mem.change_perms(
                    gb.data,
                    Addr(gb.data.0 + BLOCK_SIZE as u64),
                    PERM_READ | PERM_WRITE,
                )?;
                self.v_prep(fix, guest_ptr, validator)?;

                let data = fix.vm.mem.free(gb.data)?;

                // we deliberately don't count the cpu cost of this copy since
                // it wouldn't be incurred with bufio.
                let data_copy = data.clone();
                self.locks.insert(
                    gb.loc,
                    Lock::Clean {
                        resident: false,
                        validator: Some(validator),
                        data,
                    },
                );
                self.locks.insert(
                    new_location,
                    Lock::Clean {
                        resident: true,
                        validator: Some(validator),
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
            None => Err(anyhow!("block {} has never been locked", loc)),
        }
    }

    fn flush(&mut self, fix: &mut Fixture) -> Result<()> {
        let mut locks = BTreeMap::new();
        std::mem::swap(&mut locks, &mut self.locks);

        // Call prep on all dirty, unlocked blocks
        for (loc, entry) in locks {
            match entry {
                Lock::Dirty {
                    validator,
                    guest_ptr,
                } => {
                    // We need to make sure the data has write permissions for the prep to
                    // work (it might have been read locked last).
                    let gb = read_guest::<GBlock>(&fix.vm.mem, guest_ptr)?;
                    fix.vm.mem.change_perms(
                        gb.data,
                        Addr(gb.data.0 + BLOCK_SIZE as u64),
                        PERM_READ | PERM_WRITE,
                    )?;
                    self.v_prep(fix, guest_ptr, validator)?;

                    let data = fix.vm.mem.free(gb.data)?;
                    fix.vm.mem.free(guest_ptr)?;
                    self.locks.insert(
                        gb.loc,
                        Lock::Clean {
                            resident: true,
                            validator: Some(validator),
                            data,
                        },
                    );
                }
                _ => {
                    self.locks.insert(loc, entry);
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
            .truncate(true)
            .open(path)?;
        let zeroes = [0u8; 4096];

        for b in 0..self.nr_blocks {
            file.seek(io::SeekFrom::Start(b * BLOCK_SIZE as u64))?;
            match self.locks.get(&b) {
                Some(Lock::Clean { data, .. }) => {
                    file.write_all(data)?;
                }
                Some(_) => {
                    return Err(anyhow!(
                        "cannot write bm to disk since there's unflushed/locked data"
                    ));
                }
                None => {
                    file.write_all(&zeroes)?;
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
    // take a mut self and return anyhow errors.
    //----------------------------------------------

    fn read(&mut self, b: u64) -> io::Result<io_engine::Block> {
        self.check_bounds(b)?;

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
        self.check_bounds(block.loc)?;

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
            Some(Lock::Clean { data, .. }) => {
                data.copy_from_slice(block.get_data());
                Ok(())
            }
            None => {
                // Block isn't present, so we'll create a new one.
                self.locks.insert(
                    block.loc,
                    Lock::Clean {
                        resident: true,
                        validator: None,
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

impl BlockManager {
    pub fn new(nr_blocks: u64, bm_ptr: Addr) -> Self {
        BlockManager {
            inner: Mutex::new(BMInner::new(nr_blocks, bm_ptr)),
        }
    }

    pub fn clear_all_locks(&self, mem: &mut Memory) -> Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.clear_all_locks(mem)
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

    fn suggest_nr_threads(&self) -> usize {
        1
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
