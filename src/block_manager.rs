use crate::decode::*;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use std::collections::BTreeMap;
use std::io;
use std::io::{Read, Write};
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

    fn pack<W: Write>(&self, _w: &mut W) -> io::Result<()> {
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
    pub loc: u64,

    // We hold the data in a separate allocation so the same Vec can be
    // bounced between the host and guest.
    pub data: Addr,
}

impl Guest for GBlock {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.loc)?;
        w.write_u64::<LittleEndian>(self.data.0)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let loc = r.read_u64::<LittleEndian>()?;
        let data = Addr(r.read_u64::<LittleEndian>()?);

        Ok(GBlock { loc, data })
    }
}

//-------------------------------

pub enum Lock {
    Read { count: usize, guest_ptr: Addr },
    Write { validator: Addr },
    Unlocked { data: Vec<u8> },
}

pub struct BMInner {
    nr_blocks: u64,
    locks: BTreeMap<u64, Lock>,

    pub nr_read_locks: u64,
    pub nr_write_locks: u64,
}

impl BMInner {
    fn new(nr_blocks: u64) -> Self {
        BMInner {
            nr_blocks,
            locks: BTreeMap::new(),
            nr_read_locks: 0,
            nr_write_locks: 0,
        }
    }

    /*
        fn v_check(&self, vm: &mut VM, guest_ptr: Addr, v_ptr: Addr) -> Result<()> {
            use Reg::*;

            // Call the prep function in the guest
            vm.set_reg(A0, v_ptr.0);
            vm.set_reg(A1, guest_ptr.0);
            vm.set_reg(A2, 4096);

            let v = read_guest::<Validator>(&vm.mem, v_ptr)?;
            vm.call_at(v.check)?;

            match fix.vm.reg(A0) as i64 as i32 {
                r if r < 0 => Err(anyhow!("validator check failed: {}", error_string(-r))),
                r if r > 0 => Err(anyhow!("validator check failed: {}", r)),
                _ => Ok(()),
            }
        }
    */

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

    // FIXME: self isn't used
    fn v_prep(&self, fix: &mut Fixture, guest_ptr: Addr, v_ptr: Addr) -> Result<()> {
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

        Ok(())
    }

    fn read_lock(&mut self, mem: &mut Memory, loc: u64, _v_ptr: Addr) -> Result<Addr> {
        self.check_bounds(loc)?;
        match self.locks.remove(&loc) {
            Some(Lock::Read { count, guest_ptr }) => {
                // Already read locked, just increment the reference count,
                // and return the previous guest ptr.
                self.locks.insert(
                    loc,
                    Lock::Read {
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
            Some(Lock::Unlocked { data }) => {
                let data = mem.alloc_bytes(data, PERM_READ)?;

                // FIXME: run validator->check()

                // Create guest ptr.
                let gb = GBlock { loc, data };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Read {
                        count: 1,
                        guest_ptr,
                    },
                );
                self.nr_read_locks += 1;
                Ok(guest_ptr)
            }
            None => {
                // This block has never been touched, so we'll initialise
                // with zeroes.
                let data = mem.alloc_bytes(vec![0; BLOCK_SIZE], PERM_READ)?;

                // Create guest ptr.
                let gb = GBlock { loc, data };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Read {
                        count: 1,
                        guest_ptr,
                    },
                );
                self.nr_read_locks += 1;
                Ok(guest_ptr)
            }
        }
    }

    fn write_lock(&mut self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.check_bounds(loc)?;
        match self.locks.remove(&loc) {
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
            Some(Lock::Unlocked { data }) => {
                let data = mem.alloc_bytes(data, PERM_READ | PERM_WRITE)?;

                // FIXME: run validator->check()

                // Create guest ptr.
                let gb = GBlock { loc, data };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;

                // insert lock
                self.locks.insert(loc, Lock::Write { validator: v_ptr });
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
            None => {
                // This block has never been touched, so we'll initialise
                // with zeroes.
                let data = mem.alloc_bytes(vec![0; BLOCK_SIZE], PERM_READ | PERM_WRITE)?;

                // Create guest ptr.
                let gb = GBlock { loc, data };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;

                // insert lock
                self.locks.insert(loc, Lock::Write { validator: v_ptr });
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
        }
    }

    fn write_lock_zero(&mut self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.check_bounds(loc)?;
        match self.locks.remove(&loc) {
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
            Some(Lock::Unlocked { .. }) => {
                let data = mem.alloc_bytes(vec![0u8; BLOCK_SIZE], PERM_READ | PERM_WRITE)?;

                // Create guest ptr.
                let gb = GBlock { loc, data };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;

                // insert lock
                self.locks.insert(loc, Lock::Write { validator: v_ptr });
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
            None => {
                // This block has never been touched, so we'll initialise
                // with zeroes.
                let data = mem.alloc_bytes(vec![0; BLOCK_SIZE], PERM_READ | PERM_WRITE)?;

                // Create guest ptr.
                let gb = GBlock { loc, data };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;

                // insert lock
                self.locks.insert(loc, Lock::Write { validator: v_ptr });
                self.nr_write_locks += 1;
                Ok(guest_ptr)
            }
        }
    }

    // Returns true if ptr was freed, ie. no further holders of the lock.
    fn unlock(&mut self, fix: &mut Fixture, gb_ptr: Addr) -> Result<bool> {
        let gb = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)?;
        match self.locks.remove(&gb.loc) {
            Some(Lock::Read { count, guest_ptr }) => {
                if count > 1 {
                    // There are other holders, re insert.
                    self.locks.insert(
                        gb.loc,
                        Lock::Read {
                            count: count - 1,
                            guest_ptr,
                        },
                    );
                    Ok(false)
                } else {
                    let data = fix.vm.mem.free(gb.data)?;
                    fix.vm.mem.free(gb_ptr)?;
                    self.locks.insert(gb.loc, Lock::Unlocked { data });
                    Ok(true)
                }
            }
            Some(Lock::Write { validator }) => {
                // Call the validator
                // FIXME: we could defer this until the flush
                self.v_prep(fix, gb_ptr, validator)?;
                let data = fix.vm.mem.free(gb.data)?;
                fix.vm.mem.free(gb_ptr)?;
                self.locks.insert(gb.loc, Lock::Unlocked { data });
                Ok(true)
            }
            Some(Lock::Unlocked { .. }) => {
                Err(anyhow!("block {} is not locked", gb.loc))
            }
            None => {
                Err(anyhow!("block {} has never been locked", gb.loc))
            }
        }
    }

    fn flush(&mut self) {
        // Noop, since we write as soon as blocks are unlocked.
    }

    fn set_read_only(&mut self, _ro: bool) {
        todo!();
    }

    fn is_read_only(&self) -> bool {
        todo!();
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

            Some(Lock::Unlocked { data }) => {
                let r = io_engine::Block::new(b);
                r.get_data().copy_from_slice(data);
                Ok(r)
            }
            None => {
                // Block isn't present, so we'll just return zeroes.
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
            Some(Lock::Unlocked { data }) => {
                data.copy_from_slice(&block.get_data());
                Ok(())
            }
            None => {
                // Block isn't present, so we'll create a new one.
                self.locks.insert(
                    block.loc,
                    Lock::Unlocked {
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
    pub fn new(nr_blocks: u64) -> Self {
        BlockManager {
            inner: Mutex::new(BMInner::new(nr_blocks)),
        }
    }

    pub fn residency(&self) -> usize {
        let inner = self.inner.lock().unwrap();
        inner.locks.len()
    }

    pub fn read_lock(&self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        let mut inner = self.inner.lock().unwrap();
        inner.read_lock(mem, loc, v_ptr)
    }

    pub fn write_lock(&self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        let mut inner = self.inner.lock().unwrap();
        inner.write_lock(mem, loc, v_ptr)
    }

    pub fn write_lock_zero(&self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        let mut inner = self.inner.lock().unwrap();
        inner.write_lock_zero(mem, loc, v_ptr)
    }

    // Returns true if ptr was freed, ie. no further holders of the lock.
    pub fn unlock(&self, fix: &mut Fixture, gb_ptr: Addr) -> Result<bool> {
        let mut inner = self.inner.lock().unwrap();
        inner.unlock(fix, gb_ptr)
    }

    pub fn get_nr_read_locks(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        inner.nr_read_locks
    }

    pub fn get_nr_write_locks(&self) -> u64 {
        let inner = self.inner.lock().unwrap();
        inner.nr_write_locks
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

    pub fn flush(&self) {
        let mut inner = self.inner.lock().unwrap();
        inner.flush();
    }

    pub fn set_read_only(&self, ro: bool) {
        let mut inner = self.inner.lock().unwrap();
        inner.set_read_only(ro);
    }

    pub fn is_read_only(&self) -> bool {
        let inner = self.inner.lock().unwrap();
        inner.is_read_only()
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
