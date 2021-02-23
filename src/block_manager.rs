use crate::decode::*;
use crate::guest::*;
use crate::memory::*;
use crate::fixture::*;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::debug;
use std::collections::BTreeMap;
use std::io;
use std::io::{Read, Write};
use std::sync::{Arc, Mutex};
use thinp::io_engine;
use thinp::io_engine::{IoEngine, BLOCK_SIZE};

//-------------------------------

/// Core store is an io_engine that keeps it's data in ram.
/// FIXME: move to thinp since might be useful for tests there?
pub struct CoreEngine {
    nr_blocks: u64,
    blocks: Mutex<BTreeMap<u64, Vec<u8>>>,
}

impl CoreEngine {
    pub fn new(nr_blocks: u64) -> Self {
        CoreEngine {
            nr_blocks,
            blocks: Mutex::new(BTreeMap::new()),
        }
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

    pub fn residency(&self) -> usize {
        let blocks = self.blocks.lock().unwrap();
        blocks.len()
    }
}

impl io_engine::IoEngine for CoreEngine {
    fn get_nr_blocks(&self) -> u64 {
        self.nr_blocks
    }

    fn get_batch_size(&self) -> usize {
        16
    }

    fn read(&self, b: u64) -> io::Result<io_engine::Block> {
        self.check_bounds(b)?;

        let blocks = self.blocks.lock().unwrap();
        if let Some(bytes) = blocks.get(&b) {
            let r = io_engine::Block::new(b);
            r.get_data().copy_from_slice(&bytes);
            Ok(r)
        } else {
            // Block isn't present, so we'll just return zeroes.
            Ok(io_engine::Block::zeroed(b))
        }
    }

    fn read_many(&self, blocks: &[u64]) -> io::Result<Vec<io::Result<io_engine::Block>>> {
        let mut rvec = Vec::with_capacity(blocks.len());
        for b in blocks {
            rvec.push(self.read(*b));
        }

        Ok(rvec)
    }

    fn write(&self, block: &io_engine::Block) -> io::Result<()> {
        self.check_bounds(block.loc)?;

        let mut blocks = self.blocks.lock().unwrap();
        if let Some(bytes) = blocks.get_mut(&block.loc) {
            bytes.copy_from_slice(&block.get_data());
            Ok(())
        } else {
            // Block isn't present, so we'll create it.
            blocks.insert(block.loc, block.get_data().to_vec());
            Ok(())
        }
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
    data: Vec<u8>,
}

impl Guest for GBlock {
    fn guest_len() -> usize {
        8 + BLOCK_SIZE
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        // I'm only supporting 4k blocks atm, since that's all we use.
        assert!(self.data.len() == BLOCK_SIZE);

        w.write_u64::<LittleEndian>(self.loc)?;
        w.write_all(&self.data)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let loc = r.read_u64::<LittleEndian>()?;
        let mut data = vec![0; BLOCK_SIZE];
        r.read_exact(&mut data)?;

        Ok(GBlock { loc, data })
    }
}

//-------------------------------

pub enum Lock {
    Read { count: usize, guest_ptr: Addr },
    Write { validator: Addr },
}

pub struct BlockManager {
    pub engine: Arc<dyn IoEngine + Sync + Send>,
    pub locks: BTreeMap<u64, Lock>,

    pub nr_read_locks: u64,
    pub nr_write_locks: u64,
}

impl BlockManager {
    pub fn new(engine: Arc<dyn IoEngine + Sync + Send>) -> Self {
        BlockManager {
            engine,
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

    pub fn read_lock(&mut self, mem: &mut Memory, loc: u64, _v_ptr: Addr) -> Result<Addr> {
        self.nr_read_locks += 1;
        match self.locks.get_mut(&loc) {
            Some(Lock::Read { count, guest_ptr }) => {
                // Already read locked, just increment the reference count,
                // and return the previous guest ptr.
                *count += 1;
                Ok(*guest_ptr)
            }
            Some(Lock::Write { .. }) => Err(anyhow!(
                "Can't read lock block since it's already write locked"
            )),
            None => {
                // Read from the engine
                let io_b = self.engine.read(loc)?;

                // Create guest ptr.
                // FIXME: redundant copy
                let gb = GBlock {
                    loc,
                    data: io_b.get_data().to_vec(),
                };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ)?;
                debug!("Allocated guest_ptr at {:?}", guest_ptr);

                /*
                                // Call the validator
                                self.v_check(fix, guest_ptr, v_ptr)?;
                */

                // insert lock
                self.locks.insert(
                    loc,
                    Lock::Read {
                        count: 1,
                        guest_ptr,
                    },
                );
                Ok(guest_ptr)
            }
        }
    }

    pub fn write_lock(&mut self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.nr_write_locks += 1;
        match self.locks.get_mut(&loc) {
            Some(Lock::Read { .. }) => Err(anyhow!(
                "Can't write lock block since it's already read locked"
            )),
            Some(Lock::Write { .. }) => Err(anyhow!(
                "Can't write lock block since it's already write locked"
            )),
            None => {
                // Read from the engine
                let io_b = self.engine.read(loc)?;

                // Create guest ptr.
                let gb = GBlock {
                    loc,
                    data: io_b.get_data().to_vec(),
                };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ | PERM_WRITE)?;

                /*
                                // Call the validator
                                self.v_check(fix, guest_ptr, v_ptr)?;
                */

                // insert lock
                self.locks.insert(loc, Lock::Write { validator: v_ptr });
                Ok(guest_ptr)
            }
        }
    }

    pub fn write_lock_zero(&mut self, mem: &mut Memory, loc: u64, v_ptr: Addr) -> Result<Addr> {
        self.nr_write_locks += 1;
        match self.locks.get_mut(&loc) {
            Some(Lock::Read { .. }) => Err(anyhow!(
                "Can't write lock block since it's already read locked"
            )),
            Some(Lock::Write { .. }) => Err(anyhow!(
                "Can't write lock block since it's already write locked"
            )),
            None => {
                // No need to read from engine, since we're going to zero.
                // Create guest ptr.
                let gb = GBlock {
                    loc,
                    data: vec![0u8; BLOCK_SIZE],
                };
                let guest_ptr = alloc_guest::<GBlock>(mem, &gb, PERM_READ | PERM_WRITE)?;

                // insert lock
                self.locks.insert(loc, Lock::Write { validator: v_ptr });
                Ok(guest_ptr)
            }
        }
    }

    // Returns true if ptr was freed, ie. no further holders of the lock.
    pub fn unlock(&mut self, fix: &mut Fixture, gb_ptr: Addr) -> Result<bool> {
        let gb = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)?;
        let lock = self.locks.remove(&gb.loc);
        if lock.is_none() {
            return Err(anyhow!("Block is not locked"));
        }

        match lock.unwrap() {
            Lock::Read { count, guest_ptr } => {
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
                    fix.vm.mem.free(gb_ptr)?;
                    Ok(true)
                }
            }
            Lock::Write { validator } => {
                let io_b = io_engine::Block::new(gb.loc);

                // Call the validator
                self.v_prep(fix, gb_ptr, validator)?;

                // We have to re-read since the data will have been updated by the
                // validator.
                let gb = read_guest::<GBlock>(&fix.vm.mem, gb_ptr)?;

                fix.vm.mem.free(gb_ptr)?;

                io_b.get_data().copy_from_slice(&gb.data);
                self.engine.write(&io_b)?;
                Ok(true)
            }
        }
    }

    pub fn flush(&mut self) {
        // Noop, since we write as soon as blocks are unlocked.
    }

    pub fn set_read_only(&mut self, _ro: bool) {
        todo!();
    }

    pub fn is_read_only(&self) -> bool {
        todo!();
    }
}

//-------------------------------
