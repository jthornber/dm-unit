use crate::decode::Reg;
use crate::loader::*;
use crate::memory::*;
use crate::memory::{Addr, PERM_EXEC, PERM_READ, PERM_WRITE};
use crate::user_data::*;
use crate::vm::*;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use crc32c::crc32c;
use elf::types::Symbol;
use libc::{c_char, c_int, strerror_r};
use log::{debug, info, warn};
use std::collections::BTreeMap;
use std::ffi::CStr;
use std::io;
use std::io::{Cursor, Read, Write};
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::str;
use std::sync::{Arc, Mutex};

use Reg::*;

//-------------------------------

type FixCallback = Box<dyn Fn(&mut Fixture) -> Result<()>>;

#[allow(dead_code)]
pub struct Fixture {
    pub vm: VM,

    // Entry points for symbols
    symbols: BTreeMap<String, Symbol>,

    // Associates breakpoint addresses with callback functions.
    breakpoints: BTreeMap<u64, FixCallback>,

    // Associates an address in the vm with rust user data.
    user_data: UserData,

    // Current indentation for function tracing.
    trace_indent: usize,
}

impl Fixture {
    pub fn new<P: AsRef<Path>>(kernel_dir: P) -> Result<Self> {
        let mut module = PathBuf::new();
        module.push(kernel_dir);
        module.push("drivers/md/persistent-data/dm-persistent-data.ko");

        let heap_begin = Addr(1024 * 1024 * 1024 * 3);
        let heap_end = Addr(heap_begin.0 + (1024 * 1024));
        let mem = Memory::new(heap_begin, heap_end);
        let mut vm = VM::new(mem);
        let symbols = load_elf(&mut vm.mem, module)?;

        // Setup the stack and heap
        vm.setup_stack(8 * 1024)?;

        Ok(Fixture {
            vm,
            symbols,
            breakpoints: BTreeMap::new(),
            user_data: UserData::new(),
            trace_indent: 0,
        })
    }

    fn lookup_fn(&self, func: &str) -> Result<Addr> {
        if let Some(addr) = self.symbols.get(func) {
            Ok(Addr(addr.value))
        } else {
            Err(anyhow!("couldn't lookup symbol '{}'", func))
        }
    }

    fn symbol_rmap(&self, loc: u64) -> Option<String> {
        for (name, sym) in &self.symbols {
            if sym.value == loc {
                return Some(name.clone());
            }
        }

        None
    }

    // Runs the vm, handling any breakpoints.
    fn run_vm(&mut self) -> Result<()> {
        loop {
            match self.vm.run() {
                Ok(()) => return Ok(()),
                Err(VmErr::Breakpoint) => {
                    let loc = self.vm.reg(Reg::PC);

                    // Temporarily remove the breakpoint before executing, this
                    // gets around some issues with the fixture being held multiple
                    // times, and allows the breakpoints to recurse back into here.  The
                    // downside is you cannot recurse a particular breakpoint.
                    if let Some(callback) = self.breakpoints.remove(&loc) {
                        if let Some(_global) = self.symbol_rmap(loc) {
                            // debug!("host call: {}", global);
                        } else {
                            // debug!("host call: {:x}", loc);
                        }
                        let r = (*callback)(self);
                        self.breakpoints.insert(loc, callback);
                        r?;
                    } else {
                        Err(anyhow!(
                            "Breakpoint at {:x?} without callback",
                            self.vm.reg(PC)
                        ))?;
                    }
                }
                Err(VmErr::EBreak) => {
                    if let Some(global) = self.symbol_rmap(self.vm.reg(Reg::PC)) {
                        warn!("unstubbed global called: {}", global);
                        return Err(anyhow!("unstubbed global access '{}'", global));
                    } else {
                        Err(VmErr::EBreak)?;
                    }
                }
                err => err?,
            }
        }
    }

    // Call a named function in the vm.  Returns the contents of Ra.
    pub fn call(&mut self, func: &str) -> Result<()> {
        let entry = self.lookup_fn(func)?;

        // We need a unique address return control to us.
        let exit_addr = self.vm.mem.alloc_perms(4, PERM_EXEC)?;
        self.vm.set_reg(Reg::Ra, exit_addr.0);
        self.vm.set_pc(entry);

        let completed = Arc::new(Mutex::new(false));
        {
            let completed = completed.clone();

            let callback = move |_fix: &mut Fixture| {
                let mut completed = completed.lock().unwrap();
                *completed = true;
                Err(anyhow!("call complete, exiting"))
            };

            self.at_addr(exit_addr, Box::new(callback));
        }

        let result = self.run_vm();
        self.vm.mem.unmap(exit_addr)?;
        match result {
            Ok(_) => {
                // Not sure how we can get here
                todo!();
            }
            Err(e) => {
                let completed = completed.lock().unwrap();
                if *completed == true {
                    Ok(())
                } else {
                    Err(e)
                }
            }
        }
    }

    // Use this to call functions that return an int errno.
    pub fn call_with_errno(&mut self, tm_func: &str) -> Result<()> {
        self.call(tm_func)?;
        let r = self.vm.reg(A0) as i64 as i32;
        if r != 0 {
            if r < 0 {
                return Err(anyhow!("{} failed: {}", tm_func, error_string(-r)));
            } else {
                return Err(anyhow!("{} failed: {}", tm_func, r));
            }
        }
        Ok(())
    }

    pub fn at_addr(&mut self, loc: Addr, callback: FixCallback) {
        self.vm.add_breakpoint(loc);
        self.breakpoints.insert(loc.0, callback);
    }

    pub fn at_func(&mut self, name: &str, callback: FixCallback) -> Result<()> {
        let func_addr = self.lookup_fn(name)?;
        self.at_addr(func_addr, callback);
        Ok(())
    }

    // Stubs a function to just return a particular value.
    pub fn stub(&mut self, func: &str, v: u64) -> Result<()> {
        let callback = move |fix: &mut Fixture| {
            fix.vm.ret(v);
            Ok(())
        };
        self.at_func(func, Box::new(callback))
    }

    // FIXME: there's got to be a better way to do this
    fn indent_string(&self) -> String {
        let mut r = String::new();
        for _ in 0..self.trace_indent {
            r.push(' ');
        }
        r
    }

    fn trace_entry(&mut self, func: &str) {
        debug!("{}>>> {}", self.indent_string(), func);
        self.trace_indent += 1;
    }

    fn trace_exit(&mut self, func: &str, rv: u64) {
        let err = rv as i32;
        let estr = if err < 0 && err >= -1024 {
            error_string(-err)
        } else {
            format!("{:x}", rv)
        };
        self.trace_indent -= 1;
        debug!("{}<<< {} -> {}", self.indent_string(), func, estr);
    }

    /// Logs a debug message when this function is entered and exited.
    /// Useful for tracing progress of a test.  Tracing return from the
    /// function is awkward, we have to squeeze in a wrapper function that
    /// is returned to where we can set the breakpoint.
    pub fn trace_func(&mut self, func: &str) -> Result<()> {
        let name = func.to_string();
        let trampoline = self.vm.mem.alloc_perms(4, PERM_EXEC)?;

        let entry_callback = {
            let name = name.clone();
            move |fix: &mut Fixture| {
                // Push the real return address onto the stack.
                fix.vm.push_reg(Ra)?;

                // Set Ra to our trampoline.
                fix.vm.set_reg(Ra, trampoline.0);
                fix.trace_entry(&name);
                Ok(())
            }
        };

        let exit_callback = {
            let name = name.clone();
            move |fix: &mut Fixture| {
                fix.trace_exit(&name, fix.vm.reg(A0));
                fix.vm.pop_reg(Ra)?;
                fix.vm.set_reg(PC, fix.vm.reg(Ra));
                Ok(())
            }
        };

        self.at_func(func, Box::new(entry_callback))?;
        self.at_addr(trampoline, Box::new(exit_callback));

        Ok(())
    }

    /// Attaches a standard set of global implementations.
    /// eg, kmalloc, kfree.
    pub fn standard_globals(&mut self) -> Result<()> {
        self.at_func("__kmalloc", Box::new(kmalloc))?;
        self.at_func("kmalloc_order", Box::new(kmalloc))?;
        self.at_func("memset", Box::new(memset))?;
        self.at_func("kfree", Box::new(kfree))?;
        self.stub("__raw_spin_lock_init", 0)?;
        self.stub("_raw_spin_lock", 0)?;
        self.stub("_raw_spin_unlock", 0)?;
        self.stub("__mutex_init", 0)?;
        self.at_func("memcpy", Box::new(memcpy))?;
        self.at_func("dm_block_location", Box::new(bm_block_location))?;
        self.at_func("dm_block_data", Box::new(bm_block_data))?;
        self.at_func("dm_block_manager_create", Box::new(bm_create))?;
        self.at_func("dm_block_manager_destroy", Box::new(bm_destroy))?;
        self.at_func("dm_bm_block_size", Box::new(bm_block_size))?;
        self.at_func("dm_bm_nr_blocks", Box::new(bm_nr_blocks))?;
        self.at_func("dm_bm_read_lock", Box::new(bm_read_lock))?;
        self.at_func("dm_bm_read_try_lock", Box::new(bm_read_lock))?;
        self.at_func("dm_bm_write_lock", Box::new(bm_write_lock))?;
        self.at_func("dm_bm_write_lock_zero", Box::new(bm_write_lock_zero))?;
        self.at_func("dm_bm_unlock", Box::new(bm_unlock))?;
        self.at_func("dm_bm_flush", Box::new(bm_flush))?;
        self.at_func("dm_bm_prefetch", Box::new(bm_prefetch))?;
        self.at_func("dm_bm_is_read_only", Box::new(bm_is_read_only))?;
        self.at_func("dm_bm_set_read_only", Box::new(bm_set_read_only))?;
        self.at_func("dm_bm_set_read_write", Box::new(bm_set_read_write))?;
        self.at_func("dm_bm_checksum", Box::new(bm_checksum))?;
        self.at_func("printk", Box::new(printk))?;
        Ok(())
    }
}

//-------------------------------

// FIXME: move somewhere else
pub fn error_string(errno: i32) -> String {
    let mut buf = [0 as c_char; 512];

    let p = buf.as_mut_ptr();
    unsafe {
        if strerror_r(errno as c_int, p, buf.len()) < 0 {
            panic!("strerror_r failure");
        }

        let p = p as *const _;
        str::from_utf8(CStr::from_ptr(p).to_bytes())
            .unwrap()
            .to_owned()
    }
}

//-------------------------------

// A smart ptr to a Fixture that automatically frees
// a ptr in the guest when it is dropped.
pub struct AutoGPtr<'a> {
    fix: &'a mut Fixture,
    ptr: Addr,
}

impl<'a> AutoGPtr<'a> {
    pub fn new(fix: &'a mut Fixture, ptr: Addr) -> Self {
        AutoGPtr { fix, ptr }
    }
}

impl<'a> Drop for AutoGPtr<'a> {
    fn drop(&mut self) {
        self.fix
            .vm
            .mem
            .free(self.ptr)
            .expect(&format!("couldn't free guest ptr {:?}", self.ptr));
    }
}

impl<'a> Deref for AutoGPtr<'a> {
    type Target = Fixture;
    fn deref(&self) -> &Self::Target {
        self.fix
    }
}

impl<'a> DerefMut for AutoGPtr<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.fix
    }
}

pub fn auto_alloc<'a>(fix: &'a mut Fixture, len: usize) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = fix.vm.mem.alloc(len)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

pub fn auto_guest<'a, G: Guest>(fix: &'a mut Fixture, v: &G, perms: u8) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = alloc_guest::<G>(&mut fix.vm.mem, v, perms)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

//-------------------------------

pub fn printk(fix: &mut Fixture) -> Result<()> {
    let msg = fix.vm.mem.read_string(Addr(fix.vm.reg(A0)))?;
    info!("printk(\"{}\", 0x{:x}, 0x{:x}, 0x{:x})", &msg[2..], fix.vm.reg(A1), fix.vm.reg(A2), fix.vm.reg(A3));
    fix.vm.ret(0);
    Ok(())
}

pub fn memcpy(fix: &mut Fixture) -> Result<()> {
    let dest = Addr(fix.vm.reg(A0));
    let src = Addr(fix.vm.reg(A1));
    let len = fix.vm.reg(A2);

    // Let's check the bounds before allocating the intermediate buffer.
    fix.vm.mem.check_perms(src, Addr(src.0 + len), PERM_READ)?;
    fix.vm.mem.check_perms(dest, Addr(dest.0 + len), PERM_WRITE)?;

    let mut bytes = vec![0u8; len as usize];
    fix.vm.mem.read(src, &mut bytes, PERM_READ)?;
    fix.vm.mem.write(dest, &bytes, PERM_WRITE)?;
    fix.vm.ret(dest.0);
    Ok(())
}

pub fn kmalloc(fix: &mut Fixture) -> Result<()> {
    let len = fix.vm.reg(Reg::A0);
    let ptr = fix.vm.mem.alloc(len as usize)?;
    fix.vm.ret(ptr.0);
    Ok(())
}

pub fn kfree(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(Reg::A0));
    fix.vm.mem.free(ptr)?;
    fix.vm.ret(0);
    Ok(())
}

pub fn memset(fix: &mut Fixture) -> Result<()> {
    let base = Addr(fix.vm.reg(A0));
    let v = fix.vm.reg(A1) as u8;
    let len = fix.vm.reg(A2) as usize;
    let mut bytes = vec![0u8; len];
    for b in &mut bytes {
        *b = v;
    }
    fix.vm.mem.write(base, &mut bytes, PERM_WRITE)?;
    fix.vm.ret(0);
    Ok(())
}

//-------------------------------

// Guest types must always consume the same amount of contiguous guest
// memory.
pub trait Guest {
    fn guest_len() -> usize;
    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()>;
    fn unpack<R: Read>(r: &mut R) -> io::Result<Self>
    where
        Self: std::marker::Sized;
}

// Allocates space on the guest and copies 'bytes' into it.
pub fn alloc_guest<G: Guest>(mem: &mut Memory, v: &G, perms: u8) -> Result<Addr> {
    let mut bytes = vec![0; G::guest_len()];
    let mut w = Cursor::new(&mut bytes);
    v.pack(&mut w)?;
    let ptr = mem.alloc_perms(bytes.len(), perms)?;
    mem.write(ptr, &bytes, 0)?;
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

// Reads and frees a guest value.
pub fn free_guest<G: Guest>(mem: &mut Memory, ptr: Addr) -> Result<G> {
    let v = read_guest(mem, ptr)?;
    mem.free(ptr)?;
    Ok(v)
}

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
struct BlockManager {
    block_size: u64,
    nr_blocks: u64,
    blocks: BTreeMap<u64, Block>,
    read_only: bool,
}

fn bm_create(fix: &mut Fixture) -> Result<()> {
    let bdev_ptr = fix.vm.reg(A0);
    let block_size = fix.vm.reg(A1);
    let _max_held_per_thread = fix.vm.reg(A2);

    let nr_blocks = fix.vm.mem.read_into::<u64>(Addr(bdev_ptr), PERM_READ)?;

    let bm = Box::new(BlockManager {
        block_size,
        nr_blocks,
        blocks: BTreeMap::new(),
        read_only: false,
    });

    let guest_addr = fix.vm.mem.alloc(4)?;
    fix.user_data.insert(guest_addr, bm);

    fix.vm.ret(guest_addr.0);
    Ok(())
}

fn bm_destroy(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.remove::<BlockManager>(Addr(bm_ptr))?;

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

fn bm_block_size(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let block_size = {
        let bm = fix.user_data.get_ref::<BlockManager>(bm_ptr)?;
        bm.block_size
    };
    fix.vm.ret(block_size);
    Ok(())
}

fn bm_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = Addr(fix.vm.reg(A0));
    let nr_blocks = {
        let bm = fix.user_data.get_ref::<BlockManager>(bm_ptr)?;
        bm.nr_blocks
    };
    fix.vm.ret(nr_blocks);
    Ok(())
}

fn bm_read_lock(fix: &mut Fixture) -> Result<()> {
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
    fix.vm.ret(0);
    Ok(())
}

fn bm_write_lock(fix: &mut Fixture) -> Result<()> {
    write_lock_(fix, false)
}

fn bm_write_lock_zero(fix: &mut Fixture) -> Result<()> {
    write_lock_(fix, true)
}

fn bm_unlock(fix: &mut Fixture) -> Result<()> {
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

fn bm_block_location(fix: &mut Fixture) -> Result<()> {
    let block_ptr = fix.vm.reg(A0);
    // FIXME: this needlessly copies the data across.
    let gb = read_guest::<GBlock>(&mut fix.vm.mem, Addr(block_ptr))?;
    fix.vm.ret(gb.loc);
    Ok(())
}

fn bm_block_data(fix: &mut Fixture) -> Result<()> {
    let block_ptr = fix.vm.reg(A0);
    fix.vm.ret(block_ptr + 16);
    Ok(())
}

fn bm_flush(fix: &mut Fixture) -> Result<()> {
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
fn bm_prefetch(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let _bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    let _loc = fix.vm.reg(A1);

    fix.vm.ret(0);
    Ok(())
}

fn bm_is_read_only(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    let result = if bm.read_only { 1 } else { 0 };
    fix.vm.ret(result);
    Ok(())
}

fn bm_set_read_only(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    bm.read_only = true;
    fix.vm.ret(0);
    Ok(())
}

fn bm_set_read_write(fix: &mut Fixture) -> Result<()> {
    let bm_ptr = fix.vm.reg(A0);
    let bm = fix.user_data.get_mut::<BlockManager>(Addr(bm_ptr))?;
    bm.read_only = false;
    fix.vm.ret(0);
    Ok(())
}

fn bm_checksum(fix: &mut Fixture) -> Result<()> {
    let data = Addr(fix.vm.reg(A0));
    let len = fix.vm.reg(A1);
    let init_xor = fix.vm.reg(A2) as u32;

    let mut buf = vec![0u8; len as usize];
    fix.vm.mem.read(data, &mut buf, PERM_READ)?;
    let mut csum = crc32c(&buf) ^ 0xffffffff;
    csum = csum ^ init_xor;

    fix.vm.ret(csum as u64);
    Ok(())
}

//-------------------------------
