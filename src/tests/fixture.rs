use crate::decode::Reg;
use crate::loader::*;
use crate::memory::{Addr, Heap, PERM_EXEC, PERM_READ, PERM_WRITE};
use crate::vm::*;

use anyhow::{anyhow, Result};
use elf::types::Symbol;
use log::{debug, warn};
use std::any::Any;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use Reg::*;

//-------------------------------

type FixCallback = Box<dyn Fn(&mut Fixture) -> Result<()>>;

#[allow(dead_code)]
pub struct Fixture {
    pub vm: VM,
    symbols: BTreeMap<String, Symbol>,
    heap_base: Addr,
    heap: Heap,

    // Maps allocation block to len.
    allocations: BTreeMap<u64, usize>,

    // Associates breakpoint addresses with callback functions.
    // FIXME: make private
    pub breakpoints: BTreeMap<u64, FixCallback>,

    // Associates an address in the vm with rust user data.
    user_data: BTreeMap<u64, Box<dyn Any>>,
}

impl Fixture {
    pub fn new<P: AsRef<Path>>(kernel_dir: P) -> Result<Self> {
        let mut module = PathBuf::new();
        module.push(kernel_dir);
        module.push("drivers/md/persistent-data/dm-persistent-data.ko");

        let mut vm = VM::new();
        let symbols = load_elf(&mut vm.mem, module)?;

        // Setup the stack and heap
        vm.setup_stack(8 * 1024)?;

        let heap_base = Addr(1024 * 1024 * 1024 * 3);
        let heap_end = Addr(heap_base.0 + (64 * 1024));
        let heap = Heap::new(heap_base, heap_end);

        let allocations = BTreeMap::new();

        Ok(Fixture {
            vm,
            symbols,
            heap_base,
            heap,
            allocations,
            breakpoints: BTreeMap::new(),
            user_data: BTreeMap::new(),
        })
    }

    // Allocates a block on the heap with specific permissions.
    pub fn alloc_perms(&mut self, len: usize, perms: u8) -> Result<Addr> {
        // We allocate an extra word before and after the block to
        // detect overwrites.
        let extra_len = len + 8;
        let ptr = self.heap.alloc(extra_len)?;
        self.allocations.insert(ptr.0, extra_len);

        // mmap just the central part that may be used.
        let ptr = Addr(ptr.0 + 4);
        self.vm
            .mem
            .mmap(ptr, Addr(ptr.0 + len as u64), perms)?;

        Ok(ptr)
    }

    // Allocates a block on the heap with read/write permissions.  The
    // common case.
    pub fn alloc(&mut self, len: usize) -> Result<Addr> {
        self.alloc_perms(len, PERM_READ | PERM_WRITE)
    }

    pub fn free(&mut self, ptr: Addr) -> Result<()> {
        let heap_ptr = Addr(ptr.0 - 4);

        if let Some(_len) = self.allocations.remove(&heap_ptr.0) {
            self.heap.free(heap_ptr)?;
            self.vm.mem.unmap(ptr)?;
            Ok(())
        } else {
            Err(anyhow!("unable to free ptr at {:?}", ptr))
        }
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
    // FIXME: we need to support recursive calls.
    pub fn call(&mut self, func: &str) -> Result<u64> {
        let entry = self.lookup_fn(func)?;

        // We need a unique address return control to us.
        let exit_addr = self.alloc_perms(4, PERM_EXEC)?;
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
                    Ok(self.vm.reg(Reg::Ra))
                } else {
                    Err(e)
                }
            }
        }
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

    /// Attaches a standard set of global implementations.
    /// eg, kmalloc, kfree.
    pub fn standard_globals(&mut self) -> Result<()> {
        self.at_func("__kmalloc", Box::new(kmalloc))?;
        self.at_func("memset", Box::new(memset))?;
        self.at_func("kfree", Box::new(kfree))?;
        self.at_func("dm_bufio_client_create", Box::new(bufio_create))?;
        self.at_func("dm_bufio_client_destroy", Box::new(bufio_destroy))?;
        Ok(())
    }
}

//-------------------------------

pub fn kmalloc(fix: &mut Fixture) -> Result<()> {
    let len = fix.vm.reg(Reg::A0);
    let ptr = fix.alloc(len as usize)?;
    fix.vm.ret(ptr.0);
    Ok(())
}

pub fn kfree(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(Reg::A0));
    fix.free(ptr)?;
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

#[allow(dead_code)]
struct Bufio {
    ptr: Addr,

    bdev: u64,
    block_size: u64,
    reserved_buffers: u64,
    aux_size: u64,
    alloc_cb: Addr,
    write_cb: Addr,
}

impl Bufio {
    fn new(fix: &mut Fixture) -> Result<Self> {
        let bdev = fix.vm.reg(A0);
        let block_size = fix.vm.reg(A1);
        let reserved_buffers = fix.vm.reg(A2);
        let aux_size = fix.vm.reg(A3);
        let alloc_cb = fix.vm.reg(A4);
        let write_cb = fix.vm.reg(A5);

        assert!(block_size == 4096);
        assert!(aux_size == 16);

        let ptr = fix.alloc(4)?;

        Ok(Bufio {
            ptr,
            bdev,
            block_size,
            reserved_buffers,
            aux_size,
            alloc_cb: Addr(alloc_cb),
            write_cb: Addr(write_cb),
        })
    }
}

pub fn bufio_create(fix: &mut Fixture) -> Result<()> {
    let bufio = Bufio::new(fix)?;

    let ptr = bufio.ptr.clone();
    fix.user_data.insert(bufio.ptr.0, Box::new(bufio));
    fix.vm.ret(ptr.0);

    Ok(())
}

pub fn bufio_destroy(fix: &mut Fixture) -> Result<()> {
    let ptr = fix.vm.reg(A0);

    // FIXME: make this a utility fn
    let user_data = fix
        .user_data
        .remove(&ptr)
        .expect("couldn't look up bufio user data");
    match user_data.downcast_ref::<Bufio>() {
        Some(_bufio) => {
            debug!("found user data");
            fix.free(Addr(ptr))?;
            fix.vm.ret(0);
        }
        None => {
            return Err(anyhow!("Incorrect user data type, expected bufio"));
        }
    }

    Ok(())
}

//-------------------------------
