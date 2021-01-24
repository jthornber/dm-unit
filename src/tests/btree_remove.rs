use crate::decode;
use crate::decode::Reg;
use crate::loader::*;
use crate::memory::{Addr, Heap, PERM_EXEC, PERM_READ, PERM_WRITE};
use crate::test_runner::*;
use crate::vm::*;

use anyhow::{anyhow, Result};
use elf::types::Symbol;
use log::{debug, info, warn};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

//-------------------------------

#[allow(dead_code)]
pub struct Fixture {
    vm: VM,
    symbols: BTreeMap<String, Symbol>,
    heap_base: Addr,
    heap: Heap,

    // Maps allocation block to len.
    allocations: BTreeMap<u64, usize>,

    breakpoints: BTreeMap<u64, Box<dyn FnMut(&mut Fixture) -> Result<()>>>,
}

impl Fixture {
    fn new<P: AsRef<Path>>(kernel_dir: P) -> Result<Self> {
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
        })
    }

    pub fn alloc(&mut self, len: usize) -> Result<Addr> {
        // We allocate an extra word before and after the block to
        // detect overwrites.
        let extra_len = len + 8;
        let ptr = self.heap.alloc(extra_len)?;
        self.allocations.insert(ptr.0, extra_len);

        // mmap just the central part that may be used.
        let ptr = Addr(ptr.0 + 4);
        self.vm
            .mem
            .mmap(ptr, Addr(ptr.0 + len as u64), PERM_READ | PERM_WRITE)?;

        Ok(ptr)
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
                    let mut bps = BTreeMap::new();
                    std::mem::swap(&mut bps, &mut self.breakpoints);
                    if let Some(callback) = bps.get_mut(&loc) {
                        (*callback)(self)?;
                    } else {
                        return Err(anyhow!(
                            "Breakpoint at {:?} without callback",
                            self.vm.reg(Reg::PC)
                        ));
                    }
                    std::mem::swap(&mut bps, &mut self.breakpoints);
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

    fn call(&mut self, func: &str) -> Result<u64> {
        let entry = self.lookup_fn(func)?;

        // We need an ebreak instruction to return control to us.
        let exit_addr = Addr(0x100);
        let ebreak_inst = 0b00000000000100000000000001110011u32; // FIXME: write an assembler
        self.vm
            .mem
            .mmap_bytes(exit_addr, &ebreak_inst.to_le_bytes(), PERM_EXEC)?;
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

    fn at_addr(&mut self, loc: Addr, callback: Box<dyn FnMut(&mut Fixture) -> Result<()>>) {
        self.vm.add_breakpoint(loc);
        self.breakpoints.insert(loc.0, callback);
    }

    fn at_func(
        &mut self,
        name: &str,
        callback: Box<dyn FnMut(&mut Fixture) -> Result<()>>,
    ) -> Result<()> {
        let func_addr = self.lookup_fn(name)?;
        self.at_addr(func_addr, Box::new(callback));
        Ok(())
    }

    // Stubs a function to just return a particular value.
    fn stub(&mut self, func: &str, v: u64) -> Result<()> {
        let callback = move |fix: &mut Fixture| {
            fix.vm.ret(v);
            Ok(())
        };
        self.at_func(func, Box::new(callback))
    }
}

//-------------------------------

// pretend tests
struct Test1 {}

impl Test for Test1 {
    fn exec(&self, kernel_dir: &PathBuf) -> Result<()> {
        let mut fix = Fixture::new(kernel_dir)?;
        fix.stub("crc32c", 123)?;
        fix.call("test1")?;
        assert!(fix.vm.reg(Reg::A0) == 123);
        Ok(())
    }
}

struct Test2 {}

impl Test for Test2 {
    fn exec(&self, kernel_dir: &PathBuf) -> Result<()> {
        use decode::Reg::*;

        let mut fix = Fixture::new(kernel_dir)?;
        let kmalloc = {
            move |fix: &mut Fixture| {
                let len = fix.vm.reg(Reg::A0);
                let ptr = fix.alloc(len as usize)?;
                fix.vm.ret(ptr.0);
                Ok(())
            }
        };

        let memset = {
            move |fix: &mut Fixture| {
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
        };

        let kfree = {
            move |fix: &mut Fixture| {
                let ptr = Addr(fix.vm.reg(A0));
                fix.free(ptr)?;
                fix.vm.ret(0);
                Ok(())
            }
        };

        fix.at_func("__kmalloc", Box::new(kmalloc))?;
        fix.at_func("memset", Box::new(memset))?;
        fix.at_func("kfree", Box::new(kfree))?;
        fix.call("test2")?;
        Ok(())
    }
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    info!("registered /pdata/btree/remove tests");

    runner.register_test("/pdata/btree/remove/test1", Box::new(Test1 {}));
    runner.register_test("/pdata/btree/remove/test2", Box::new(Test2 {}));

    Ok(())
}

//-------------------------------
