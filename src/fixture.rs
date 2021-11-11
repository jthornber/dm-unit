use crate::anymap::*;
use crate::emulator::loader::*;
use crate::emulator::memory::*;
use crate::emulator::memory::{Addr, PERM_EXEC};
use crate::emulator::riscv::Reg;
use crate::emulator::vm::*;
use crate::guest::*;

use anyhow::{anyhow, Result};
use libc::{c_int, strerror_r};
use log::*;
use std::collections::BTreeMap;
use std::ffi::CStr;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use Reg::*;

//-------------------------------

type FixCallback = Arc<Mutex<dyn Fn(&mut Fixture) -> Result<()>>>;

#[allow(dead_code)]
pub struct Fixture {
    pub vm: VM,

    loader_info: LoaderInfo,

    // Associates breakpoint addresses with callback functions.
    breakpoints: BTreeMap<u64, FixCallback>,

    // Current indentation for function tracing.
    trace_indent: usize,

    // A useful place to store host structures against a guest
    // address.
    pub contexts: AnyMap<Addr>,
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct KernelModule {
    basename: &'static str,
    relative_path: &'static str,
}

impl KernelModule {
    pub fn path<P: AsRef<Path>>(&self, kernel_dir: P) -> PathBuf {
        let mut module = PathBuf::new();
        module.push(kernel_dir);
        module.push(self.relative_path.to_string());
        module
    }

    pub fn name(&self) -> String {
        self.basename.to_string()
    }
}

pub const PDATA_MOD: KernelModule = KernelModule {
    basename: "dm-persistent-data",
    relative_path: "drivers/md/persistent-data/dm-persistent-data.ko",
};

pub const THIN_MOD: KernelModule = KernelModule {
    basename: "dm-thin-pool",
    relative_path: "drivers/md/dm-thin-pool.ko",
};

pub const THIN2_MOD: KernelModule = KernelModule {
    basename: "dm-thin2",
    relative_path: "drivers/md/dm-thin2.ko",
};

pub const CACHE_MOD: KernelModule = KernelModule {
    basename: "dm-cache",
    relative_path: "drivers/md/dm-cache.ko",
};

pub const CACHE_SMQ_MOD: KernelModule = KernelModule {
    basename: "dm-cache-smq",
    relative_path: "drivers/md/dm-cache-smq.ko",
};

pub const RBTREE_MOD: KernelModule = KernelModule {
    basename: "rbtree",
    relative_path: "lib/rbtree.ko",
};

impl Fixture {
    pub fn prep_memory<P: AsRef<Path> + Clone>(
        kernel_dir: P,
        kmodules: &[KernelModule],
    ) -> Result<(LoaderInfo, Memory)> {
        let mut modules = Vec::new();
        for km in kmodules {
            modules.push(km.path(kernel_dir.clone()));
        }

        let heap_begin = Addr(1024 * 1024 * 1024 * 3);
        // let heap_end = Addr(heap_begin.0 + (32 * 1024 * 1024));
        let heap_end = Addr(heap_begin.0 + (256 * 1024 * 1024));
        let mut mem = Memory::new(heap_begin, heap_end);
        let loader_info = load_modules(&mut mem, &modules[0..])?;
        Ok((loader_info, mem))
    }

    pub fn new(loader_info: LoaderInfo, mem: Memory, jit: bool) -> Result<Self> {
        let mut vm = VM::new(mem, jit);

        // Setup the stack and heap
        vm.setup_stack(8 * 1024)?;

        Ok(Fixture {
            vm,
            loader_info,
            breakpoints: BTreeMap::new(),
            trace_indent: 0,
            contexts: AnyMap::default(),
        })
    }

    fn lookup_fn(&self, func: &str) -> Result<Addr> {
        if let Some(addr) = self.loader_info.get_sym(func) {
            Ok(addr)
        } else {
            Err(anyhow!("couldn't lookup symbol '{}'", func))
        }
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

                    /*
                    // This debug is expensive, but useful when bug hunting.
                    if let Some(global) = self.loader_info.get_rmap(Addr(self.vm.reg(Reg::PC))) {
                        debug!("calling stub for {}", global);
                    }
                    */

                    if let Some(callback) = self.breakpoints.remove(&loc) {
                        let inner = callback.lock().unwrap();
                        let r = (*inner)(self);
                        drop(inner);
                        self.breakpoints.insert(loc, callback);
                        r?;
                    } else {
                        return Err(anyhow!(
                            "Breakpoint at {:x?} without callback",
                            self.vm.reg(PC)
                        ));
                    }
                }
                Err(VmErr::EBreak) => {
                    debug!("hit ebreak at {:?}", self.vm.reg(Reg::PC));
                    if let Some(global) = self.loader_info.get_rmap(Addr(self.vm.reg(Reg::PC))) {
                        warn!(
                            "Unexpected ebreak instruction.  This could be because:\n\
     A BUG() function has been called.\n\
     An unstubbed global called ({}).",
                            global
                        );
                        return Err(anyhow!("unstubbed global access '{}'", global));
                    } else {
                        return Err(VmErr::EBreak.into());
                    }
                }
                err => {
                    debug!("\n{}", self.vm);
                    err?
                }
            }
        }
    }

    // Sometimes we need a unique location to set a breakpoint, to do this
    // we allocate a word on the heap and fill it out with an ebreak.
    // FIXME: memleak
    fn alloc_ebreak(&mut self) -> Result<Addr> {
        // We need a unique address return control to us.
        let ptr = self.vm.mem.alloc_bytes(vec![0u8; 4], PERM_EXEC)?;

        // Fill out a c.ebreak at this address because basic blocks are decoded
        // before breakpoints are checked.
        let ret: u16 = 0b1001000000000010;
        let bytes = (ret as u32).to_le_bytes();
        self.vm.mem.write(ptr, &bytes, 0)?;
        Ok(ptr)
    }

    // Call a named function in the vm.  Returns the contents of Ra.
    pub fn call_at(&mut self, code: Addr) -> Result<()> {
        use Reg::*;

        // We need a unique address return control to us.
        let exit_addr = self.alloc_ebreak()?;

        self.vm.push_reg(Ra)?;
        self.vm.set_reg(Ra, exit_addr.0);
        self.vm.set_pc(code);

        let completed = Arc::new(AtomicBool::new(false));
        {
            let completed = completed.clone();

            let callback = move |fix: &mut Fixture| {
                completed.store(true, Ordering::Relaxed);
                fix.vm.pop_reg(Ra)?;
                Err(anyhow!("call complete, exiting"))
            };

            self.bp_at_addr(exit_addr, Arc::new(Mutex::new(callback)));
        }

        let result = self.run_vm();
        self.vm.mem.unmap(exit_addr)?;
        match result {
            Ok(_) => {
                // Not sure how we can get here
                todo!();
            }
            Err(e) => {
                if completed.load(Ordering::Relaxed) {
                    self.bp_rm(exit_addr);
                    Ok(())
                } else {
                    Err(e)
                }
            }
        }
    }

    pub fn call(&mut self, func: &str) -> Result<()> {
        self.call_at(self.lookup_fn(func)?)
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

    pub fn call_at_with_errno(&mut self, loc: Addr) -> Result<()> {
        self.call_at(loc)?;
        let r = self.vm.reg(A0) as i64 as i32;
        if r != 0 {
            if r < 0 {
                return Err(anyhow!("failed: {}", error_string(-r)));
            } else {
                return Err(anyhow!("failed: {}", r));
            }
        }
        Ok(())
    }

    pub fn bp_at_addr(&mut self, loc: Addr, callback: FixCallback) {
        self.vm.add_breakpoint(loc);
        self.breakpoints.insert(loc.0, callback);
    }

    pub fn bp_rm(&mut self, loc: Addr) {
        self.vm.rm_breakpoint(loc);
        self.breakpoints.remove(&loc.0);
    }

    pub fn at_func(&mut self, name: &str, callback: FixCallback) -> Result<()> {
        let func_addr = self.lookup_fn(name)?;
        self.bp_at_addr(func_addr, callback);
        Ok(())
    }

    // Stubs a function to just return a particular value.
    pub fn stub(&mut self, func: &str, v: u64) -> Result<()> {
        let callback = move |fix: &mut Fixture| {
            fix.vm.ret(v);
            Ok(())
        };
        self.at_func(func, Arc::new(Mutex::new(callback)))
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
        let trampoline = self.alloc_ebreak()?;

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
            let name = name;
            move |fix: &mut Fixture| {
                fix.trace_exit(&name, fix.vm.reg(A0));
                fix.vm.pop_reg(Ra)?;
                fix.vm.set_reg(PC, fix.vm.reg(Ra));
                Ok(())
            }
        };

        self.at_func(func, Arc::new(Mutex::new(entry_callback)))?;
        self.bp_at_addr(trampoline, Arc::new(Mutex::new(exit_callback)));

        Ok(())
    }

    pub fn log_func_calls(&self, func: &str) -> Result<()> {
        let ptr = self.lookup_fn(func)?;
        if let Some(stats) = self.vm.get_bb_stats(ptr) {
            debug!("{}: {} calls", func, stats.hits);
        } else {
            debug!("{}: never called", func);
        }

        Ok(())
    }

    pub fn log_top_funcs(&mut self, mut count: usize) {
        // See which basic blocks start at a func entry point
        let bbs = self.vm.get_hot_basic_blocks();
        debug!("Top basic blocks:");
        for bb in &bbs {
            if count == 0 {
                break;
            }

            if let Some(name) = self.loader_info.get_rmap(bb.begin) {
                debug!("    {}:\t{}", name, bb.hits);
                count -= 1;
            }
        }
    }
}

//-------------------------------

// FIXME: move somewhere else
pub fn error_string(errno: i32) -> String {
    let mut buf = [0_i8; 512];

    let p = buf.as_mut_ptr();
    unsafe {
        if strerror_r(errno as c_int, p, buf.len()) < 0 {
            panic!("strerror_r failure");
        }

        let p = p as *const _;
        std::str::from_utf8(CStr::from_ptr(p).to_bytes())
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
            .unwrap_or_else(|_| panic!("couldn't free guest ptr {:?}", self.ptr));
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

pub fn auto_alloc(fix: &mut Fixture, len: usize) -> Result<(AutoGPtr, Addr)> {
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0u8; len], PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

/// Allocates an excutable chunk of memory that we can use to fake a callback.
/// You will have to hook the return addr.
pub fn auto_ebreak(fix: &mut Fixture) -> Result<(AutoGPtr, Addr)> {
    // We need a unique address return control to us.
    let ptr = fix.vm.mem.alloc_bytes(vec![0u8; 4], PERM_EXEC)?;

    // Fill out a c.ebreak at this address because basic blocks are decoded
    // before breakpoints are checked.
    let ret: u16 = 0b1001000000000010;
    let bytes = (ret as u32).to_le_bytes();
    fix.vm.mem.write(ptr, &bytes, 0)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

pub fn auto_guest<'a, G: Guest>(
    fix: &'a mut Fixture,
    v: &G,
    perms: u8,
) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = alloc_guest::<G>(&mut fix.vm.mem, v, perms)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

//-------------------------------
