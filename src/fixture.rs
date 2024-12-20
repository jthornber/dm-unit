use crate::anymap::*;
use crate::emulator::loader::*;
use crate::emulator::memory::*;
use crate::emulator::memory::{Addr, PERM_EXEC};
use crate::emulator::riscv::Reg;
use crate::emulator::stack_trace::*;
use crate::emulator::vm::*;
use crate::errno::*;
use crate::guest::*;
use crate::lock_check::*;

use anyhow::{anyhow, Context, Result};
use log::*;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use Reg::*;

//-------------------------------

type FixCallback = Box<dyn Fn(&mut Fixture) -> Result<()>>;

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

    kernel_dir: PathBuf,

    pub lock_check: LockCheck,

    // Optional arguments for tests
    pub args: BTreeSet<String>,
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
        module.push(self.relative_path);
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

pub const BUFIO_MOD: KernelModule = KernelModule {
    basename: "dm-bufio",
    relative_path: "drivers/md/dm-bufio.ko",
};

pub const THIN_MOD: KernelModule = KernelModule {
    basename: "dm-thin-pool",
    relative_path: "drivers/md/dm-thin-pool.ko",
};

pub const CACHE_MOD: KernelModule = KernelModule {
    basename: "dm-cache",
    relative_path: "drivers/md/dm-cache.ko",
};

pub const CACHE_SMQ_MOD: KernelModule = KernelModule {
    basename: "dm-cache-smq",
    relative_path: "drivers/md/dm-cache-smq.ko",
};

#[derive(Debug)]
pub struct CallError {
    pub func: String,
    pub ret: i32,
}

impl CallError {
    pub fn new(func: &str, ret: i32) -> Self {
        Self {
            func: func.to_string(),
            ret,
        }
    }

    pub fn errno(&self) -> Option<i32> {
        match self.ret {
            r if r < 0 => Some(-r),
            _ => None,
        }
    }

    pub fn is_errno(&self, errno: std::ffi::c_int) -> bool {
        self.ret == -errno
    }
}

impl std::error::Error for CallError {}

impl std::fmt::Display for CallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.ret < 0 {
            write!(f, "{} failed: {}", self.func, error_string(-self.ret))
        } else {
            write!(f, "{} failed: {}", self.func, self.ret)
        }
    }
}

impl Fixture {
    pub fn prep_memory<P: AsRef<Path> + Clone>(
        kernel_dir: P,
        kmodules: &[KernelModule],
    ) -> Result<(LoaderInfo, Memory)> {
        let mut modules = Vec::new();
        for km in kmodules {
            modules.push(km.path(kernel_dir.clone()));
        }

        let heap_begin = Addr(1024 * 1024 * 256);
        let heap_end = Addr(heap_begin.0 + (256 * 1024 * 1024));
        let mut mem = Memory::new(heap_begin, heap_end);
        let loader_info = load_modules(&mut mem, &modules[0..])?;
        Ok((loader_info, mem))
    }

    pub fn new<P: AsRef<Path>>(
        kernel_dir: &P,
        loader_info: LoaderInfo,
        mem: Memory,
        jit: bool,
        args: BTreeSet<String>,
    ) -> Result<Self> {
        let mut vm = VM::new(mem, jit);

        // Setup the stack and heap
        vm.setup_stack(8 * 1024)?;

        Ok(Fixture {
            vm,
            loader_info,
            breakpoints: BTreeMap::new(),
            trace_indent: 0,
            contexts: AnyMap::default(),
            kernel_dir: std::fs::canonicalize(PathBuf::from(kernel_dir.as_ref())).unwrap(),
            lock_check: LockCheck::default(),
            args,
        })
    }

    pub fn get_lock(&mut self, kind: LockType, addr: Addr) {
        self.lock_check.lock(kind, addr, Addr(self.vm.reg(Reg::Ra)));
    }

    pub fn put_lock(&mut self, kind: LockType, addr: Addr) -> Result<()> {
        if let Err(l) = self.lock_check.unlock(kind, addr) {
            Err(anyhow!("lock mismatch: {:?}", l))
        } else {
            Ok(())
        }
    }

    /// Checks if a spin lock is held and raises an error if so.
    pub fn may_sleep(&self) -> Result<()> {
        if self.lock_check.spin_held() {
            let spin_pc = self.lock_check.most_recent_spin_pc().unwrap();
            let loc = self.get_loc_from_addr(spin_pc)?;
            return Err(anyhow!(
                "may_sleep() called with spin lock taken at {}",
                loc
            ));
        }

        Ok(())
    }

    fn lookup_fn(&self, func: &str) -> Result<Addr> {
        if let Some(addr) = self.loader_info.get_sym(func) {
            Ok(addr)
        } else {
            Err(anyhow!("couldn't lookup symbol '{}'", func))
        }
    }

    pub fn get_loc_from_addr(&self, addr: Addr) -> Result<String> {
        let debug = self.loader_info.debug.lock().unwrap();
        let mut stack = Vec::new();
        debug.addr2frames(&self.kernel_dir, addr, true, &mut stack)?;
        if stack.len() > 0 {
            Ok(stack.last().unwrap().to_string())
        } else {
            Ok(format!("{:?}", addr))
        }
    }

    fn get_stack_trace(&self) -> Result<String> {
        // We use the debug info to convert the PC to a kernel source line.
        let debug = self.loader_info.debug.lock().unwrap();
        let mut stack = Vec::new();

        let mut fp = self.vm.reg(S0);
        let mut pc = self.vm.reg(PC);
        let mut bottom = true;

        // Walk the frame pointers
        loop {
            debug.addr2frames(&self.kernel_dir, Addr(pc), bottom, &mut stack)?;
            bottom = false;

            if let Ok(frame) =
                read_guest::<StackFrame>(&self.vm.mem, Addr(fp - StackFrame::guest_len() as u64))
            {
                fp = frame.fp;
                pc = frame.ra;
            } else {
                break;
            }
        }

        // One location per line, with a blank line before and after.
        let mut str = String::new();
        str.push_str("\nGuest stack:\n");
        for loc in stack.iter().rev() {
            str.push_str(&loc.to_string());
            str.push_str("\n");
        }
        str.push_str("\n");

        Ok(str)
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
                        let r = (*callback)(self);
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
                    let addr = Addr(self.vm.reg(Reg::PC));
                    if let Some(global) = self.loader_info.get_rmap(addr) {
                        let loc = self.get_loc_from_addr(addr)?;
                        warn!("{}: unstubbed global called '{}'", loc, global);
                        return Err(anyhow!("unstubbed global access '{}'", global));
                    }

                    return Err(VmErr::EBreak.into());
                }
                err => err?,
            }
        }
    }

    // Sometimes we need a unique location to set a breakpoint, to do this
    // we allocate a word on the heap and fill it out with an ebreak.
    // FIXME: memleak
    pub fn alloc_ebreak(&mut self) -> Result<Addr> {
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

            self.bp_at_addr(exit_addr, Box::new(callback));
        }

        let result = self.run_vm();
        self.vm.mem.free(exit_addr)?;
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
                    Err(e).with_context(|| {
                        self.get_stack_trace()
                            .unwrap_or(format!("0x{:x}", self.vm.reg(PC)))
                    })
                }
            }
        }
    }

    pub fn call(&mut self, func: &str) -> Result<()> {
        // debug!(">>> {}()", func);
        self.call_at(self.lookup_fn(func)?)?;
        // debug!("<<< {}()", func);
        Ok(())
    }

    // Use this to call functions that return an int errno.
    // To extract the returned errno, the caller has to downcast the returned
    // error object to CallError, e.g.,
    //
    // let e = fix.call_with_errno("dm_btree_cursor_next").unwrap_err();
    // assert!(matches!(e.downcast_ref::<CallError>(),
    //   Some(err) if err.is_errno(libc::ENODATA)
    // ));
    // assert_eq!(e.downcast_ref::<CallError>().and_then(|err| err.errno()),
    //   Some(libc::ENODATA));
    pub fn call_with_errno(&mut self, tm_func: &str) -> Result<()> {
        self.call(tm_func)?;
        let r = self.vm.reg(A0) as i64 as i32;
        if r != 0 {
            return Err(anyhow::Error::new(CallError::new(tm_func, r)));
        }
        Ok(())
    }

    pub fn call_at_with_errno_(&mut self, loc: Addr) -> Result<()> {
        self.call_at(loc)?;
        let r = self.vm.reg(A0) as i64 as i32;
        if r != 0 {
            return Err(anyhow::Error::new(CallError::new(
                &format!("call_at {:#x}", loc.0),
                r,
            )));
        }
        Ok(())
    }

    pub fn call_at_with_errno(&mut self, loc: Addr) -> Result<()> {
        // debug!(">>> 0x{:x}", loc.0);
        self.call_at_with_errno_(loc)?;
        // debug!("<<< 0x{:x}", loc.0);
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
        self.at_func(func, Box::new(callback))
    }

    pub fn const_callback(&mut self, v: u64) -> Result<Addr> {
        let callback = move |fix: &mut Fixture| {
            fix.vm.ret(v);
            Ok(())
        };
        let ptr = self.alloc_ebreak()?;
        self.bp_at_addr(ptr, Box::new(callback));
        Ok(ptr)
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
        let estr = if (-1024..0).contains(&err) {
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
            move |fix: &mut Fixture| {
                fix.trace_exit(&name, fix.vm.reg(A0));
                fix.vm.pop_reg(Ra)?;
                fix.vm.set_reg(PC, fix.vm.reg(Ra));
                Ok(())
            }
        };

        self.at_func(func, Box::new(entry_callback))?;
        self.bp_at_addr(trampoline, Box::new(exit_callback));

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

    /// Takes ownership of the pointer and returns its value.
    ///
    /// The method sets the pointer to zero to prevent double-freeing and returns its original value.
    ///
    /// # Returns
    ///
    /// The value of the pointer.
    pub fn take(&mut self) -> Addr {
        let ptr = self.ptr;
        self.ptr.0 = 0;
        ptr
    }
}

impl Drop for AutoGPtr<'_> {
    fn drop(&mut self) {
        if self.ptr.is_null() {
            return;
        }

        self.fix
            .vm
            .mem
            .free(self.ptr)
            .unwrap_or_else(|_| panic!("couldn't free guest ptr {:?}", self.ptr));
    }
}

impl Deref for AutoGPtr<'_> {
    type Target = Fixture;
    fn deref(&self) -> &Self::Target {
        self.fix
    }
}

impl DerefMut for AutoGPtr<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.fix
    }
}

/// Create an auto ptr to a guest allocation of size |len|.  The memory
/// will have read/write permissions.
pub fn auto_alloc(fix: &mut Fixture, len: usize) -> Result<(AutoGPtr, Addr)> {
    let ptr = fix
        .vm
        .mem
        .alloc_bytes(vec![0u8; len], PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

pub fn auto_alloc_vec<'a, G: Guest>(
    fix: &'a mut Fixture,
    vals: &'a [G],
) -> Result<(AutoGPtr<'a>, Vec<Addr>)> {
    let len = G::guest_len() * vals.len();
    let (mut fix, ptr) = auto_alloc(fix, len)?;

    for (i, v) in vals.iter().enumerate() {
        let v_ptr = Addr(ptr.0 + (G::guest_len() * i) as u64);
        write_guest(&mut fix.vm.mem, v_ptr, v)?;
    }

    let ptrs = (0..vals.len())
        .map(|i| Addr(ptr.0 + (G::guest_len() * i) as u64))
        .collect();

    Ok((fix, ptrs))
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
