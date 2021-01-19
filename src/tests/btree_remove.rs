use crate::breakpoint::Stub;
use crate::decode::Reg;
use crate::loader::*;
use crate::memory::{Addr, Heap, PERM_EXEC};
use crate::vm::*;
use crate::test_runner::*;

use anyhow::{anyhow, Result};
use log::{info};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//-------------------------------

#[allow(dead_code)]
struct Fixture {
    vm: VM,
    symbols: BTreeMap<String, elf::types::Symbol>,
    heap: Heap,
}

impl Fixture {
    fn new<P: AsRef<Path>>(module: P) -> Result<Self> {
        let mut vm = VM::new();
        let symbols = load_elf(&mut vm.mem, module)?;

        // Setup the stack and heap
        vm.setup_stack(8 * 1024)?;
        let heap = vm.setup_heap(64 * 1024)?;

        Ok(Fixture { vm, symbols, heap })
    }

    fn lookup_fn(&self, func: &str) -> Result<Addr> {
        if let Some(addr) = self.symbols.get(func) {
            Ok(Addr(addr.value))
        } else {
            Err(anyhow!("couldn't lookup symbol '{}'", func))
        }
    }

    fn call(&mut self, func: &str) -> Result<u64> {
        let entry = self.lookup_fn(func)?;
        let vm = &mut self.vm;

        // We need an ebreak instruction to return control to us.
        let exit_addr = Addr(0x100);
        let ebreak_inst = 0b00000000000100000000000001110011u32; // FIXME: write an assembler
        vm.mem
            .mmap_bytes(exit_addr, &ebreak_inst.to_le_bytes(), PERM_EXEC)?;
        vm.set_reg(Reg::Ra, exit_addr.0);
        vm.set_pc(entry);

        match vm.run() {
            Ok(_) => {
                todo!();
            }
            Err(VmErr::EBreak) => {
                if vm.reg(Reg::PC) == exit_addr.0 {
                    // Successfully returned from the fn
                    return Ok(self.vm.reg(Reg::A0));
                } else {
                    eprintln!("{}", vm);
                    Err(VmErr::EBreak)?
                }
            }
            Err(e) => {
                eprintln!("{}", vm);
                Err(e)?
            }
        }
    }

    // Stubs a function to just return a particular value.
    fn stub(&mut self, func: &str, v: u64) -> Result<()> {
        self.vm
            .add_breakpoint(self.lookup_fn(func)?, Box::new(Stub::new(func, v)));
        Ok(())
    }
}

//-------------------------------

// pretend tests
fn test_test1(mut fix: Fixture) -> Result<()> {
    fix.stub("crc32c", 123)?;
    fix.call("test1")?;
    assert!(fix.vm.reg(Reg::A0) == 123);
    Ok(())
}

struct BTreeRemoveSuite {
    module_path: PathBuf,
}

impl TestSuite for BTreeRemoveSuite {
    fn get_paths(&self) -> Vec<TestPath> {
        vec!["/pdata/btree/remove/test1",
             "/pdata/btree/remove/test2",
             "/pdata/btree/remove/test3"].iter().map(|s| s.to_string()).collect()
    }

    fn exec(&self, _p: &TestPath) -> Result<()> {
        let fix = Fixture::new(self.module_path.clone())?;
        test_test1(fix)
    }
}

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    info!("registered /pdata/btree/remove tests");
    let mut module_path = PathBuf::from(runner.get_kernel_dir());
    module_path.push("drivers/md/persistent-data/dm-persistent-data.ko");
    runner.register_suite(Box::new(BTreeRemoveSuite {module_path}));
    Ok(())
}

//-------------------------------
