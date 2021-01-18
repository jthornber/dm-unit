extern crate dm_unit;
extern crate log;

use anyhow::{anyhow, Result};
use clap::{App, Arg};
use dm_unit::decode::Reg;
use dm_unit::loader::*;
use dm_unit::memory::{Addr, Heap, PERM_EXEC};
use dm_unit::vm;
use dm_unit::vm::*;
use log::info;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//--------------------------

#[allow(dead_code)]
struct Fixture {
    vm: VM,
    symbols: BTreeMap<String, elf::types::Symbol>,
    heap: Heap,
}

struct RetBP {
    v: u64,
}

impl Breakpoint for RetBP {
    fn exec(&mut self, vm: &mut VM) -> vm::Result<()> {
        vm.set_reg(Reg::A0, self.v);
        vm.ret();
        Ok(())
    }
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

    fn call(&mut self, func: &str) -> Result<()> {
        let entry = self.lookup_fn(func)?;
        info!("Entry point: {:#x}", entry);

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
                    return Ok(());
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
            .add_breakpoint(self.lookup_fn(func)?, Box::new(RetBP { v }));
        Ok(())
    }
}

fn main() -> Result<()> {
    env_logger::init();

    let parser = App::new("dm-unit")
        .version("0")
        .about("Unit test framework for device mapper kernel modules")
        .arg(
            Arg::with_name("INPUT")
                .help("RISCV64imac kernel module to load (must be dm-persistent-data.ko)")
                .required(true)
                .index(1),
        );

    let matches = parser.get_matches();
    let module = Path::new(matches.value_of("INPUT").unwrap());
    let mut fix = Fixture::new(PathBuf::from(module))?;

    let sym = "crc32c";
    let global = fix.symbols.get(sym).unwrap();
    info!("{} = {}", sym, global);

    fix.stub("crc32c", 123)?;
    fix.call("test1")?;
    //   info!("{}", fix.vm);
    Ok(())
}
