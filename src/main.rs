extern crate riscv_emulator;

use anyhow::{anyhow, Result};
use clap::{App, Arg};
use elf;
use elf::types::*;
use riscv_emulator::memory::{Addr, Memory, PERM_EXEC, PERM_READ, PERM_WRITE};
use riscv_emulator::vm::*;
use std::path::{Path, PathBuf};

/// Emulator for riscv32i

//--------------------------

fn has_flag(flags: SectionFlag, item: SectionFlag) -> bool {
    (flags.0 & item.0) != 0
}

fn fmt_perm(perm: u8) -> String {
    let mut out = String::new();
    if perm & PERM_READ != 0 {
        out.push('R');
    }
    if perm & PERM_WRITE != 0{
        out.push('W');
    }
    if perm &PERM_EXEC != 0 {
        out.push('X');
    }
    out
}

/// Loads an elf format file into memory.  Returns the entry point.
fn load_elf<P: AsRef<Path>>(mem: &mut Memory, path: P) -> Result<Addr> {
    let file = elf::File::open_path(&path).map_err(|_e| anyhow!("couldn't read elf file"))?;

    for section in &file.sections {
        // FIXME: must be a better way of ignoring info sections
        if section.data.len() == 0 || section.shdr.addr == 0 {
            continue;
        }

        let flags = section.shdr.flags;
        let mut perm = 0;

        if has_flag(flags, SHF_WRITE) {
            perm |= PERM_WRITE;
        }

        if has_flag(flags, SHF_ALLOC) {
            perm |= PERM_READ;
        }

        if has_flag(flags, SHF_EXECINSTR) {
            perm |= PERM_EXEC;
        }

        println!("Loading {} at {:#x}, {}", section.shdr.name, section.shdr.addr, fmt_perm(perm));

        mem.write(Addr(section.shdr.addr as u64), &section.data, 0u8)
            .map_err(|_e| anyhow!("couldn't load binary to memory"))?;

        mem.set_perms(
            Addr(section.shdr.addr as u64),
            section.data.len() as u64,
            perm,
        )
        .map_err(|_e| anyhow!("couldn't set memory permissions"))?;
    }

    Ok(Addr(file.ehdr.entry as u64))
}

//--------------------------

fn main() -> Result<()> {
    let parser = App::new("risc-emulator")
        .version("0")
        .about("simple emulator, still under development")
        .arg(
            Arg::with_name("INPUT")
                .help("RISCV32i binary to run")
                .required(true)
                .index(1),
        );

    let matches = parser.get_matches();
    let bin = Path::new(matches.value_of("INPUT").unwrap());

    let mut vm = VM::new(1 * 1024 * 1024);
    let entry = load_elf(&mut vm.mem, PathBuf::from(bin))?;
    
    println!("Entry point: {:#x}", entry);
    vm.set_pc(entry);

    // Setup the stack containing our environment
    vm.setup_stack(64 * 1024)?;
    vm.push(0u64)?; // auxp
    vm.push(0u64)?; // envp

    // FIXME: need to add progname
    vm.push(0u64)?; // argv end
    vm.push(0u64)?; // argc

    loop {
        match vm.step() {
            Ok(_) => { /* carry on */ }
            Err(e) => {
                eprintln!("{}", vm);
                Err(e)?;
            }
        }
    }

    // Ok(())
}
