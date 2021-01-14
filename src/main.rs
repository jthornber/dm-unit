extern crate riscv_emulator;

use anyhow::{anyhow, Result};
use clap::{App, Arg};
use elf;
use elf::types::*;
use riscv_emulator::memory::{Addr, Memory, PERM_EXEC, PERM_READ, PERM_WRITE};
use riscv_emulator::vm::*;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//--------------------------

fn has_flag(flags: SectionFlag, item: SectionFlag) -> bool {
    (flags.0 & item.0) != 0
}

fn fmt_perm(perm: u8) -> String {
    let mut out = String::new();
    if perm & PERM_READ != 0 {
        out.push('R');
    }
    if perm & PERM_WRITE != 0 {
        out.push('W');
    }
    if perm & PERM_EXEC != 0 {
        out.push('X');
    }
    out
}

fn next_word(ptr: u64) -> u64 {
    ((ptr + 3) / 4) * 4
}

// Layout of module in memory:
//    [text] [ro-data] [w-data]
//
// Each of these segments is page aligned (vm doesn't need this since
// we have per byte permissions).  'bases' is a map from section name to
// base address.  This get's filled in as individual sections are mapped.

fn load_sections(
    base: Addr,
    mem: &mut Memory,
    ss: Vec<&elf::Section>,
    perms: u8,
    bases: &mut BTreeMap<String, Addr>,
) -> Result<()> {
    let mut len = 0;
    for s in ss {
        eprintln!("loading section {} at {:x}", s.shdr.name, base.0 + len);

        let begin = Addr(base.0 + len);
        if s.data.len() == 0 {
            let end = Addr(base.0 + len + s.shdr.size);
            mem.mmap_zeroes(begin, end, perms)
                .map_err(|_e| anyhow!("couldnt' mmap zero section"))?;
        } else {
            mem.mmap_bytes(begin, &s.data, perms)
                .map_err(|_e| anyhow!("couldn't mmap section"))?;
        }
        bases.insert(s.shdr.name.clone(), begin);

        len = next_word(len + s.shdr.size);
    }

    Ok(())
}

/// Loads an elf format file into memory.  Returns a symbol table.
fn load_elf<P: AsRef<Path>>(mem: &mut Memory, path: P) -> Result<BTreeMap<String, Symbol>> {
    let file = elf::File::open_path(&path).map_err(|_e| anyhow!("couldn't read elf file"))?;

    let mut syms = None;
    for s in &file.sections {
        if s.shdr.name == ".symtab" {
            syms = Some(match file.get_symbols(s) {
                Ok(ss) => ss,
                Err(_) => Vec::new(),
            });
        }
    }

    let mut syms_by_section = BTreeMap::new();
    for s in syms.unwrap() {
        if !syms_by_section.contains_key(&s.shndx) {
            syms_by_section.insert(s.shndx, Vec::new());
        }
        let v = syms_by_section.get_mut(&s.shndx).unwrap();
        v.push(s);
    }

    let mut text_sections = Vec::new();
    let mut ro_sections = Vec::new();
    let mut rw_sections = Vec::new();

    // Symbols refer to sections by index, so we need a way
    // of mapping to section name.
    let mut indexes = BTreeMap::new();

    for (index, section) in file.sections.iter().enumerate() {
        indexes.insert(index as u16, section.shdr.name.clone());
        let flags = section.shdr.flags;

        // We're only interested in sections that need to be loaded.
        if !has_flag(flags, SHF_ALLOC) {
            continue;
        }

        // I hope thread local storage isn't needed.
        assert!(!has_flag(flags, SHF_TLS));

        if has_flag(flags, SHF_EXECINSTR) {
            text_sections.push(section);
        } else if has_flag(flags, SHF_WRITE) {
            rw_sections.push(section);
        } else {
            ro_sections.push(section);
        }
    }

    let mut bases = BTreeMap::new();

    // One meg per segment should be ample
    let meg = 1024 * 1024;
    let text_base = Addr(meg);
    eprintln!("loading text sections");

    load_sections(text_base, mem, text_sections, PERM_EXEC, &mut bases)?;

    let ro_base = Addr(2 * meg);
    eprintln!("loading ro sections");
    load_sections(ro_base, mem, ro_sections, PERM_READ, &mut bases)?;

    let rw_base = Addr(3 * meg);
    eprintln!("loading rw sections");
    load_sections(
        rw_base,
        mem,
        rw_sections,
        PERM_READ | PERM_WRITE,
        &mut bases,
    )?;

    // Now we pull all the symbol info together to create a map from
    // symbol -> elf::Symbol, where the addr reflects where we've actually
    // loaded the sections.
    let mut symbols = BTreeMap::new();
    for (index, syms) in &syms_by_section {
        for sym in syms {
            let mut sym = sym.clone();

            // adjust the offset for defined symbols
            if sym.shndx != 0 {
                if let Some(section_name) = indexes.get(&sym.shndx) {
                    if let Some(base) = bases.get(section_name) {
                        sym.value += base.0;
                    }
                }
            }
            symbols.insert(sym.name.clone(), sym);
        }
    }

    Ok(symbols)
}

//--------------------------

fn main() -> Result<()> {
    let parser = App::new("risc-emulator")
        .version("0")
        .about("simple emulator, still under development")
        .arg(
            Arg::with_name("INPUT")
                .help("RISCV64imac binary to run")
                .required(true)
                .index(1),
        );

    let matches = parser.get_matches();
    let bin = Path::new(matches.value_of("INPUT").unwrap());

    let mut vm = VM::new();
    let symbols = load_elf(&mut vm.mem, PathBuf::from(bin))?;

    let entry = Addr(symbols.get("node_shift").unwrap().value);
    println!("Entry point: {:#x}", entry);

    vm.set_pc(entry);

    // Setup the stack and heap
    vm.setup_stack(8 * 1024)?;
    let mut heap = vm.setup_heap(64 * 1024)?;

    // We need a progname.
    let progname = heap.alloc(6)?;
    eprintln!("allocated progname at {:?}", progname);
    let buf = b"a.out";
    vm.mem.write(progname, buf, PERM_WRITE)?;

    vm.push(0u64)?; // auxp
    vm.push(0u64)?; // envp

    vm.push(0u64)?; // argv end
    vm.push(progname.0)?;
    vm.push(1u64)?; // argc

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
