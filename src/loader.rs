use anyhow::{anyhow, Result};
use elf::types::*;
use log::*;
use nom::{number::complete::*, IResult};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::Path;
use std::rc::Rc;
use tempfile::NamedTempFile;

use crate::memory::{Addr, Memory, PERM_EXEC, PERM_READ, PERM_WRITE};

//--------------------------

fn has_flag(flags: SectionFlag, item: SectionFlag) -> bool {
    (flags.0 & item.0) != 0
}

fn next_word(ptr: u64) -> u64 {
    ((ptr + 3) / 4) * 4
}

#[allow(non_camel_case_types, dead_code)]
#[derive(Clone, Copy, Debug, PartialOrd, Ord, PartialEq, Eq)]
#[repr(usize)]
enum RelocationType {
    Rnone = 0,
    R32 = 1,
    R64 = 2,
    Rrelative = 3,
    Rcopy = 4,
    Rjump_slot = 5,
    Rtls_dtpmod32 = 6,
    Rtls_dtpmod64 = 7,
    Rtls_dtprel32 = 8,
    Rtls_dtprel64 = 9,
    Rtls_tprel32 = 10,
    Rtls_tprel64 = 11,
    Rbranch = 16,
    Rjal = 17,
    Rcall = 18,
    Rcall_plt = 19,
    Rgot_hi20 = 20,
    Rtls_got_hi20 = 21,
    Rtls_gd_hi20 = 22,
    Rpcrel_hi20 = 23,
    Rpcrel_lo12_i = 24,
    Rpcrel_lo12_s = 25,
    Rhi20 = 26,
    Rlo12_i = 27,
    Rlo12_s = 28,
    Rtprel_hi20 = 29,
    Rtprel_lo12_i = 30,
    Rtprel_lo12_s = 31,
    Rtprel_add = 32,
    Radd8 = 33,
    Radd16 = 34,
    Radd32 = 35,
    Radd64 = 36,
    Rsub8 = 37,
    Rsub16 = 38,
    Rsub32 = 39,
    Rsub64 = 40,
    Rgnu_vtinherit = 41,
    Rgnu_vtentry = 42,
    Ralign = 43,
    Rrvc_branch = 44,
    Rrvc_jump = 45,
    Rlui = 46,
    Rgprel_i = 47,
    Rgprel_s = 48,
    Rtprel_i = 49,
    Rtprel_s = 50,
    Rrelax = 51,
    Rsub6 = 52,
    Rset6 = 53,
    Rset8 = 54,
    Rset16 = 55,
    Rset32 = 56,
    R32_pcrel = 57,
}

impl From<u32> for RelocationType {
    fn from(v: u32) -> Self {
        assert!(v < 58);
        unsafe { core::ptr::read_unaligned(&(v as usize) as *const usize as *const RelocationType) }
    }
}

#[derive(Clone)]
struct Relocation {
    offset: u64,
    section: Rc<RefCell<elf::Section>>,
    sym: Rc<RefCell<Sym>>,
    rtype: RelocationType,
    addend: u64,
}

fn parse_relocation<'a>(
    i: &'a [u8],
    syms: &[Rc<RefCell<Sym>>],
    section: Rc<RefCell<elf::Section>>,
) -> IResult<&'a [u8], Relocation> {
    let (i, offset) = le_u64(i)?;
    let (i, info) = le_u64(i)?;
    let (i, addend) = le_u64(i)?;

    let sym = syms[(info >> 32) as usize].clone();
    let rtype = RelocationType::from((info & 0xffffffff) as u32);

    Ok((
        i,
        Relocation {
            offset,
            section,
            sym,
            rtype,
            addend,
        },
    ))
}

fn parse_relocations(
    mut data: &[u8],
    syms: &[Rc<RefCell<Sym>>],
    section: Rc<RefCell<elf::Section>>,
) -> Result<Vec<Relocation>> {
    let mut rels = Vec::new();

    let count = data.len() / 24;
    for _ in 0..count {
        let (next, rel) = parse_relocation(data, syms, section.clone())
            .map_err(|_| anyhow!("couldn't parse relocation"))?;
        data = next;
        rels.push(rel);
    }

    Ok(rels)
}

// FIXME: I wonder if this should return u32?
fn addr_offset(lhs: Addr, rhs: Addr) -> i32 {
    if lhs.0 > rhs.0 {
        let delta = lhs.0 - rhs.0;
        assert!(delta <= i32::MAX as u64);
        delta as i32
    } else {
        let delta = rhs.0 - lhs.0;
        assert!(delta <= i32::MAX as u64);
        -(delta as i32)
    }
}

/// Some relocations need to be performed as a pair.  ie. the location of the hi
/// relocation is used in the calculation for the low bits.
#[derive(Clone)]
enum CompoundRel {
    Simple(Relocation),
    Pair(Relocation, Relocation),
}

fn build_compound_rels(rlocs: Vec<Relocation>) -> Vec<CompoundRel> {
    use RelocationType::*;

    let mut i = 0;
    let mut compound = Vec::new();
    while i < rlocs.len() {
        let rloc = &rlocs[i];
        if rloc.rtype == Rpcrel_hi20 {
            // the next entry is probably the corresponding lo12
            i += 1;
            if i < rlocs.len() {
                let rloc2 = &rlocs[i];
                if rloc2.rtype == Rpcrel_lo12_i {
                    compound.push(CompoundRel::Pair(rloc.clone(), rloc2.clone()));
                    i += 1;
                } else {
                    compound.push(CompoundRel::Simple(rloc.clone()));
                }
            } else {
                compound.push(CompoundRel::Simple(rloc.clone()));
            }
        } else {
            compound.push(CompoundRel::Simple(rloc.clone()));
            i += 1;
        }
    }

    compound
}

fn mutate_u16<F: FnOnce(u16) -> u16>(mem: &mut Memory, loc: Addr, f: F) -> Result<()> {
    let old = mem.read_into::<u16>(loc, 0)?;
    let new = f(old);
    let bytes = new.to_le_bytes();
    mem.write(loc, &bytes, 0)
        .map_err(|e| anyhow!("bad access at {}", e))
}

fn mutate_u32<F: FnOnce(u32) -> u32>(mem: &mut Memory, loc: Addr, f: F) -> Result<()> {
    let old = mem.read_into::<u32>(loc, 0)?;
    let new = f(old);
    let bytes = new.to_le_bytes();
    mem.write(loc, &bytes, 0)
        .map_err(|e| anyhow!("bad access at {}", e))
}

fn mutate_u64<F: FnOnce(u64) -> u64>(mem: &mut Memory, loc: Addr, f: F) -> Result<()> {
    let old = mem.read_into::<u64>(loc, 0)?;
    let new = f(old);
    let bytes = new.to_le_bytes();
    mem.write(loc, &bytes, 0)
        .map_err(|e| anyhow!("bad access at {}", e))
}

fn relocate(
    mem: &mut Memory,
    rtype: RelocationType,
    location: Addr,
    sym: Addr,
    _addend: u64,
) -> Result<()> {
    use RelocationType::*;

    match rtype {
        R32 => {
            assert!(sym.0 as u32 as u64 == sym.0);
            mutate_u32(mem, location, |_old| sym.0 as u32)?;
        }
        R64 => {
            mutate_u64(mem, location, |_old| sym.0)?;
        }
        Rbranch => {
            let offset = addr_offset(sym, location) as u32;

            let imm12 = (offset & 0x1000) << (31 - 12);
            let imm11 = (offset & 0x800) >> (11 - 7);
            let imm10_5 = (offset & 0x7e0) << (30 - 10);
            let imm4_1 = (offset & 0x1e) << (11 - 4);
            mutate_u32(mem, location, |old| {
                (old & 0x1fff07f) | imm12 | imm11 | imm10_5 | imm4_1
            })?;
        }
        Rjal => {
            let offset = addr_offset(sym, location) as u32;
            let imm20 = (offset & 0x100000) << (31 - 20);
            let imm19_12 = offset & 0xff000;
            let imm11 = (offset & 0x800) << (20 - 11);
            let imm10_1 = (offset & 0x7fe) << (30 - 10);
            mutate_u32(mem, location, |old| {
                (old & 0xfff) | imm20 | imm19_12 | imm11 | imm10_1
            })?;
        }
        Rcall => {
            let offset = addr_offset(sym, location);

            let hi20: u32 = (offset as u32).wrapping_add(0x800) & 0xfffff000;
            let lo12: u32 = (offset as u32).wrapping_sub(hi20) & 0xfff;
            mutate_u32(mem, location, |old| (old & 0xfff) | hi20)?;
            let location = Addr(location.0 + 4);
            mutate_u32(mem, location, |old| (old & 0xfffff) | (lo12 << 20))?;
        }
        Rpcrel_hi20 => {
            let offset = addr_offset(sym, location);
            let hi20 = (offset as u32).wrapping_add(0x800) & 0xfffff000;
            mutate_u32(mem, location, |old| (old & 0xfff) | hi20)?;
        }
        Rpcrel_lo12_i => {
            mutate_u32(mem, location, |old| {
                (old & 0xfffff) | (((sym.0 as u32) & 0xfff) << 20)
            })?;
        }
        Radd32 => {
            mutate_u32(mem, location, |old| old + sym.0 as u32)?;
        }
        Rsub32 => {
            mutate_u32(mem, location, |old| old.wrapping_sub(sym.0 as u32))?;
        }
        Rrvc_branch => {
            let offset = addr_offset(sym, location) as u16;

            let imm8 = (offset & 0x100) << (12 - 8);
            let imm7_6 = (offset & 0xc0) >> (6 - 5);
            let imm5 = (offset & 0x20) >> (5 - 2);
            let imm4_3 = (offset & 0x18) << (12 - 5);
            let imm2_1 = (offset & 0x6) << (12 - 10);
            mutate_u16(mem, location, |old| {
                (old & 0xe383) | imm8 | imm7_6 | imm5 | imm4_3 | imm2_1
            })?;
        }
        Rrvc_jump => {
            let offset = addr_offset(sym, location) as u16;

            let imm11 = (offset & 0x800) << (12 - 11);
            let imm10 = (offset & 0x400) >> (10 - 8);
            let imm9_8 = (offset & 0x300) << (12 - 11);
            let imm7 = (offset & 0x80) >> (7 - 6);
            let imm6 = (offset & 0x40) << (12 - 11);
            let imm5 = (offset & 0x20) >> (5 - 2);
            let imm4 = (offset & 0x10) << (12 - 5);
            let imm3_1 = (offset & 0xe) << (12 - 10);

            mutate_u16(mem, location, |old| {
                (old & 0xe003) | imm11 | imm10 | imm9_8 | imm7 | imm6 | imm5 | imm4 | imm3_1
            })?;
        }
        _ => {
            return Err(anyhow!("unsupported relocation type: {:?}", rtype));
        }
    }

    Ok(())
}

fn exec_relocation(mem: &mut Memory, crel: &CompoundRel) -> Result<()> {
    match crel {
        CompoundRel::Simple(rloc) => {
            // This is the location of the instruction that needs adjusting.
            let base = rloc.section.borrow().shdr.addr;
            let location = Addr(base + rloc.offset);
            let sym = rloc.sym.borrow();
            let mut sym_addr = sym.section.as_ref().unwrap().borrow().shdr.addr;
            sym_addr += sym.value;

            relocate(
                mem,
                rloc.rtype,
                location,
                Addr(sym_addr + rloc.addend),
                rloc.addend,
            )?;
        }
        CompoundRel::Pair(hi_rloc, lo_rloc) => {
            let base = hi_rloc.section.borrow().shdr.addr;

            // These is the location of the instruction that needs adjusting.
            let hi_location = Addr(base + hi_rloc.offset);
            let lo_location = Addr(base + lo_rloc.offset);

            // Both hi/lo refer to the same sym.
            let sym = hi_rloc.sym.borrow();
            let mut sym_addr = sym.section.as_ref().unwrap().borrow().shdr.addr;
            sym_addr += sym.value;

            // Do the hi20 relocation
            relocate(
                mem,
                hi_rloc.rtype,
                hi_location,
                Addr(sym_addr + hi_rloc.addend),
                hi_rloc.addend,
            )?;

            // Do the lo12 relocation
            let offset = addr_offset(Addr(sym_addr + hi_rloc.addend), hi_location);
            let hi20 = ((offset + 0x800) as u32 as u64) & 0xfffff000;
            let lo12 = (offset as u32 as u64).wrapping_sub(hi20);
            relocate(mem, lo_rloc.rtype, lo_location, Addr(lo12), lo_rloc.addend)?;
        }
    }

    Ok(())
}

//--------------------------

#[derive(Clone)]
struct Sym {
    name: String,
    value: u64,
    size: u64,
    section: Option<Rc<RefCell<elf::Section>>>,
    symtype: SymbolType,
    bind: SymbolBind,
}

type Sections = Vec<Rc<RefCell<elf::Section>>>;
type Syms = Vec<Rc<RefCell<Sym>>>;

struct Module {
    refs: Syms,
    defs: Syms,
    internal: Syms,

    text_sections: Sections,
    rw_sections: Sections,
    ro_sections: Sections,
    relocations: Vec<CompoundRel>,
}

fn read_syms(file: &elf::File) -> Result<Vec<Symbol>> {
    for s in &file.sections {
        if s.shdr.name == ".symtab" {
            return file
                .get_symbols(s)
                .map_err(|_| anyhow!("couldn't parse .symtab section"));
        }
    }

    Err(anyhow!("couldn't find .symtab section"))
}

fn xlate_syms(syms: Vec<Symbol>, sections: &[Rc<RefCell<elf::Section>>]) -> Vec<Rc<RefCell<Sym>>> {
    let mut result = Vec::new();
    for sym in syms {
        result.push(Rc::new(RefCell::new(Sym {
            name: sym.name.clone(),
            value: sym.value,
            size: sym.size,
            section: if sym.shndx == 0 || sym.shndx as usize >= sections.len() {
                None
            } else {
                Some(sections[sym.shndx as usize].clone())
            },
            symtype: sym.symtype,
            bind: sym.bind,
        })));
    }
    result
}

/// Returns (refs, defs, internal)
fn filter_syms(syms: &[Rc<RefCell<Sym>>]) -> (Syms, Syms, Syms) {
    let mut defs = Vec::new();
    let mut refs = Vec::new();
    let mut internal = Vec::new();

    for s in syms {
        let s_ = s.borrow();
        if s_.section.is_none() {
            refs.push(s.clone());
        } else if s_.bind == STB_GLOBAL {
            defs.push(s.clone());
        } else {
            internal.push(s.clone());
        }
    }

    (refs, defs, internal)
}

// Returns (text, rw, ro, rel)
fn filter_sections(sections: &Sections) -> (Sections, Sections, Sections, Sections) {
    let mut text_sections = Vec::new();
    let mut rw_sections = Vec::new();
    let mut ro_sections = Vec::new();
    let mut rel_sections = Vec::new();

    for section in sections {
        let s = section.borrow();
        let flags = s.shdr.flags;

        // Not supported/needed
        assert!(s.shdr.shtype != SHT_REL);

        if s.shdr.shtype == SHT_RELA {
            rel_sections.push(section.clone());
            continue;
        }

        // We're only interested in sections that need to be loaded.
        if !has_flag(flags, SHF_ALLOC) {
            continue;
        }

        // I hope thread local storage isn't needed.
        assert!(!has_flag(flags, SHF_TLS));

        if has_flag(flags, SHF_EXECINSTR) {
            text_sections.push(section.clone());
        } else if has_flag(flags, SHF_WRITE) {
            rw_sections.push(section.clone());
        } else {
            ro_sections.push(section.clone());
        }
    }

    (text_sections, rw_sections, ro_sections, rel_sections)
}

fn read_module<P: AsRef<Path>>(path: P) -> Result<Module> {
    let mut file = elf::File::open_path(&path).map_err(|_e| anyhow!("couldn't read elf file"))?;
    let syms = read_syms(&file)?;

    let mut old_sections = Vec::new();
    std::mem::swap(&mut old_sections, &mut file.sections);
    let mut sections: Vec<Rc<RefCell<elf::Section>>> = Vec::new();
    for s in old_sections {
        sections.push(Rc::new(RefCell::new(s)));
    }

    let syms = xlate_syms(syms, &sections);
    let (refs, defs, internal) = filter_syms(&syms[0..]);
    let (text_sections, rw_sections, ro_sections, rel_sections) = filter_sections(&sections);

    // FIXME: factor out
    let mut relocations = Vec::new();
    for rsection in rel_sections {
        let rsection = rsection.borrow();

        let index = rsection.shdr.info as usize;
        let associated_section = sections[index].clone();

        // Hack to avoid relocating debug sections.  Really we should
        // check to see if the associated section is going to be loaded.
        if !has_flag(associated_section.borrow().shdr.flags, SHF_ALLOC) {
            debug!(
                "ignoring relocations for section {}",
                associated_section.borrow().shdr.name
            );
            continue;
        }

        relocations.append(&mut parse_relocations(
            &rsection.data,
            &syms[0..],
            associated_section,
        )?);
    }
    let relocations = build_compound_rels(relocations);

    Ok(Module {
        refs,
        defs,
        internal,

        text_sections,
        rw_sections,
        ro_sections,

        relocations,
    })
}

fn check_sym(sym: &Rc<RefCell<Sym>>) {
    let sym = sym.borrow();
    if sym.section.is_none() {
        warn!("'{}' has no section", sym.name);
        panic!();
    }
}

fn check_relocation(crel: &CompoundRel) {
    use CompoundRel::*;

    match crel {
        Simple(rel) => {
            check_sym(&rel.sym);
        }
        Pair(rel1, rel2) => {
            check_sym(&rel1.sym);
            check_sym(&rel2.sym);
        }
    }
}

/// Fills out the section.addr with the location
fn load_sections(mem: &mut Memory, base: Addr, ss: &mut Sections, perms: u8) -> Result<Addr> {
    let mut len = 0;
    for s in ss {
        let mut s = s.borrow_mut();

        let begin = Addr(base.0 + len);
        debug!("    {} at {:?}", s.shdr.name, begin);
        s.shdr.addr = begin.0;

        // We round up all the sections to be dword aligned so naughty functions like
        // memcpy which read dwords don't get perms errors.
        if s.data.is_empty() {
            let end = Addr(base.0 + next_word(len + s.shdr.size));
            mem.mmap_zeroes(begin, end, perms)
                .map_err(|_e| anyhow!("couldn't mmap zero section"))?;
        } else {
            mem.mmap_bytes(begin, s.data.clone(), perms)
                .map_err(|_e| anyhow!("couldn't mmap section"))?;

            let new_len = len + s.shdr.size;
            let new_rounded = next_word(len + s.shdr.size);
            if new_len != new_rounded {
                // We need to map an extra few bytes
                mem.mmap_zeroes(Addr(base.0 + new_len), Addr(base.0 + new_rounded), perms)
                    .map_err(|_e| anyhow!("couldn't mmap zero tail section"))?;
            }
        }

        len = next_word(len + s.shdr.size);
    }

    Ok(Addr(base.0 + len))
}

pub struct LoaderInfo {
    symbols: BTreeMap<String, Addr>,
    sym_rmap: BTreeMap<Addr, String>,
}

impl LoaderInfo {
    fn new(symbols: BTreeMap<String, Addr>) -> Self {
        let mut sym_rmap = BTreeMap::new();
        for (k, v) in &symbols {
            sym_rmap.insert(*v, k.clone());
        }

        LoaderInfo { symbols, sym_rmap }
    }

    pub fn get_sym(&self, name: &str) -> Option<Addr> {
        self.symbols.get(name).map(|a| a.clone())
    }

    pub fn get_rmap(&self, loc: Addr) -> Option<String> {
        self.sym_rmap.get(&loc).map(|s| s.clone())
    }
}

fn load_module(mem: &mut Memory, mut module: Module) -> Result<LoaderInfo> {
    // Layout of module in memory:
    //    [text] [ro-data] [w-data]
    //
    // Each of these segments is page aligned (vm doesn't need this since
    // we have per byte permissions).  'bases' is a map from section name to
    // base address.  This get's filled in as individual sections are mapped.
    let space = 1024 * 1024;
    let text_base = Addr(space);
    debug!("loading text sections starting at {:?}", text_base);
    load_sections(mem, text_base, &mut module.text_sections, PERM_EXEC)?;

    let ro_base = Addr(2 * space);
    debug!("loading ro sections starting at {:?}", ro_base);
    load_sections(mem, ro_base, &mut module.ro_sections, PERM_READ)?;

    let rw_base = Addr(3 * space);
    debug!("loading rw sections starting at {:?}", rw_base);
    load_sections(
        mem,
        rw_base,
        &mut module.rw_sections,
        PERM_READ | PERM_WRITE,
    )?;

    // FIXME: factor out
    {
        // Create a section for undefined references.  These will be hooked by
        // test code.
        let undefined_base = Addr(4 * space);
        let undefined_end = Addr(undefined_base.0 + module.refs.len() as u64 * 4);
        mem.mmap_zeroes(
            undefined_base,
            undefined_end,
            PERM_EXEC | PERM_READ | PERM_WRITE, // FIXME: would PERM_EXEC be enough?
        )?;

        let ebreak_instr: u16 = 0b1001000000000010;
        for i in 0..module.refs.len() {
            mem.write_out::<u16>(ebreak_instr, Addr(undefined_base.0 + (i as u64 * 4)), 0)?;
        }

        let undefined_section = Rc::new(RefCell::new(elf::Section {
            shdr: SectionHeader {
                name: "dm-unit-stubs".to_string(),
                shtype: SectionType(0),
                flags: SectionFlag(0),

                // This is the only field that matters.
                addr: undefined_base.0,

                offset: 0,
                size: 0,
                link: 0,
                info: 0,
                addralign: 4,
                entsize: 4,
            },
            data: vec![0u8; 0],
        }));

        for (i, sym) in module.refs.iter().enumerate() {
            let mut sym = sym.borrow_mut();
            sym.section = Some(undefined_section.clone());
            sym.value = (i * 4) as u64;
        }
    }

    // Now that the global refs have been stubbed, every
    // symbol in the relocations should have an associated
    // section.
    for r in &module.relocations {
        check_relocation(r);
    }

    // Execute all the relocations.
    for r in &module.relocations {
        exec_relocation(mem, r)?;
    }

    // build globals symbol table
    let mut symtable = BTreeMap::new();
    for s in &module.refs {
        let s = s.borrow();
        if let Some(section) = &s.section {
            let section = section.borrow();
            symtable.insert(s.name.clone(), Addr(section.shdr.addr + s.value));
        }
    }

    for s in &module.defs {
        let s = s.borrow();
        if let Some(section) = &s.section {
            let section = section.borrow();
            symtable.insert(s.name.clone(), Addr(section.shdr.addr + s.value));
        }
    }

    for s in &module.internal {
        let s = s.borrow();
        if let Some(section) = &s.section {
            let section = section.borrow();
            symtable.insert(s.name.clone(), Addr(section.shdr.addr + s.value));
        }
    }

    Ok(LoaderInfo::new(symtable))
}

/// Links all the modules needed for a test into a single 'super' module.
fn link_modules<P: AsRef<Path>>(paths: &[P], output: &Path) -> Result<()> {
    use std::env::{var, VarError};

    let cross_compile = match var("CROSS_COMPILE") {
        Ok(s) => s,
        Err(VarError::NotPresent) => {
            debug!(
                "CROSS_COMPILE environment variable not set, defaulting to 'riscv64-linux-gnu-'"
            );
            "riscv64-linux-gnu-".to_string()
        }
        e @ Err(_) => e?,
    };

    let ld_cmd = format!("{}ld", cross_compile);
    let mut args = vec!["-r", "-melf64lriscv", "-T", "misc/module.lds", "-o", output.to_str().unwrap()];
    for p in paths {
        args.push(p.as_ref().to_str().unwrap());
    }
    duct::cmd(ld_cmd, args).run()?;
    Ok(())
}

pub fn load_modules<P: AsRef<Path>>(mem: &mut Memory, paths: &[P]) -> Result<LoaderInfo> {
    let super_module = NamedTempFile::new()?;
    link_modules(paths, super_module.path())?;
    let module = read_module(super_module.path())?;
    load_module(mem, module)
}

//--------------------------
