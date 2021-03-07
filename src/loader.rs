use anyhow::{anyhow, Result};
use elf::types::Symbol;
use elf::types::*;
use log::debug;
use nom::{number::complete::*, IResult};
use std::collections::BTreeMap;
use std::path::Path;

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

#[derive(Clone, Debug)]
struct Relocation {
    offset: u64,
    sym: u32,
    rtype: RelocationType,
    addend: u64,
}

fn parse_relocation(i: &[u8]) -> IResult<&[u8], Relocation> {
    let (i, offset) = le_u64(i)?;
    let (i, info) = le_u64(i)?;
    let (i, addend) = le_u64(i)?;

    let sym = (info >> 32) as u32;
    let rtype = RelocationType::from((info & 0xffffffff) as u32);

    Ok((
        i,
        Relocation {
            offset,
            sym,
            rtype,
            addend,
        },
    ))
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

fn read_symbols(file: &elf::File) -> Result<Vec<Symbol>> {
    for s in &file.sections {
        if s.shdr.name == ".symtab" {
            return file
                .get_symbols(s)
                .map_err(|_| anyhow!("couldn't parse .symtab section"));
        }
    }

    Err(anyhow!("couldn't find .symtab section"))
}

struct Loader<'a> {
    mem: &'a mut Memory,
}

impl<'a> Loader<'a> {
    fn new(mem: &'a mut Memory) -> Self {
        Loader { mem }
    }

    /// Loads an elf format file into memory.  Returns a symbol table.
    fn load<P: AsRef<Path>>(&mut self, path: P) -> Result<BTreeMap<String, Symbol>> {
        let file = elf::File::open_path(&path).map_err(|_e| anyhow!("couldn't read elf file"))?;

        let mut syms = read_symbols(&file)?;

        // Build a vector of symbols for each section.
        let mut syms_by_section = BTreeMap::new();
        for (index, s) in syms.iter().enumerate() {
            syms_by_section.entry(s.shndx).or_insert_with(Vec::new);
            let v = syms_by_section.get_mut(&s.shndx).unwrap();
            v.push(index);
        }

        let mut text_sections = Vec::new();
        let mut ro_sections = Vec::new();
        let mut rw_sections = Vec::new();
        let mut rela_sections = Vec::new();

        // Symbols refer to sections by index, so we need a way
        // of mapping to section name.
        let mut indexes = BTreeMap::new();

        for (index, section) in file.sections.iter().enumerate() {
            indexes.insert(index as u16, section.shdr.name.clone());
            let flags = section.shdr.flags;

            // Not supported/needed
            assert!(section.shdr.shtype != SHT_REL);

            if section.shdr.shtype == SHT_RELA {
                rela_sections.push(section);
                continue;
            }

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
        debug!("loading text sections");
        self.load_sections(text_base, text_sections, PERM_EXEC, &mut bases)?;

        let ro_base = Addr(2 * meg);
        debug!("loading ro sections");
        self.load_sections(ro_base, ro_sections, PERM_READ, &mut bases)?;

        let rw_base = Addr(3 * meg);
        debug!("loading rw sections");
        self.load_sections(rw_base, rw_sections, PERM_READ | PERM_WRITE, &mut bases)?;

        // Now we can adjust all the symbol addresses to reflect where
        // we put the sections.
        let mut globals: Vec<usize> = Vec::new();
        for (i, sym) in syms.iter_mut().enumerate() {
            // adjust the offset for defined symbols
            if sym.shndx == 0 {
                globals.push(i);
            } else if let Some(section_name) = indexes.get(&sym.shndx) {
                if let Some(base) = bases.get(section_name) {
                    // info!("adjusting {}: {} += {}, section '{}'", sym.name, sym.value, base.0, section_name);
                    sym.value += base.0;
                }
            }
        }

        // Each global becomes a single 'ret' instruction.
        let globals_base = Addr(4 * meg);
        let globals_end = Addr(globals_base.0 + globals.len() as u64 * 4);
        debug!("globals at {:?} -> {:?}", globals_base, globals_end);
        self.mem.mmap_zeroes(
            globals_base,
            globals_end,
            PERM_EXEC | PERM_READ | PERM_WRITE,
        )?;

        // c.ebreak
        let ret: u16 = 0b1001000000000010;
        let bytes = (ret as u32).to_le_bytes();

        for (i, si) in globals.iter().enumerate() {
            let sym = &mut syms[*si];
            if sym.shndx == 0 {
                let addr = Addr(globals_base.0 + (i as u64 * 4));
                debug!("mapping {} to {:?}", sym.name, addr);
                self.mem.write(addr, &bytes, 0)?;
                sym.value = addr.0;
            }
        }

        // Execute all the relocation instructions to adjust the code.
        self.exec_relocations(rela_sections, &indexes, &bases, &syms)?;

        // Now we pull all the symbol info together to create a map from
        // symbol -> elf::Symbol, where the addr reflects where we've actually
        // loaded the sections.
        let mut symbols = BTreeMap::new();
        for sym in syms {
            symbols.insert(sym.name.clone(), sym.clone());
        }
        Ok(symbols)
    }

    fn exec_relocations(
        &mut self,
        rs: Vec<&elf::Section>,
        indexes: &BTreeMap<u16, String>,
        bases: &BTreeMap<String, Addr>,
        syms: &[Symbol],
    ) -> Result<()> {
        for r in rs {
            let (_, rlocs) = nom::multi::many0(parse_relocation)(&r.data)
                .map_err(|_| anyhow!("couldn't parse relocations"))?;

            // Each relocation section has a corresponding code section that it
            // mutates.  We need the base address that this section is loaded at.
            let index = r.shdr.info as u16;
            let base = match bases.get(indexes.get(&index).unwrap()) {
                Some(base) => base,
                None => {
                    debug!("No base found for section {}", r.shdr.name);
                    return Ok(());
                }
            };

            for crel in build_compound_rels(rlocs) {
                match crel {
                    CompoundRel::Simple(rloc) => {
                        // This is the location of the instruction that needs adjusting.
                        let location = Addr(base.0 + rloc.offset);

                        // This is the address of the symbol that is referred to.
                        let sym_index = rloc.sym as usize;
                        let sym = &syms[sym_index];

                        self.relocate(
                            rloc.rtype,
                            location,
                            Addr(sym.value + rloc.addend),
                            rloc.addend,
                        )?;
                    }
                    CompoundRel::Pair(hi_rloc, lo_rloc) => {
                        // These is the location of the instruction that needs adjusting.
                        let hi_location = Addr(base.0 + hi_rloc.offset);
                        let lo_location = Addr(base.0 + lo_rloc.offset);

                        // This is the address of the symbol that both hi/lo refer to.
                        let sym_index = hi_rloc.sym as usize;
                        let sym = &syms[sym_index];

                        debug!("{} relocating to {:?}", sym.name, Addr(sym.value));

                        // Do the hi20 relocation
                        self.relocate(
                            hi_rloc.rtype,
                            hi_location,
                            Addr(sym.value + hi_rloc.addend),
                            hi_rloc.addend,
                        )?;

                        // Do the lo12 relocation
                        let offset = addr_offset(Addr(sym.value + hi_rloc.addend), hi_location);
                        let hi20 = ((offset + 0x800) as u32 as u64) & 0xfffff000;
                        let lo12 = (offset as u32 as u64).wrapping_sub(hi20);
                        self.relocate(lo_rloc.rtype, lo_location, Addr(lo12), lo_rloc.addend)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn relocate(
        &mut self,
        rtype: RelocationType,
        location: Addr,
        sym: Addr,
        _addend: u64,
    ) -> Result<()> {
        use RelocationType::*;

        match rtype {
            R64 => {
                self.mutate_u64(location, |_old| sym.0)?;
            }
            Rbranch => {
                let offset = addr_offset(sym, location) as u32;

                let imm12 = (offset & 0x1000) << (31 - 12);
                let imm11 = (offset & 0x800) >> (11 - 7);
                let imm10_5 = (offset & 0x7e0) << (30 - 10);
                let imm4_1 = (offset & 0x1e) << (11 - 4);
                self.mutate_u32(location, |old| {
                    (old & 0x1fff07f) | imm12 | imm11 | imm10_5 | imm4_1
                })?;
            }
            Rjal => {
                let offset = addr_offset(sym, location) as u32;
                let imm20 = (offset & 0x100000) << (31 - 20);
                let imm19_12 = offset & 0xff000;
                let imm11 = (offset & 0x800) << (20 - 11);
                let imm10_1 = (offset & 0x7fe) << (30 - 10);
                self.mutate_u32(location, |old| {
                    (old & 0xfff) | imm20 | imm19_12 | imm11 | imm10_1
                })?;
            }
            Rcall => {
                let offset = addr_offset(sym, location);

                let hi20: u32 = (offset as u32).wrapping_add(0x800) & 0xfffff000;
                let lo12: u32 = (offset as u32).wrapping_sub(hi20) & 0xfff;
                self.mutate_u32(location, |old| (old & 0xfff) | hi20)?;
                let location = Addr(location.0 + 4);
                self.mutate_u32(location, |old| (old & 0xfffff) | (lo12 << 20))?;
            }
            Rpcrel_hi20 => {
                let offset = addr_offset(sym, location);
                let hi20 = (offset as u32).wrapping_add(0x800) & 0xfffff000;
                self.mutate_u32(location, |old| (old & 0xfff) | hi20)?;
            }
            Rpcrel_lo12_i => {
                self.mutate_u32(location, |old| {
                    (old & 0xfffff) | (((sym.0 as u32) & 0xfff) << 20)
                })?;
            }
            Radd32 => {
                self.mutate_u32(location, |old| old + sym.0 as u32)?;
            }
            Rsub32 => {
                self.mutate_u32(location, |old| old.wrapping_sub(sym.0 as u32))?;
            }
            Rrvc_branch => {
                let offset = addr_offset(sym, location) as u16;

                let imm8 = (offset & 0x100) << (12 - 8);
                let imm7_6 = (offset & 0xc0) >> (6 - 5);
                let imm5 = (offset & 0x20) >> (5 - 2);
                let imm4_3 = (offset & 0x18) << (12 - 5);
                let imm2_1 = (offset & 0x6) << (12 - 10);
                self.mutate_u16(location, |old| {
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

                self.mutate_u16(location, |old| {
                    (old & 0xe003) | imm11 | imm10 | imm9_8 | imm7 | imm6 | imm5 | imm4 | imm3_1
                })?;
            }
            _ => {
                return Err(anyhow!("unsupported relocation type: {:?}", rtype));
            }
        }

        Ok(())
    }

    // Layout of module in memory:
    //    [text] [ro-data] [w-data]
    //
    // Each of these segments is page aligned (vm doesn't need this since
    // we have per byte permissions).  'bases' is a map from section name to
    // base address.  This get's filled in as individual sections are mapped.

    fn load_sections(
        &mut self,
        base: Addr,
        ss: Vec<&elf::Section>,
        perms: u8,
        bases: &mut BTreeMap<String, Addr>,
    ) -> Result<()> {
        let mut len = 0;
        for s in ss {
            debug!("loading section {} at {:x}", s.shdr.name, base.0 + len);

            // We round up all the sections to be dword aligned so naughty functions like
            // memcpy which read dwords don't get perms errors.
            let begin = Addr(base.0 + len);
            if s.data.is_empty() {
                let end = Addr(base.0 + next_word(len + s.shdr.size));
                self.mem
                    .mmap_zeroes(begin, end, perms)
                    .map_err(|_e| anyhow!("couldn't mmap zero section"))?;
            } else {
                self.mem
                    .mmap_bytes(begin, s.data.clone(), perms)
                    .map_err(|_e| anyhow!("couldn't mmap section"))?;

                let new_len = len + s.shdr.size;
                let new_rounded = next_word(len + s.shdr.size);
                if new_len != new_rounded {
                    // We need to map an extra few bytes
                    self.mem
                        .mmap_zeroes(Addr(base.0 + new_len), Addr(base.0 + new_rounded), perms)
                        .map_err(|_e| anyhow!("couldn't mmap zero tail section"))?;
                }
            }
            debug!(
                "{} mapped to {:?}..{:?}",
                s.shdr.name,
                begin,
                Addr(begin.0 + s.shdr.size)
            );
            bases.insert(s.shdr.name.clone(), begin);

            len = next_word(len + s.shdr.size);
        }

        Ok(())
    }

    fn mutate_u16<F: FnOnce(u16) -> u16>(&mut self, loc: Addr, f: F) -> Result<()> {
        let old = self.mem.read_into::<u16>(loc, 0)?;
        let new = f(old);
        let bytes = new.to_le_bytes();
        self.mem
            .write(loc, &bytes, 0)
            .map_err(|e| anyhow!("bad access at {}", e))
    }

    fn mutate_u32<F: FnOnce(u32) -> u32>(&mut self, loc: Addr, f: F) -> Result<()> {
        let old = self.mem.read_into::<u32>(loc, 0)?;
        let new = f(old);
        let bytes = new.to_le_bytes();
        self.mem
            .write(loc, &bytes, 0)
            .map_err(|e| anyhow!("bad access at {}", e))
    }

    fn mutate_u64<F: FnOnce(u64) -> u64>(&mut self, loc: Addr, f: F) -> Result<()> {
        let old = self.mem.read_into::<u64>(loc, 0)?;
        let new = f(old);
        let bytes = new.to_le_bytes();
        self.mem
            .write(loc, &bytes, 0)
            .map_err(|e| anyhow!("bad access at {}", e))
    }
}

//--------------------------

pub fn load_module<P: AsRef<Path>>(mem: &mut Memory, path: P) -> Result<BTreeMap<String, Symbol>> {
    let mut ldr = Loader::new(mem);
    let symbols = ldr.load(path)?;
    Ok(symbols)
}
