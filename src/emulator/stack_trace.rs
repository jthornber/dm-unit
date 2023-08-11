use addr2line::Context;
use anyhow::{anyhow, Result};
use std::collections::BTreeMap;
use std::sync::Arc;

use crate::emulator::memory::{Addr, Memory, PERM_READ};

//-------------------------------------------------------------------

/// Debug sections each get their own memory object.  We don't want them in the vm
/// address space, but we do want to relocate them.
pub type DbgMems = BTreeMap<String, (usize, Memory)>;

type DebugContext = Context<gimli::EndianArcSlice<gimli::RunTimeEndian>>;

pub struct DebugInfo {
    context: DebugContext,
}

/// Callback used by gimli to read debug sections
fn read_dbg_section<Endian: gimli::Endianity>(
    mems: &DbgMems,
    endian: Endian,
    id: gimli::SectionId,
) -> Result<gimli::EndianArcSlice<Endian>> {
    let name = id.name();

    if let Some((len, mem)) = mems.get(name) {
        let mut data = vec![0; *len];
        mem.read(Addr(0), &mut data[..], PERM_READ)
            .map_err(|_e| anyhow!("couldn't read section"))?;
        Ok(gimli::EndianArcSlice::new(Arc::from(&data[..]), endian))
    } else {
        Ok(gimli::EndianArcSlice::new(Arc::from(&[][..]), endian))
    }
}

impl DebugInfo {
    pub fn new(mems: DbgMems) -> Result<Self> {
        let endian = gimli::RunTimeEndian::Little;
        let load_dbg_section =
            |id: gimli::SectionId| -> Result<_, _> { read_dbg_section(&mems, endian, id) };
        let dwarf = gimli::Dwarf::load(load_dbg_section)?;
        Ok(Self {
            context: Context::from_dwarf(dwarf)?,
        })
    }

    pub fn addr2line(&self, addr: Addr) -> Result<String> {
        if let Some(loc) = self.context.find_location(addr.0)? {
            Ok(format!(
                "{}:{}",
                loc.file.or(Some("-")).unwrap(),
                loc.line.or(Some(0)).unwrap(),
            ))
        } else {
            Ok("no location info".to_string())
        }
    }
}
