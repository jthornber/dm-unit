use addr2line::Context;
use anyhow::{anyhow, Result};
use std::collections::BTreeMap;
use std::path::Path;
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

/// Remove the kernel directory prefix from a path
fn strip_prefix(kernel_dir: &Path, path: Option<&str>) -> String {
    if let Some(path) = path {
        if let Ok(path) = Path::new(path).strip_prefix(kernel_dir) {
            if let Some(path) = path.to_str() {
                return path.to_string();
            }
        }
    }
    path.unwrap_or("-").to_string()
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

    pub fn addr2line<P: AsRef<Path>>(&self, kernel_dir: P, addr: Addr) -> Result<String> {
        if let Some(loc) = self.context.find_location(addr.0)? {
            Ok(format!(
                "{}:{}",
                strip_prefix(kernel_dir.as_ref(), loc.file.or(Some("-"))),
                loc.line.unwrap_or(0),
            ))
        } else {
            Ok("<no location info>".to_string())
        }
    }
}
