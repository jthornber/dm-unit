use addr2line::{Context, Frame, LookupResult};
use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use gimli::Reader;
use std::collections::BTreeMap;
use std::io::{self, Read, Write};
use std::path::Path;
use std::sync::Arc;

use crate::emulator::memory::{Addr, Memory, PERM_READ};
use crate::guest::*;

//-------------------------------------------------------------------

/// Debug sections each get their own memory object.  We don't want them in the vm
/// address space, but we do want to relocate them.
pub type DbgMems = BTreeMap<String, (usize, Memory)>;

type DebugContext = Context<gimli::EndianArcSlice<gimli::RunTimeEndian>>;

pub struct DebugInfo {
    context: DebugContext,
}

// The kernel modules are compile with frame pointers, which means a linked list
// of these structures will be present on the stack, making it easy to walk the stack
// to get a call trace.
pub struct StackFrame {
    pub fp: u64,
    pub ra: u64,
}

impl Guest for StackFrame {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W, _loc: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.fp)?;
        w.write_u64::<LittleEndian>(self.ra)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let fp = r.read_u64::<LittleEndian>()?;
        let ra = r.read_u64::<LittleEndian>()?;
        Ok(Self { fp, ra })
    }
}

/// Remove the kernel directory prefix from a path
fn strip_prefix(kernel_dir: &Path, path: &str) -> String {
    if let Ok(path) = Path::new(path).strip_prefix(kernel_dir) {
        if let Some(path) = path.to_str() {
            return path.to_string();
        }
    }

    path.to_string()
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

/// A Guest _source_ location.
pub struct Location {
    pub file: Option<String>,
    pub line: Option<u32>,
    pub func: Option<String>,
}

impl Location {
    pub fn to_string(&self) -> String {
        let unknown = "???".to_string();
        let file = self.file.as_ref().unwrap_or(&unknown);
        let line = self.line.unwrap_or(0);
        let func = self.func.as_ref().unwrap_or(&unknown);

        format!("    {}:{}:\t{}()", file, line, func)
    }
}

fn frame_to_loc<R>(frame: &Frame<R>, kernel_dir: &Path) -> Location
where
    R: Reader<Offset = usize>,
{
    let file = frame
        .location
        .as_ref()
        .and_then(|loc| loc.file.map(|f| f.to_string()))
        .map(|f| strip_prefix(kernel_dir, &f.to_string()));
    let line = frame.location.as_ref().and_then(|loc| loc.line);

    let func = match &frame.function {
        Some(function) => Some(
            function
                .demangle()
                .unwrap_or_else(|_| function.raw_name().unwrap())
                .to_string(),
        ),
        None => None,
    };

    Location { file, line, func }
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

    /*
    pub fn addr2line<P: AsRef<Path>>(&self, kernel_dir: P, addr: Addr) -> Result<String> {
        if let Some(loc) = self.context.find_location(addr.0)? {
            Ok(format!(
                "{}:{}",
                strip_prefix(kernel_dir.as_ref(), &loc.file.unwrap_or("-")),
                loc.line.unwrap_or(0),
            ))
        } else {
            Ok("<no location info>".to_string())
        }
    }
    */

    /// Normally this will return just one location, but if we're within an
    /// inlined function it may return multiple locations.
    ///
    /// 'is_bottom' indicates if the address passed is the bottom of the stack.  Higher
    /// levels of the stack have 4 subtraced from their address to allow for the
    /// the increment that the jump instructions automatically add.
    ///
    /// Locations are appended to the 'result' vector to make it easy to build a
    /// stack trace.
    pub fn addr2frames<P: AsRef<Path>>(
        &self,
        kernel_dir: P,
        addr: Addr,
        is_bottom: bool,
        result: &mut Vec<Location>,
    ) -> Result<()> {
        let pc = if is_bottom { addr.0 } else { addr.0 - 4 };
        let lookup_result = self.context.find_frames(pc);

        let mut frames = loop {
            match lookup_result {
                LookupResult::Output(result) => break result,
                LookupResult::Load { .. } => {
                    // I don't think we need to support split loading.
                    todo!();
                }
            }
        }?;

        while let Some(frame) = frames.next()? {
            result.push(frame_to_loc(&frame, kernel_dir.as_ref()));
        }

        Ok(())
    }
}
