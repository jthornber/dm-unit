use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};

use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;

use Reg::*;

//-------------------------------

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mapping {
    pub thin_begin: u64,
    pub data_begin: u64,
    pub len: u32,
    pub time: u32,
}

impl Guest for Mapping {
    fn guest_len() -> usize {
        24
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.thin_begin)?;
        w.write_u64::<LittleEndian>(self.data_begin)?;
        w.write_u32::<LittleEndian>(self.len)?;
        w.write_u32::<LittleEndian>(self.time)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let thin_begin = r.read_u64::<LittleEndian>()?;
        let data_begin = r.read_u64::<LittleEndian>()?;
        let len = r.read_u32::<LittleEndian>()?;
        let time = r.read_u32::<LittleEndian>()?;

        Ok(Mapping {
            thin_begin,
            data_begin,
            len,
            time,
        })
    }
}

pub fn dm_rtree_empty(fix: &mut Fixture, tm: Addr) -> Result<u64> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_rtree_empty")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_rtree_del(fix: &mut Fixture, tm: Addr, data_sm: Addr, root: u64) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, data_sm.0);
    fix.vm.set_reg(A2, root);
    fix.call_with_errno("dm_rtree_del")
}

pub fn dm_rtree_lookup(
    fix: &mut Fixture,
    tm: Addr,
    root: u64,
    key: u64,
) -> Result<Option<Mapping>> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, Mapping::guest_len())?;
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, key);
    fix.vm.set_reg(A3, result_ptr.0);
    fix.call("dm_rtree_lookup")?;
    let r = fix.vm.reg(A0) as i64 as i32;
    if r == 0 {
        let value = read_guest(&fix.vm.mem, result_ptr)?;
        return Ok(Some(value));
    } else if r == -libc::ENODATA {
        return Ok(None);
    } else {
        if r < 0 {
            return Err(anyhow!("dm_rtree_lookup() failed: {}", error_string(-r)));
        } else {
            return Err(anyhow!("dm_rtree_lookup() failed: {}", r));
        }
    }
}

pub fn dm_rtree_insert(
    fix: &mut Fixture,
    tm: Addr,
    data_sm: Addr,
    root: u64,
    value: &Mapping,
) -> Result<(u64, u32)> {
    let (mut fix, mapping_ptr) = auto_guest::<Mapping>(&mut *fix, value, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root_ptr) = auto_alloc(&mut *fix, 8)?;
    let (mut fix, nr_inserts_ptr) = auto_alloc(&mut *fix, 4)?;
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, data_sm.0);
    fix.vm.set_reg(A2, root);
    fix.vm.set_reg(A3, mapping_ptr.0);
    fix.vm.set_reg(A4, new_root_ptr.0);
    fix.vm.set_reg(A5, nr_inserts_ptr.0);
    fix.call_with_errno("dm_rtree_insert")?;
    let new_root = fix.vm.mem.read_into::<u64>(new_root_ptr, PERM_READ)?;
    let nr_inserts = fix.vm.mem.read_into::<u32>(nr_inserts_ptr, PERM_READ)?;
    Ok((new_root, nr_inserts))
}

pub fn dm_rtree_remove(
    fix: &mut Fixture,
    tm: Addr,
    data_sm: Addr,
    root: u64,
    thin_begin: u64,
    thin_end: u64,
) -> Result<u64> {
    let (mut fix, new_root_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, data_sm.0);
    fix.vm.set_reg(A2, root);
    fix.vm.set_reg(A3, thin_begin);
    fix.vm.set_reg(A4, thin_end);
    fix.vm.set_reg(A5, new_root_ptr.0);
    fix.call_with_errno("dm_rtree_remove")?;
    let new_root = fix.vm.mem.read_into::<u64>(new_root_ptr, PERM_READ)?;
    Ok(new_root)
}

//-------------------------------
