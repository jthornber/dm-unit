use crate::decode::*;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;

use anyhow::{ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use std::io;
use std::io::{Read, Write};
use std::marker::PhantomData;

use Reg::*;

//-------------------------------

pub struct BTreeValueType<G: Guest> {
    pub context: Addr,
    pub inc_fn: Addr,
    pub dec_fn: Addr,
    pub eq_fn: Addr,
    pub rust_value_type: PhantomData<G>,
}

impl<G: Guest> Guest for BTreeValueType<G> {
    fn guest_len() -> usize {
        // 4 functions ptrs and a u32
        4 * 8 + 4
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.context.0)?;
        w.write_u32::<LittleEndian>(G::guest_len() as u32)?;
        w.write_u32::<LittleEndian>(0)?; // padding
        w.write_u64::<LittleEndian>(self.inc_fn.0)?;
        w.write_u64::<LittleEndian>(self.dec_fn.0)?;
        w.write_u64::<LittleEndian>(self.eq_fn.0)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let context = Addr(r.read_u64::<LittleEndian>()?);
        let size = r.read_u32::<LittleEndian>()?;
        let _padding = r.read_u32::<LittleEndian>()?;
        let inc_fn = Addr(r.read_u64::<LittleEndian>()?);
        let dec_fn = Addr(r.read_u64::<LittleEndian>()?);
        let eq_fn = Addr(r.read_u64::<LittleEndian>()?);

        assert!(size == G::guest_len() as u32);

        Ok(BTreeValueType {
            context,
            inc_fn,
            dec_fn,
            eq_fn,
            rust_value_type: PhantomData,
        })
    }
}

pub struct BTreeInfo<G: Guest> {
    pub tm: Addr,
    pub levels: u32,
    pub vtype: BTreeValueType<G>,
}

impl<G: Guest> Guest for BTreeInfo<G> {
    fn guest_len() -> usize {
        8 + 4 + BTreeValueType::<G>::guest_len()
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.tm.0)?;
        w.write_u32::<LittleEndian>(self.levels)?;
        w.write_u32::<LittleEndian>(0)?; // padding
        self.vtype.pack(w)
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let tm = Addr(r.read_u64::<LittleEndian>()?);
        let levels = r.read_u32::<LittleEndian>()?;
        let _padding = r.read_u32::<LittleEndian>()?;
        let vtype = BTreeValueType::unpack(r)?;

        Ok(BTreeInfo { tm, levels, vtype })
    }
}

pub fn auto_info<'a, G: Guest>(
    fix: &'a mut Fixture,
    info: &BTreeInfo<G>,
) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = alloc_guest(&mut fix.vm.mem, info, PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

pub fn dm_btree_empty<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;

    fix.vm.set_reg(A0, info_ptr.0);
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call_with_errno("dm_btree_empty")?;
    Ok(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?)
}

pub fn dm_btree_del<G: Guest>(fix: &mut Fixture, info: &BTreeInfo<G>, root: u64) -> Result<()> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    debug!("about to call dm_btree_del");
    fix.call_with_errno("dm_btree_del")
}

fn auto_keys<'a>(fix: &'a mut Fixture, keys: &[u64]) -> Result<(AutoGPtr<'a>, Addr)> {
    let ptr = fix.vm.mem.alloc(8 * keys.len())?;

    for (i, _item) in keys.iter().enumerate() {
        let bytes = keys[i].to_le_bytes();
        fix.vm
            .mem
            .write(Addr(ptr.0 + (8 * i as u64)), &bytes, PERM_WRITE)?;
    }

    Ok((AutoGPtr::new(fix, ptr), ptr))
}

// Returns the new root
pub fn dm_btree_insert<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
    v: &G,
) -> Result<u64> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;
    let (mut fix, guest_keys) = auto_keys(&mut *fix, keys)?;
    let (mut fix, guest_value) = auto_guest(&mut *fix, v, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root) = auto_alloc(&mut *fix, 8)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, guest_keys.0);
    fix.vm.set_reg(A3, guest_value.0);
    fix.vm.set_reg(A4, new_root.0);

    fix.call_with_errno("dm_btree_insert")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root, PERM_READ)?;
    Ok(new_root)
}

pub fn dm_btree_insert_notify<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
    v: &G,
) -> Result<(u64, bool)> {
    let (mut fix, info_ptr) = auto_info(fix, info)?;
    let (mut fix, guest_keys) = auto_keys(&mut *fix, keys)?;
    let (mut fix, guest_value) = auto_guest(&mut *fix, v, PERM_READ | PERM_WRITE)?;
    let (mut fix, new_root) = auto_alloc(&mut *fix, 8)?;
    let (mut fix, inserted_ptr) = auto_alloc(&mut *fix, 4)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, guest_keys.0);
    fix.vm.set_reg(A3, guest_value.0);
    fix.vm.set_reg(A4, new_root.0);
    fix.vm.set_reg(A5, inserted_ptr.0);

    fix.call_with_errno("dm_btree_insert_notify")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root, PERM_READ)?;
    let inserted = fix.vm.mem.read_into::<u32>(inserted_ptr, PERM_READ)?;

    Ok((new_root, inserted != 0))
}

pub fn dm_btree_lookup<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
) -> Result<G> {
    ensure!(keys.len() == info.levels as usize);

    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);

    let (mut fix, keys_ptr) = auto_keys(&mut *fix, keys)?;
    fix.vm.set_reg(A2, keys_ptr.0);

    let (mut fix, value_ptr) = auto_alloc(&mut *fix, G::guest_len())?;
    fix.vm.set_reg(A3, value_ptr.0);

    fix.call_with_errno("dm_btree_lookup")?;

    let value = read_guest::<G>(&fix.vm.mem, value_ptr)?;
    Ok(value)
}

pub fn dm_btree_lookup_next<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
) -> Result<(Vec<u64>, G)> {
    ensure!(keys.len() == info.levels as usize);

    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);

    let (mut fix, keys_ptr) = auto_keys(&mut *fix, keys)?;
    fix.vm.set_reg(A2, keys_ptr.0);

    let (mut fix, rkeys_ptr) = auto_alloc(&mut *fix, 8 * info.levels as usize)?;
    fix.vm.set_reg(A3, rkeys_ptr.0);

    let (mut fix, value_ptr) = auto_alloc(&mut *fix, G::guest_len())?;

    fix.call_with_errno("dm_btree_lookup_next")?;

    let mut rkeys = Vec::new();
    for i in 0..keys.len() {
        let r = fix
            .vm
            .mem
            .read_into::<u64>(Addr(rkeys_ptr.0 + (8 * i as u64)), PERM_READ)?;
        rkeys.push(r);
    }

    let value = read_guest::<G>(&fix.vm.mem, value_ptr)?;
    Ok((rkeys, value))
}

pub fn dm_btree_remove<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
) -> Result<u64> {
    ensure!(keys.len() == info.levels as usize);

    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);

    let (mut fix, keys_ptr) = auto_keys(&mut *fix, keys)?;
    fix.vm.set_reg(A2, keys_ptr.0);

    let (mut fix, new_root_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A3, new_root_ptr.0);

    fix.call_with_errno("dm_btree_remove")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root_ptr, PERM_READ)?;
    Ok(new_root)
}

pub fn dm_btree_remove_leaves<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
    keys: &[u64],
    end_key: u64,
) -> Result<(u64, u32)> {
    ensure!(keys.len() == info.levels as usize);

    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    let (mut fix, keys_ptr) = auto_keys(&mut *fix, keys)?;
    let (mut fix, new_root_ptr) = auto_alloc(&mut *fix, 8)?;
    let (mut fix, inserted_ptr) = auto_alloc(&mut *fix, 4)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, keys_ptr.0);
    fix.vm.set_reg(A3, end_key);
    fix.vm.set_reg(A4, new_root_ptr.0);

    fix.call_with_errno("dm_btree_remove_leaves")?;

    let new_root = fix.vm.mem.read_into::<u64>(new_root_ptr, PERM_READ)?;
    let inserted = fix.vm.mem.read_into::<u32>(inserted_ptr, PERM_READ)?;
    Ok((new_root, inserted))
}

pub fn dm_btree_find_lowest_key<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
) -> Result<Vec<u64>> {
    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    let (mut fix, rkeys_ptr) = auto_alloc(&mut *fix, 8 * info.levels as usize)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, rkeys_ptr.0);

    fix.call_with_errno("dm_btree_find_lowest_key")?;

    let mut rkeys = Vec::new();
    for i in 0..info.levels {
        let r = fix
            .vm
            .mem
            .read_into::<u64>(Addr(rkeys_ptr.0 + (8 * i as u64)), PERM_READ)?;
        rkeys.push(r);
    }

    Ok(rkeys)
}

pub fn dm_btree_find_highest_key<G: Guest>(
    fix: &mut Fixture,
    info: &BTreeInfo<G>,
    root: u64,
) -> Result<Vec<u64>> {
    let (mut fix, info_ptr) = auto_info(fix, &info)?;
    let (mut fix, rkeys_ptr) = auto_alloc(&mut *fix, 8 * info.levels as usize)?;

    fix.vm.set_reg(A0, info_ptr.0);
    fix.vm.set_reg(A1, root);
    fix.vm.set_reg(A2, rkeys_ptr.0);

    fix.call_with_errno("dm_btree_find_highest_key")?;

    let mut rkeys = Vec::new();
    for i in 0..info.levels {
        let r = fix
            .vm
            .mem
            .read_into::<u64>(Addr(rkeys_ptr.0 + (8 * i as u64)), PERM_READ)?;
        rkeys.push(r);
    }

    Ok(rkeys)
}

//-------------------------------

pub struct ShadowSpine {
    info: Addr,
    nodes: Vec<Addr>,
    root: u64,
}

impl Guest for ShadowSpine {
    fn guest_len() -> usize {
        40
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.info.0)?;
        assert!(self.nodes.len() <= 2);
        w.write_u32::<LittleEndian>(self.nodes.len() as u32)?;
        w.write_u32::<LittleEndian>(0)?; // padding

        match self.nodes.len() {
            0 => {
                w.write_u64::<LittleEndian>(0)?;
                w.write_u64::<LittleEndian>(0)?;
            }
            1 => {
                w.write_u64::<LittleEndian>(self.nodes[0].0)?;
                w.write_u64::<LittleEndian>(0)?;
            }
            2 => {
                w.write_u64::<LittleEndian>(self.nodes[0].0)?;
                w.write_u64::<LittleEndian>(self.nodes[1].0)?;
            }
            _ => {
                assert!(false);
            }
        }
        w.write_u64::<LittleEndian>(self.root)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let info = Addr(r.read_u64::<LittleEndian>()?);
        let count = r.read_u32::<LittleEndian>()?;
        let _padding = r.read_u32::<LittleEndian>()?;

        assert!(count <= 3);

        let mut nodes = Vec::new();
        for _ in 0..count {
            nodes.push(Addr(r.read_u64::<LittleEndian>()?));
        }

        for _ in count..2 {
            let _ = r.read_u64::<LittleEndian>()?;
        }

        let root = r.read_u64::<LittleEndian>()?;

        Ok(ShadowSpine { info, nodes, root })
    }
}

pub fn split_one_into_two<V: Guest>(
    fix: &mut Fixture,
    spine: &mut ShadowSpine,
    parent_index: usize,
    vt: &BTreeValueType<V>,
    key: u64,
) -> Result<()> {
    let (mut fix, spine_ptr) = auto_guest::<ShadowSpine>(fix, spine, PERM_READ | PERM_WRITE)?;
    let (mut fix, vt_ptr) = auto_guest::<BTreeValueType<V>>(&mut *fix, vt, PERM_READ | PERM_WRITE)?;

    fix.vm.set_reg(A0, spine_ptr.0);
    fix.vm.set_reg(A1, parent_index as u64);
    fix.vm.set_reg(A2, vt_ptr.0);
    fix.vm.set_reg(A3, key);

    fix.call_with_errno("split_one_into_two")?;

    *spine = read_guest::<ShadowSpine>(&fix.vm.mem, spine_ptr)?;
    Ok(())
}

//-------------------------------

pub fn redistribute2(fix: &mut Fixture, left: Addr, right: Addr) -> Result<()> {
    fix.vm.set_reg(A0, left.0);
    fix.vm.set_reg(A1, right.0);

    fix.call("redistribute2")?;

    Ok(())
}

//-------------------------------

pub fn redistribute3(fix: &mut Fixture, left: Addr, center: Addr, right: Addr) -> Result<()> {
    fix.vm.set_reg(A0, left.0);
    fix.vm.set_reg(A1, center.0);
    fix.vm.set_reg(A2, right.0);

    fix.call("redistribute3")?;

    Ok(())
}

//-------------------------------
