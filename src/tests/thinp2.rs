use anyhow::{anyhow, ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use libc::ENOSPC;
use log::*;
use std::io::{self, Read, Write};
use std::sync::{Arc, Mutex};

use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::stubs::*;
use crate::test_runner::*;

use Reg::*;

//-------------------------------

fn pack_bool(v: bool) -> u8 {
    if v {
        1
    } else {
        0
    }
}

fn unpack_bool(v: u8) -> bool {
    if v == 0 {
        false
    } else {
        true
    }
}

//-------------------------------

struct Waiter {
    want_intent: bool,
    want_upgrade: bool,
}

impl Guest for Waiter {
    fn guest_len() -> usize {
        32
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        // list
        w.write_u32::<LittleEndian>(0)?;
        w.write_u32::<LittleEndian>(0)?;

        // task
        w.write_u64::<LittleEndian>(0)?;

        w.write_u8(pack_bool(self.want_upgrade))?;
        w.write_u8(pack_bool(self.want_intent))?;

        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let _ = r.read_u32::<LittleEndian>()?;
        let _ = r.read_u32::<LittleEndian>()?;

        let want_upgrade = unpack_bool(r.read_u8()?);
        let want_intent = unpack_bool(r.read_u8()?);

        Ok(Waiter {
            want_intent,
            want_upgrade,
        })
    }
}

struct RIWLock {
    locked: bool,
    intent: bool,
    count: i32,
    waiters: Vec<Waiter>,
}

impl Default for RIWLock {
    fn default() -> Self {
        RIWLock {
            locked: false,
            intent: false,
            count: 0,
            waiters: vec![],
        }
    }
}

impl Guest for RIWLock {
    fn guest_len() -> usize {
        48
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u32::<LittleEndian>(pack_bool(self.locked) as u32)?;
        let bytes = [0u8; 20];
        w.write_all(&bytes)?;

        w.write_u8(pack_bool(self.intent))?;
        let bytes = [0u8; 3];
        w.write_all(&bytes)?;
        w.write_i32::<LittleEndian>(self.count)?;

        // The waiters will have to be written in a second
        // pass.
        w.write_u64::<LittleEndian>(0)?;
        w.write_u64::<LittleEndian>(0)?;

        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let locked = unpack_bool(r.read_u32::<LittleEndian>()? as u8);
        let mut bytes = [0u8; 20];
        r.read(&mut bytes)?;
        let intent = unpack_bool(r.read_u8()?);
        let mut bytes = [0u8; 3];
        r.read(&mut bytes)?;
        let count = r.read_i32::<LittleEndian>()?;
        let waiters = vec![];

        Ok(RIWLock {
            locked,
            intent,
            count,
            waiters,
        })
    }
}

fn pack_list_head(mem: &mut Memory, list_head: Addr, next: Addr, prev: Addr) -> Result<()> {
    mem.write_out(next.0, list_head, PERM_READ | PERM_WRITE)?;
    mem.write_out(prev.0, Addr(list_head.0 + 8), PERM_READ | PERM_WRITE)?;
    Ok(())
}

impl RIWLock {
    fn pack_waiters(&self, mem: &mut Memory, ptr: Addr) -> Result<()> {
        let mut waiters = Vec::new();
        for w in &self.waiters {
            let w_ptr = alloc_guest::<Waiter>(mem, &w, PERM_READ | PERM_WRITE)?;
            waiters.push(w_ptr);
        }

        let list_head = Addr(ptr.0 + 32);
        for i in 0..waiters.len() {
            let next = if i == (waiters.len() - 1) {
                list_head
            } else {
                waiters[i + 1]
            };
            let prev = if i == 0 { list_head } else { waiters[i - 1] };

            pack_list_head(mem, waiters[i], next, prev)?;
        }

        if self.waiters.len() > 0 {
            pack_list_head(mem, list_head, waiters[0], waiters[waiters.len() - 1])?;
        } else {
            pack_list_head(mem, list_head, list_head, list_head)?;
        }

        Ok(())
    }

    /*
    fn unpack_waiters(&self, _mem: &mut Memory, _ptr: Addr) -> Result<()> {
        Ok(())
    }

    fn unmap_waiters(&self, _mem: &mut Memory, _ptr: Addr) -> Result<()> {
        Ok(())
    }
    */
}

//-------------------------------

fn auto_riw<'a>(fix: &'a mut Fixture, riw: &RIWLock) -> Result<(AutoGPtr<'a>, Addr)> {
    let (mut fix, ptr) = auto_guest(fix, riw, PERM_READ | PERM_WRITE)?;
    riw.pack_waiters(&mut (*fix).vm.mem, ptr)?;
    Ok((fix, ptr))
}

fn riw_init(fix: &mut Fixture) -> Result<RIWLock> {
    let riw = RIWLock::default();
    let (mut fix, riw_ptr) = auto_guest(fix, &riw, PERM_READ | PERM_WRITE)?;

    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call_with_errno("riw_init")?;

    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;
    Ok(riw)
}

fn riw_down_read(fix: &mut Fixture, riw: &RIWLock) -> Result<RIWLock> {
    let (mut fix, riw_ptr) = auto_riw(fix, &riw)?;
    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call_with_errno("riw_down_read")?;
    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;

    Ok(riw)
}

fn riw_up_read(fix: &mut Fixture, riw: &RIWLock) -> Result<RIWLock> {
    let (mut fix, riw_ptr) = auto_riw(fix, &riw)?;
    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call("riw_up_read")?;
    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;

    Ok(riw)
}

fn riw_down_intent(fix: &mut Fixture, riw: &RIWLock) -> Result<RIWLock> {
    let (mut fix, riw_ptr) = auto_riw(fix, &riw)?;
    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call_with_errno("riw_down_intent")?;
    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;

    Ok(riw)
}

fn riw_up_intent(fix: &mut Fixture, riw: &RIWLock) -> Result<RIWLock> {
    let (mut fix, riw_ptr) = auto_riw(fix, &riw)?;
    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call("riw_up_intent")?;
    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;

    Ok(riw)
}

fn riw_down_write(fix: &mut Fixture, riw: &RIWLock) -> Result<RIWLock> {
    let (mut fix, riw_ptr) = auto_riw(fix, &riw)?;
    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call_with_errno("riw_down_write")?;
    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;

    Ok(riw)
}

fn riw_up_write(fix: &mut Fixture, riw: &RIWLock) -> Result<RIWLock> {
    let (mut fix, riw_ptr) = auto_riw(fix, &riw)?;
    fix.vm.set_reg(A0, riw_ptr.0);
    fix.call("riw_up_write")?;
    let riw = read_guest::<RIWLock>(&fix.vm.mem, riw_ptr)?;

    Ok(riw)
}

//-------------------------------

fn bp_init(fix: &mut Fixture, bp: Addr, nr_buffers: u64) -> Result<()> {
    fix.vm.set_reg(A0, bp.0);
    fix.vm.set_reg(A1, nr_buffers);
    fix.call_with_errno("bp_init")?;
    Ok(())
}

fn auto_bp(fix: &mut Fixture, nr_buffers: u64) -> Result<(AutoGPtr, Addr)> {
    const BP_SIZE: usize = 40;
    let (mut fix, bp_ptr) = auto_alloc(fix, BP_SIZE)?;
    bp_init(&mut *fix, bp_ptr, nr_buffers)?;
    Ok((fix, bp_ptr))
}

fn bp_exit(fix: &mut Fixture, bp: Addr) -> Result<()> {
    fix.vm.set_reg(A0, bp.0);
    fix.call_with_errno("bp_exit")?;
    Ok(())
}

fn return_buffer(fix: &mut Fixture) -> Result<Option<Addr>> {
    let buf = fix.vm.reg(A0);
    if buf == 0 {
        Ok(None)
    } else {
        Ok(Some(Addr(buf)))
    }
}

fn bp_find(fix: &mut Fixture, bp: Addr, loc: u64) -> Result<Option<Addr>> {
    fix.vm.set_reg(A0, bp.0);
    fix.vm.set_reg(A1, loc);
    fix.call("bp_find")?;
    return_buffer(fix)
}

fn bp_alloc(fix: &mut Fixture, bp: Addr, loc: u64) -> Result<Option<Addr>> {
    fix.vm.set_reg(A0, bp.0);
    fix.vm.set_reg(A1, loc);
    fix.call("bp_alloc")?;
    return_buffer(fix)
}

fn bp_free(fix: &mut Fixture, bp: Addr, buf: Addr) -> Result<()> {
    fix.vm.set_reg(A0, bp.0);
    fix.vm.set_reg(A1, buf.0);
    fix.call("bp_free")?;
    Ok(())
}

//-------------------------------

fn sm_init(fix: &mut Fixture, sm: Addr, nr_blocks: u64) -> Result<()> {
    fix.vm.set_reg(A0, sm.0);
    fix.vm.set_reg(A1, nr_blocks);
    fix.call_with_errno("sm_init")?;
    Ok(())
}

fn auto_sm(fix: &mut Fixture, nr_blocks: u64) -> Result<(AutoGPtr, Addr)> {
    const SM_SIZE: usize = 48;
    let (mut fix, sm_ptr) = auto_alloc(fix, SM_SIZE)?;
    sm_init(&mut *fix, sm_ptr, nr_blocks)?;
    Ok((fix, sm_ptr))
}

fn sm_exit(fix: &mut Fixture, sm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, sm.0);
    fix.call("sm_exit")?;
    Ok(())
}

fn sm_nr_free(fix: &mut Fixture, sm: Addr) -> Result<u64> {
    fix.vm.set_reg(A0, sm.0);
    fix.call("sm_nr_free")?;
    Ok(fix.vm.reg(A0))
}

fn sm_new(fix: &mut Fixture, sm: Addr) -> Result<Option<u64>> {
    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A0, sm.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call("sm_new")?;
    let r = fix.vm.reg(A0) as i32;
    if r == 0 {
        let loc = fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?;
        Ok(Some(loc))
    } else if r == -ENOSPC {
        Ok(None)
    } else if r < 0 {
        return Err(anyhow!("failed: {}", error_string(-r)));
    } else {
        return Err(anyhow!("failed: {}", r));
    }
}

fn sm_get(fix: &mut Fixture, sm: Addr, loc: u64) -> Result<u8> {
    fix.vm.set_reg(A0, sm.0);
    fix.vm.set_reg(A1, loc);
    fix.call("sm_get")?;
    Ok(fix.vm.reg(A0) as u8)
}

fn sm_inc(fix: &mut Fixture, sm: Addr, loc: u64) -> Result<()> {
    fix.vm.set_reg(A0, sm.0);
    fix.vm.set_reg(A1, loc);
    fix.call_with_errno("sm_inc")?;
    Ok(())
}

fn sm_dec(fix: &mut Fixture, sm: Addr, loc: u64) -> Result<()> {
    fix.vm.set_reg(A0, sm.0);
    fix.vm.set_reg(A1, loc);
    fix.call_with_errno("sm_dec")?;
    Ok(())
}

fn sm_commit(fix: &mut Fixture, sm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, sm.0);
    fix.call_with_errno("sm_commit")?;
    Ok(())
}

//-------------------------------

fn riw_globals(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let _ = fix.stub("get_current_", 0)?;
    let _ = fix.stub("put_current_", 0)?;
    let _ = fix.stub("get_task_struct_", 0)?;
    Ok(())
}

// Checks func eventually hits __wait.
fn ensure_blocks<F>(fix: &mut Fixture, func: F) -> Result<()>
where
    F: Fn(&mut Fixture) -> Result<()>,
{
    let blocked = Arc::new(Mutex::new(false));
    {
        let blocked = blocked.clone();
        let my_wait = move |_fix: &mut Fixture| {
            let mut blocked = blocked.lock().unwrap();
            *blocked = true;
            Err(anyhow!("in __wait"))
        };
        fix.at_func("__wait", Box::new(my_wait))?;
    }

    ensure!(func(fix).is_err());

    let blocked = blocked.lock().unwrap();
    ensure!(*blocked);
    Ok(())
}

fn test_riw_init(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 0);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_read_unlocked(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_read(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 1);
    ensure!(riw.waiters.len() == 0);

    let riw = riw_up_read(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 0);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_read_many(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_read(fix, &riw)?;
    let riw = riw_down_read(fix, &riw)?;
    let riw = riw_down_read(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 3);
    ensure!(riw.waiters.len() == 0);

    let riw = riw_up_read(fix, &riw)?;
    let riw = riw_up_read(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 1);
    ensure!(riw.waiters.len() == 0);

    let riw = riw_up_read(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 0);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_read_intent_held(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_intent(fix, &riw)?;
    ensure!(riw.intent);

    let riw = riw_down_read(fix, &riw)?;
    ensure!(!riw.locked);
    ensure!(riw.intent);
    ensure!(riw.count == 2);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_read_write_held(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_write(fix, &riw)?;

    ensure_blocks(fix, |fix| {
        let _ = riw_down_read(fix, &riw)?;
        Ok(())
    })?;

    Ok(())
}

fn test_riw_down_intent_unlocked(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_intent(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(riw.intent);
    ensure!(riw.count == 1);
    ensure!(riw.waiters.len() == 0);

    let riw = riw_up_intent(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 0);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_intent_read_held(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_read(fix, &riw)?;
    let riw = riw_down_intent(fix, &riw)?;

    ensure!(riw.intent);
    ensure!(riw.count == 2);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_intent_many(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_intent(fix, &riw)?;

    ensure_blocks(fix, |fix| {
        let _ = riw_down_intent(fix, &riw)?;
        Ok(())
    })?;

    Ok(())
}

fn test_riw_down_intent_write_held(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_write(fix, &riw)?;

    ensure_blocks(fix, |fix| {
        let _ = riw_down_intent(fix, &riw)?;
        Ok(())
    })?;

    Ok(())
}

fn test_riw_down_write_unlocked(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_write(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == -1);
    ensure!(riw.waiters.len() == 0);

    let riw = riw_up_write(fix, &riw)?;

    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 0);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_write_read_held(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_read(fix, &riw)?;

    ensure_blocks(fix, |fix| {
        let _ = riw_down_write(fix, &riw)?;
        Ok(())
    })?;

    Ok(())
}

fn test_riw_down_write_intent_held(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_intent(fix, &riw)?;

    ensure_blocks(fix, |fix| {
        let _ = riw_down_write(fix, &riw)?;
        Ok(())
    })?;

    Ok(())
}

fn test_riw_down_write_many(fix: &mut Fixture) -> Result<()> {
    riw_globals(fix)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_write(fix, &riw)?;

    ensure_blocks(fix, |fix| {
        let _ = riw_down_write(fix, &riw)?;
        Ok(())
    })?;

    Ok(())
}

//-------------------------------

fn test_bp_init(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, bp_ptr) = auto_bp(fix, 1024)?;
    bp_exit(&mut *fix, bp_ptr)?;
    Ok(())
}

fn test_bp_find_fails(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, bp_ptr) = auto_bp(fix, 1024)?;
    let _buf_ptr = bp_find(&mut *fix, bp_ptr, 0)?;
    Ok(())
}

fn test_bp_alloc_runs_out_of_space(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let count = 1024u64;
    let (mut fix, bp_ptr) = auto_bp(fix, count)?;

    for i in 0..count {
        let _buf = bp_alloc(&mut *fix, bp_ptr, i)?;
    }

    let result = bp_alloc(&mut *fix, bp_ptr, count * 2)?;
    ensure!(result.is_none());
    Ok(())
}

fn test_bp_finds_buffers(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let count = 1024;
    let (mut fix, bp_ptr) = auto_bp(fix, count)?;

    let mut bufs = Vec::with_capacity(20);
    for i in 0..20 {
        bufs.push(bp_alloc(&mut *fix, bp_ptr, i)?.unwrap());
    }

    for i in 0..20 {
        let found = bp_find(&mut *fix, bp_ptr, i)?.unwrap();
        debug!(
            "bufs[{}] = {:?}, bp_find = {:?}",
            i, bufs[i as usize], found
        );
        ensure!(bufs[i as usize] == found);
    }

    Ok(())
}

fn test_bp_frees(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let count = 1024;
    let (mut fix, bp_ptr) = auto_bp(fix, count)?;

    for i in 0..20 {
        ensure!(bp_alloc(&mut *fix, bp_ptr, i)?.is_some());
    }

    for i in 0..20 {
        let buf = bp_find(&mut *fix, bp_ptr, i).unwrap().unwrap();
        bp_free(&mut *fix, bp_ptr, buf)?;
    }

    for i in 0..20 {
        ensure!(bp_find(&mut *fix, bp_ptr, i)?.is_none());
    }

    Ok(())
}

fn test_bp_rolling(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let count = 1024;
    let (mut fix, bp_ptr) = auto_bp(fix, count)?;

    for i in 0..(count * 10) {
        if i >= count {
            let old_buf = bp_find(&mut *fix, bp_ptr, i - count)?.unwrap();
            bp_free(&mut *fix, bp_ptr, old_buf)?;
        }

        ensure!(bp_alloc(&mut *fix, bp_ptr, i)?.is_some());
    }

    Ok(())
}

//-------------------------------

fn test_sm_init(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let count = 12345;
    let (mut fix, sm_ptr) = auto_sm(fix, count)?;
    ensure!(sm_nr_free(&mut *fix, sm_ptr)? == count);
    sm_exit(&mut *fix, sm_ptr)?;
    Ok(())
}

fn test_sm_new(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let nr_blocks = 128u64;
    let (mut fix, sm_ptr) = auto_sm(fix, nr_blocks)?;

    let count = 128u64;
    let mut blocks = Vec::with_capacity(count as usize);
    for _i in 0..count {
        blocks.push(sm_new(&mut *fix, sm_ptr)?.unwrap());
    }

    for i in 0..count {
        ensure!(sm_get(&mut *fix, sm_ptr, blocks[i as usize])? == 1);
    }

    ensure!(sm_new(&mut *fix, sm_ptr)?.is_none());

    ensure!(sm_nr_free(&mut *fix, sm_ptr)? == nr_blocks - count);
    sm_exit(&mut *fix, sm_ptr)?;
    Ok(())
}

fn test_sm_inc_dec(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let nr_blocks = 128u64;
    let (mut fix, sm_ptr) = auto_sm(fix, nr_blocks)?;

    debug!("1");
    let b = sm_new(&mut *fix, sm_ptr)?.unwrap();
    ensure!(sm_get(&mut *fix, sm_ptr, b)? == 1);

    debug!("2");
    sm_inc(&mut *fix, sm_ptr, b)?;
    sm_inc(&mut *fix, sm_ptr, b)?;
    ensure!(sm_get(&mut *fix, sm_ptr, b)? == 3);

    debug!("3");
    sm_dec(&mut *fix, sm_ptr, b)?;
    sm_dec(&mut *fix, sm_ptr, b)?;
    ensure!(sm_get(&mut *fix, sm_ptr, b)? == 1);

    debug!("4");
    sm_dec(&mut *fix, sm_ptr, b)?;
    ensure!(sm_get(&mut *fix, sm_ptr, b)? == 0);

    debug!("5");
    sm_exit(&mut *fix, sm_ptr)?;
    Ok(())
}

fn test_sm_freed_blocks_can_be_allocated(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let nr_blocks = 128u64;
    let (mut fix, sm_ptr) = auto_sm(fix, nr_blocks)?;

    // allocate all blocks
    let mut blocks = Vec::with_capacity(nr_blocks as usize);
    for _i in 0..nr_blocks {
        blocks.push(sm_new(&mut *fix, sm_ptr)?.unwrap());
    }

    // confirm we can't allocate any more
    ensure!(sm_new(&mut *fix, sm_ptr)?.is_none());

    // free one of the blocks
    sm_dec(&mut *fix, sm_ptr, 12)?;

    // We must commit to see the free block
    sm_commit(&mut *fix, sm_ptr)?;

    // We should have 1 free block now
    ensure!(sm_nr_free(&mut *fix, sm_ptr)? == 1);

    // new should allocate the block we just freed
    let b = sm_new(&mut *fix, sm_ptr)?.unwrap();
    ensure!(b == 12);

    sm_exit(&mut *fix, sm_ptr)?;
    Ok(())
}

/*
// - No block may be allocated that is present in the previous transaction
fn test_sm_no_alloc_from_prior_trans(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let nr_blocks = 128u64;
    let (mut fix, sm_ptr) = auto_sm(fix, nr_blocks)?;

    // allocate all blocks
    let mut blocks = Vec::with_capacity(nr_blocks as usize);
    for _i in 0..nr_blocks {
        blocks.push(sm_new(&mut *fix, sm_ptr)?.unwrap());
    }

    // confirm we can't allocate any more
    ensure!(sm_new(&mut *fix, sm_ptr)?.is_none());

    sm_commit(&mut *fix, sm_ptr)?;



    // free one of the blocks
    sm_dec(&mut *fix, sm_ptr, 12)?;

    // We should have 1 free block now
    ensure!(sm_nr_free(&mut *fix, sm_ptr)? == 1);

    // new should allocate the block we just freed
    let b = sm_new(&mut *fix, sm_ptr)?.unwrap();
    ensure!(b == 12);

    sm_exit(&mut *fix, sm_ptr)?;
    Ok(())
    Ok(())
}
*/

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![THIN2_MOD, RBTREE_MOD];
    let mut prefix: Vec<&'static str> = Vec::new();

    macro_rules! test_section {
        ($path:expr, $($s:stmt)*) => {{
            prefix.push($path);
            $($s)*
            prefix.pop().unwrap();
        }}
    }

    macro_rules! test {
        ($path:expr, $func:expr) => {{
            prefix.push($path);
            let p = prefix.concat();
            prefix.pop().unwrap();
            runner.register(&p, Test::new(kmodules.clone(), Box::new($func)));
        }};
    }

    test_section! {
        "/thinp2/",

        test_section! {
            "riw/",
            test!("init", test_riw_init)
            test!("down-read-unlocked", test_riw_down_read_unlocked)
            test!("down-read-many", test_riw_down_read_many)
            test!("down-read-intent-held", test_riw_down_read_intent_held)
            test!("down-read-write-held", test_riw_down_read_write_held)

            test!("down-intent-unlocked", test_riw_down_intent_unlocked)
            test!("down-intent-read-held", test_riw_down_intent_read_held)
            test!("down-intent-many", test_riw_down_intent_many)
            test!("down-intent-write-held", test_riw_down_intent_write_held)

            test!("down-write-unlocked", test_riw_down_write_unlocked)
            test!("down-write-read-held", test_riw_down_write_read_held)
            test!("down-write-intent-held", test_riw_down_write_intent_held)
            test!("down-write-many", test_riw_down_write_many)
        }

        test_section! {
            "buffer-pool/",
            test!("init", test_bp_init)
            test!("find-fails", test_bp_find_fails)
            test!("alloc-runs-out-of-space", test_bp_alloc_runs_out_of_space)
            test!("finds-allocated-buffers", test_bp_finds_buffers)
            test!("frees", test_bp_frees)
            test!("rolling-allocations", test_bp_rolling)
        }

        test_section! {
            "space-map/",
            test!("init", test_sm_init)
            test!("new", test_sm_new)
            test!("inc-dec", test_sm_inc_dec)
            test!("freed-blocks-can-be-allocated", test_sm_freed_blocks_can_be_allocated)
        }
    }

    Ok(())
}

//-------------------------------
