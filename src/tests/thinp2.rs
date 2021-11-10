use anyhow::{anyhow, ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use libc::{ENODATA, ENOSPC};
use log::*;
use nom::{number::complete::*, IResult};
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{self, Read, Write};
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};
use thinp::pdata::unpack::*;

use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::stubs::block_device::*;
use crate::stubs::*;
use crate::test_runner::*;

use Reg::*;

//-------------------------------

const MD_BLOCK_SIZE: usize = 4096;

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

#[allow(dead_code)]
enum RIWType {
    RIWRead,
    RIWIntent,
    RIWWrite,
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

fn tm_init(
    fix: &mut Fixture,
    tm: Addr,
    bdev: Addr,
    nr_buffers: u64,
    max_per_thread: u64,
) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, bdev.0);
    fix.vm.set_reg(A2, nr_buffers);
    fix.vm.set_reg(A3, max_per_thread);
    fix.call_with_errno("tm_init")?;
    Ok(())
}

fn auto_tm(fix: &mut Fixture, bdev: Addr, nr_buffers: u64) -> Result<(AutoGPtr, Addr)> {
    const TM_SIZE: usize = 200;
    let (mut fix, tm_ptr) = auto_alloc(fix, TM_SIZE)?;
    tm_init(&mut *fix, tm_ptr, bdev, nr_buffers, 16)?;
    Ok((fix, tm_ptr))
}

fn tm_exit(fix: &mut Fixture, tm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.call("tm_exit")?;
    Ok(())
}

fn tm_new(fix: &mut Fixture, tm: Addr) -> Result<Option<u64>> {
    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, result_ptr.0);
    fix.call("tm_new")?;
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

fn tm_get(fix: &mut Fixture, tm: Addr, loc: u64, lt: RIWType) -> Result<Addr> {
    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, loc);

    use RIWType::*;
    let lt = match lt {
        RIWRead => 1,
        RIWIntent => 2,
        RIWWrite => 3,
    };

    fix.vm.set_reg(A2, lt);
    fix.vm.set_reg(A3, result_ptr.0);
    fix.call_with_errno("tm_get")?;

    Ok(Addr(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?))
}

fn tm_commit(fix: &mut Fixture, tm: Addr, sb_data: Addr) -> Result<()> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, sb_data.0);
    fix.call_with_errno("tm_commit")?;

    // check there's no pending io

    Ok(())
}

struct TMStats {
    nr_read: u64,
    nr_intent: u64,
    nr_upgrade: u64,
    nr_write: u64,
}

impl Default for TMStats {
    fn default() -> Self {
        TMStats {
            nr_read: 0,
            nr_intent: 0,
            nr_upgrade: 0,
            nr_write: 0,
        }
    }
}

impl TMStats {
    fn delta(&self, rhs: &TMStats) -> Self {
        let nr_read = rhs.nr_read - self.nr_read;
        let nr_intent = rhs.nr_intent - self.nr_intent;
        let nr_upgrade = rhs.nr_upgrade - self.nr_upgrade;
        let nr_write = rhs.nr_write - self.nr_write;

        TMStats {
            nr_read,
            nr_intent,
            nr_upgrade,
            nr_write,
        }
    }
}

impl Guest for TMStats {
    fn guest_len() -> usize {
        32
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.nr_read)?;
        w.write_u64::<LittleEndian>(self.nr_intent)?;
        w.write_u64::<LittleEndian>(self.nr_upgrade)?;
        w.write_u64::<LittleEndian>(self.nr_write)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let nr_read = r.read_u64::<LittleEndian>()?;
        let nr_intent = r.read_u64::<LittleEndian>()?;
        let nr_upgrade = r.read_u64::<LittleEndian>()?;
        let nr_write = r.read_u64::<LittleEndian>()?;
        Ok(TMStats {
            nr_read,
            nr_intent,
            nr_upgrade,
            nr_write,
        })
    }
}

fn tm_stats(fix: &mut Fixture, tm: Addr) -> Result<TMStats> {
    fix.vm.set_reg(A0, tm.0);
    fix.call("tm_stats")?;
    let result = Addr(fix.vm.reg(A0));
    Ok(read_guest::<TMStats>(&fix.vm.mem, result)?)
}

fn buffer_add(fix: &mut Fixture, list: Addr, buf_ptr: Addr) -> Result<()> {
    fix.vm.set_reg(A0, list.0);
    fix.vm.set_reg(A1, buf_ptr.0);
    fix.call("buffer_add")?;
    Ok(())
}

fn buffer_loc(fix: &mut Fixture, buf_ptr: Addr) -> Result<u64> {
    fix.vm.set_reg(A0, buf_ptr.0);
    fix.call("buffer_loc")?;
    Ok(fix.vm.reg(A0))
}

fn buffer_data(fix: &mut Fixture, buf_ptr: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, buf_ptr.0);
    fix.call("buffer_data")?;
    Ok(Addr(fix.vm.reg(A0)))
}

//-------------------------------

struct FakeIoEngine {
    nr_blocks: usize,
    data: BTreeMap<u64, Vec<u8>>,
    pending: BTreeMap<Addr, u64>,
}

impl FakeIoEngine {
    fn new(nr_blocks: usize) -> Self {
        FakeIoEngine {
            nr_blocks,
            data: BTreeMap::new(),
            pending: BTreeMap::new(),
        }
    }

    fn check_no_pending(&self) -> Result<()> {
        if !self.pending.is_empty() {
            Err(anyhow!("There was unexpected pending io."))
        } else {
            Ok(())
        }
    }
}

fn io_init(fix: &mut Fixture) -> Result<()> {
    let io_ptr = Addr(fix.vm.reg(A0));
    let bdev_ptr = Addr(fix.vm.reg(A1));
    let block_size = fix.vm.reg(A2);

    ensure!(block_size == 8);

    let bdev = read_guest::<BlockDevice>(&fix.vm.mem, bdev_ptr)?;
    let inode = read_guest::<INode>(&fix.vm.mem, bdev.inode)?;

    let nr_blocks = inode.nr_sectors / 8;
    let engine = Arc::new(Mutex::new(FakeIoEngine::new(nr_blocks as usize)));

    fix.contexts.insert(io_ptr, engine.clone());

    fix.vm.ret(0);
    Ok(())
}

fn io_exit(fix: &mut Fixture) -> Result<()> {
    let io_ptr = Addr(fix.vm.reg(A0));

    let _engine: Box<Arc<Mutex<FakeIoEngine>>> = fix.contexts.remove(&io_ptr);

    Ok(())
}

fn io_nr_blocks(fix: &mut Fixture) -> Result<()> {
    let io_ptr = Addr(fix.vm.reg(A0));
    let engine = fix
        .contexts
        .get::<Arc<Mutex<FakeIoEngine>>>(&io_ptr)
        .unwrap()
        .clone();
    let engine = engine.lock().unwrap();

    fix.vm.ret(engine.nr_blocks as u64);

    Ok(())
}

fn io_issue(fix: &mut Fixture) -> Result<()> {
    let io_ptr = Addr(fix.vm.reg(A0));
    let io_dir = fix.vm.reg(A1);
    let buf_ptr = Addr(fix.vm.reg(A2));

    let engine = fix
        .contexts
        .get::<Arc<Mutex<FakeIoEngine>>>(&io_ptr)
        .unwrap()
        .clone();
    let mut engine = engine.lock().unwrap();

    let old = engine.pending.insert(buf_ptr, io_dir);
    ensure!(old.is_none());
    fix.vm.ret(0);

    Ok(())
}

fn exec_io(fix: &mut Fixture, engine: &mut FakeIoEngine, buf_ptr: Addr, io_dir: u64) -> Result<()> {
    let loc = buffer_loc(fix, buf_ptr)?;
    let data = buffer_data(fix, buf_ptr)?;

    match io_dir {
        0 => {
            // Read
            let on_disk = engine.data.entry(loc).or_insert_with(|| vec![0u8; 4096]);
            fix.vm.mem.write(data, on_disk, PERM_READ | PERM_WRITE)?;
            Ok(())
        }
        1 => {
            // Write
            let on_disk = engine.data.entry(loc).or_insert_with(|| vec![0u8; 4096]);
            fix.vm.mem.read(data, on_disk, PERM_READ | PERM_WRITE)?;
            Ok(())
        }
        _ => {
            return Err(anyhow!("bad io_dir"));
        }
    }
}

fn io_wait_buffer(fix: &mut Fixture) -> Result<()> {
    let io_ptr = Addr(fix.vm.reg(A0));
    let buf_ptr = Addr(fix.vm.reg(A1));

    let engine = fix
        .contexts
        .get::<Arc<Mutex<FakeIoEngine>>>(&io_ptr)
        .unwrap()
        .clone();
    let mut engine = engine.lock().unwrap();

    let io_dir = engine.pending.remove(&buf_ptr).unwrap();
    exec_io(fix, &mut engine, buf_ptr, io_dir)?;

    fix.vm.ret(0);
    Ok(())
}

fn io_wait(fix: &mut Fixture) -> Result<()> {
    let io_ptr = Addr(fix.vm.reg(A0));
    let _count = fix.vm.reg(A1);
    let completed = Addr(fix.vm.reg(A2));

    let engine = fix
        .contexts
        .get::<Arc<Mutex<FakeIoEngine>>>(&io_ptr)
        .unwrap()
        .clone();
    let mut engine = engine.lock().unwrap();

    while !engine.pending.is_empty() {
        let (buf_ptr, io_dir) = engine.pending.pop_first().unwrap();
        exec_io(fix, &mut engine, buf_ptr, io_dir)?;
        buffer_add(fix, completed, buf_ptr)?;
    }

    fix.vm.ret(0);
    Ok(())
}

fn check_no_pending_io(fix: &mut Fixture, btree_ptr: Addr) -> Result<()> {
    let io_ptr = btree_to_engine(fix, btree_ptr)?;
    let engine = fix
        .contexts
        .get::<Arc<Mutex<FakeIoEngine>>>(&io_ptr)
        .unwrap()
        .clone();
    let engine = engine.lock().unwrap();

    engine.check_no_pending()
}

fn stub_io_engine(fix: &mut Fixture) -> Result<()> {
    fix.at_func("io_init", Box::new(io_init))?;
    fix.at_func("io_exit", Box::new(io_exit))?;
    fix.at_func("io_nr_blocks", Box::new(io_nr_blocks))?;
    fix.at_func("io_issue", Box::new(io_issue))?;
    fix.at_func("io_wait_buffer", Box::new(io_wait_buffer))?;
    // fix.at_func("io_wait", Box::new(io_wait))?;
    Ok(())
}

//-------------------------------

struct StatsTracker {
    tm_ptr: Addr,
    csv: File,
    iteration: usize,
    nr_instructions: u64,
    baseline: TMStats,
}

impl StatsTracker {
    fn new(path: &str, tm_ptr: Addr) -> Result<Self> {
        let mut csv = File::create(path)?;
        write!(
            csv,
            "iteration, instructions, read, intent, upgrades, writes\n"
        )?;

        let baseline = TMStats::default();

        Ok(StatsTracker {
            csv,
            iteration: 0,
            nr_instructions: 0,
            tm_ptr,
            baseline,
        })
    }

    fn checkpoint(&mut self, fix: &mut Fixture) -> Result<()> {
        let new_stats = tm_stats(&mut *fix, self.tm_ptr)?;
        let stats = self.baseline.delta(&new_stats);
        let nr_instructions = fix.vm.stats.instrs;
        write!(
            self.csv,
            "{}, {}, {}, {}, {}, {}\n",
            self.iteration,
            nr_instructions - self.nr_instructions,
            stats.nr_read,
            stats.nr_intent,
            stats.nr_upgrade,
            stats.nr_write
        )?;
        self.baseline = new_stats;
        self.iteration += 1;
        self.nr_instructions = nr_instructions;
        Ok(())
    }
}

//-------------------------------

pub struct ValueType<G: Guest> {
    pub size: usize,
    pub inc_fn: Addr,
    pub dec_fn: Addr,
    pub eq_fn: Addr,
    pub rust_value_type: PhantomData<G>,
}

impl<G: Guest> ValueType<G> {
    fn new(size: usize, inc_fn: Addr, dec_fn: Addr, eq_fn: Addr) -> Self {
        ValueType {
            size,
            inc_fn,
            dec_fn,
            eq_fn,
            rust_value_type: PhantomData,
        }
    }
}

impl<G: Guest> Guest for ValueType<G> {
    fn guest_len() -> usize {
        // 3 functions ptrs and a u32 + 4 padding
        32
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.inc_fn.0)?;
        w.write_u64::<LittleEndian>(self.dec_fn.0)?;
        w.write_u64::<LittleEndian>(self.eq_fn.0)?;
        w.write_u32::<LittleEndian>(G::guest_len() as u32)?;
        w.write_u32::<LittleEndian>(0)?; // padding
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let inc_fn = Addr(r.read_u64::<LittleEndian>()?);
        let dec_fn = Addr(r.read_u64::<LittleEndian>()?);
        let eq_fn = Addr(r.read_u64::<LittleEndian>()?);
        let size = r.read_u32::<LittleEndian>()? as usize;
        let _padding = r.read_u32::<LittleEndian>()?;

        assert!(size == G::guest_len());

        Ok(ValueType {
            inc_fn,
            dec_fn,
            eq_fn,
            size,
            rust_value_type: PhantomData,
        })
    }
}

pub struct BTree<G: Guest> {
    pub vt: ValueType<G>,
    pub vt_context: Addr,
    pub tm: Addr,
    pub root: u64,
}

impl<G: Guest> Guest for BTree<G> {
    fn guest_len() -> usize {
        32
    }

    fn pack<W: Write>(&self, w: &mut W, ptr: Addr) -> io::Result<()> {
        self.vt.pack(w, ptr)?;
        w.write_u64::<LittleEndian>(self.vt_context.0)?;
        w.write_u64::<LittleEndian>(self.tm.0)?;
        w.write_u64::<LittleEndian>(self.root)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, ptr: Addr) -> io::Result<Self> {
        let vt = ValueType::unpack(r, ptr)?;
        let vt_context = Addr(r.read_u64::<LittleEndian>()?);
        let tm = Addr(r.read_u64::<LittleEndian>()?);
        let root = r.read_u64::<LittleEndian>()?;

        Ok(BTree {
            vt,
            vt_context,
            tm,
            root,
        })
    }
}

fn btree_new(fix: &mut Fixture, btree: Addr, vt: Addr, vt_context: Addr, tm: Addr) -> Result<()> {
    fix.vm.set_reg(A0, btree.0);
    fix.vm.set_reg(A1, vt.0);
    fix.vm.set_reg(A2, vt_context.0);
    fix.vm.set_reg(A3, tm.0);
    fix.call_with_errno("btree_new")?;
    Ok(())
}

fn btree_lookup<G: Guest>(fix: &mut Fixture, btree: Addr, key: u64) -> Result<Option<G>> {
    let (mut fix, result_ptr) = auto_alloc(fix, 8)?;

    fix.vm.set_reg(A0, btree.0);
    fix.vm.set_reg(A1, key);
    fix.vm.set_reg(A2, result_ptr.0);

    fix.call("btree_lookup")?;

    let r = fix.vm.reg(A0) as i32;
    if r == 0 {
        let value = read_guest(&fix.vm.mem, result_ptr)?;
        Ok(Some(value))
    } else if r == -ENODATA {
        Ok(None)
    } else if r < 0 {
        Err(anyhow!("failed: {}", error_string(-r)))
    } else {
        Err(anyhow!("failed: {}", r))
    }
}

fn btree_insert<G: Guest>(fix: &mut Fixture, btree: Addr, key: u64, value: &G) -> Result<()> {
    let (mut fix, value_ptr) = auto_guest(fix, value, PERM_READ | PERM_WRITE)?;
    fix.vm.set_reg(A0, btree.0);
    fix.vm.set_reg(A1, key);
    fix.vm.set_reg(A2, value_ptr.0);
    fix.call_with_errno("btree_insert")?;
    Ok(())
}

fn btree_to_engine(fix: &mut Fixture, btree: Addr) -> Result<Addr> {
    fix.vm.set_reg(A0, btree.0);
    fix.call("btree_to_engine")?;
    Ok(Addr(fix.vm.reg(A0)))
}

fn btree_root(fix: &mut Fixture, btree: Addr) -> Result<u64> {
    fix.vm.set_reg(A0, btree.0);
    fix.call("btree_root")?;
    Ok(fix.vm.reg(A0))
}

//-------------------------------

#[allow(dead_code)]
struct Header {
    blocknr: u64,
    is_leaf: bool,
    nr_entries: usize,
    value_size: usize,
}

// const INTERNAL_NODE: u32 = 1;
const LEAF_NODE: u32 = 2;

impl Unpack for Header {
    fn disk_size() -> u32 {
        24
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Header> {
        let (i, _csum) = le_u32(data)?;
        let (i, flags) = le_u32(i)?;
        let (i, blocknr) = le_u64(i)?;
        let (i, _purpose) = le_u32(i)?;
        let (i, nr_entries) = le_u16(i)?;
        let (i, value_size) = le_u16(i)?;

        Ok((
            i,
            Header {
                blocknr,
                is_leaf: flags == LEAF_NODE,
                nr_entries: nr_entries as usize,
                value_size: value_size as usize,
            },
        ))
    }
}

fn unpack_header(data: &[u8]) -> Result<Header> {
    let (_, hdr) = Header::unpack(data).map_err(|_e| anyhow!("couldn't unpack Header"))?;
    Ok(hdr)
}

enum Node<V: Unpack> {
    Internal {
        header: Header,
        keys: Vec<u64>,
        values: Vec<u64>,
    },
    Leaf {
        header: Header,
        keys: Vec<u64>,
        values: Vec<V>,
    },
}

fn internal_max_entries() -> usize {
    (MD_BLOCK_SIZE - Header::disk_size() as usize) / (2 * u64::disk_size() as usize)
}

fn leaf_max_entries<V: Unpack>() -> usize {
    (MD_BLOCK_SIZE - Header::disk_size() as usize)
        / (u64::disk_size() as usize + V::disk_size() as usize)
}

pub fn convert_result<'a, V>(r: IResult<&'a [u8], V>) -> Result<(&'a [u8], V)> {
    r.map_err(|_e| anyhow!("parse error"))
}

fn unpack_node<V: Unpack>(data: &[u8]) -> Result<Node<V>> {
    use nom::multi::count;

    let (i, hdr) = Header::unpack(data).map_err(|_e| anyhow!("couldn't unpack header"))?;

    if hdr.is_leaf && hdr.value_size != V::disk_size() as usize {
        return Err(anyhow!("bad value_size"));
    }

    let (i, keys) = convert_result(count(le_u64, hdr.nr_entries as usize)(i))?;
    let mut last = None;
    for k in &keys {
        if let Some(l) = last {
            if k <= l {
                return Err(anyhow!("keys out of order"));
            }
        }

        last = Some(k);
    }

    // skip the unused keys
    let max_entries = if hdr.is_leaf {
        leaf_max_entries::<V>()
    } else {
        internal_max_entries()
    };

    let remaining = max_entries - hdr.nr_entries;
    let (i, keys) = convert_result(count(le_u64, remaining)(i))?;

    if hdr.is_leaf {
        let (_i, values) = convert_result(count(V::unpack, hdr.nr_entries as usize)(i))?;

        Ok(Node::Leaf {
            header: hdr,
            keys,
            values,
        })
    } else {
        let (_i, values) = convert_result(count(le_u64, hdr.nr_entries as usize)(i))?;
        Ok(Node::Internal {
            header: hdr,
            keys,
            values,
        })
    }
}

fn check_node<V: Unpack>(
    engine: &FakeIoEngine,
    loc: u64,
    mut highest_key: Option<u64>,
) -> Result<Option<u64>> {
    let data = engine.data.get(&loc).unwrap();

    let mut zeroes = true;
    for b in data {
        if *b != 0 {
            zeroes = false;
        }
    }
    ensure!(!zeroes);

    let node = unpack_node::<V>(data)?;

    match node {
        Node::Internal { values, header, .. } => {
            /*
            debug!(
                "checking internal node at {}, nr_entries = {}, values {:?}",
                loc, header.nr_entries, values
            );
            */
            for v in values {
                highest_key = check_node::<V>(engine, v, highest_key)?;
            }
        }
        Node::Leaf { keys, .. } => {
            // debug!("checking leaf node at {}", loc);
            if let Some(hkey) = highest_key {
                if keys.len() > 0 {
                    ensure!(keys[0] > hkey);
                    highest_key = Some(keys[keys.len() - 1]);
                }
            }
        }
    }

    Ok(highest_key)
}

fn check_btree<V: Unpack>(fix: &mut Fixture, btree_ptr: Addr) -> Result<()> {
    let io_ptr = btree_to_engine(fix, btree_ptr)?;
    let root = btree_root(fix, btree_ptr)?;
    let engine = fix
        .contexts
        .get::<Arc<Mutex<FakeIoEngine>>>(&io_ptr)
        .unwrap()
        .clone();
    let engine = engine.lock().unwrap();

    check_node::<V>(&*engine, root, None);
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

fn test_sm_freed_blocks_can_not_be_allocated(fix: &mut Fixture) -> Result<()> {
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

    // We should still have no free blocks
    ensure!(sm_nr_free(&mut *fix, sm_ptr)? == 0);

    // new will fail
    ensure!(sm_new(&mut *fix, sm_ptr)?.is_none());

    sm_exit(&mut *fix, sm_ptr)?;
    Ok(())
}

fn test_sm_freed_blocks_can_be_allocated_after_commit(fix: &mut Fixture) -> Result<()> {
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

//-------------------------------

fn test_tm_init(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let bdev = mk_block_device(&mut fix.vm.mem, 0, 1024 * 8)?;
    let (mut fix, tm_ptr) = auto_tm(&mut *fix, bdev, 32)?;
    tm_exit(&mut *fix, tm_ptr)?;
    Ok(())
}

fn test_tm_new(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let nr_blocks = 128;
    let bdev = mk_block_device(&mut fix.vm.mem, 0, nr_blocks * 8)?;
    let (mut fix, tm_ptr) = auto_tm(&mut *fix, bdev, 32)?;

    for _i in 0..nr_blocks {
        let b = tm_new(&mut *fix, tm_ptr)?;
        ensure!(b.is_some());
    }

    ensure!(tm_new(&mut *fix, tm_ptr)?.is_none());

    tm_exit(&mut *fix, tm_ptr)?;
    Ok(())
}

fn test_tm_get(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    stub_io_engine(fix)?;

    let nr_blocks = 128;
    let bdev = mk_block_device(&mut fix.vm.mem, 0, nr_blocks * 8)?;
    let (mut fix, tm_ptr) = auto_tm(&mut *fix, bdev, 32)?;

    let b = tm_new(&mut *fix, tm_ptr)?.unwrap();

    let buf_ptr = tm_get(&mut *fix, tm_ptr, b, RIWType::RIWRead)?;
    debug!("buf_ptr = {:?}", buf_ptr);
    tm_exit(&mut *fix, tm_ptr)?;
    Ok(())
}

//-------------------------------

fn trace_things(fix: &mut Fixture) -> Result<()> {
    /*
    fix.trace_func("tm_shadow")?;
    fix.trace_func("ss_get")?;
    fix.trace_func("tm_get")?;
    */
    fix.trace_func("btree_lookup")?;
    fix.trace_func("btree_insert")?;
    fix.trace_func("insert_")?;
    /*
    fix.trace_func("riw_down_read")?;
    fix.trace_func("riw_down_intent")?;
    fix.trace_func("riw_down_write")?;
    fix.trace_func("riw_up_read")?;
    fix.trace_func("riw_up_intent")?;
    fix.trace_func("riw_up_write")?;
    fix.trace_func("riw_upgrade")?;
    */

    fix.trace_func("split_beneath")?;
    fix.trace_func("rebalance_or_split")?;
    fix.trace_func("rebalance_left")?;
    fix.trace_func("rebalance_right")?;
    fix.trace_func("split_one_into_two")?;
    fix.trace_func("split_two_into_three")?;
    fix.trace_func("get_node_free_space")?;
    Ok(())
}

fn test_btree_new(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    stub_io_engine(fix)?;
    trace_things(fix)?;

    let nr_blocks = 128;
    let bdev = mk_block_device(&mut fix.vm.mem, 0, nr_blocks * 8)?;
    let (mut fix, tm_ptr) = auto_tm(&mut *fix, bdev, 8)?;

    let vt = ValueType::<u64>::new(8, Addr(0), Addr(0), Addr(0));

    let (mut fix, vt_ptr) = auto_guest(&mut *fix, &vt, PERM_READ | PERM_WRITE)?;
    let (mut fix, btree_ptr) = auto_alloc(&mut *fix, BTree::<u64>::guest_len())?;
    let vt_context = Addr(0);
    btree_new(&mut *fix, btree_ptr, vt_ptr, vt_context, tm_ptr)?;
    Ok(())
}

fn test_btree_insert(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    riw_globals(fix)?;
    stub_io_engine(fix)?;
    // trace_things(fix)?;

    let nr_blocks = 1024;
    let bdev = mk_block_device(&mut fix.vm.mem, 0, nr_blocks * 8)?;

    // FIXME: reduce nr_buffers
    let (mut fix, tm_ptr) = auto_tm(&mut *fix, bdev, nr_blocks)?;

    let vt = ValueType::<u64>::new(8, Addr(0), Addr(0), Addr(0));

    let (mut fix, vt_ptr) = auto_guest(&mut *fix, &vt, PERM_READ | PERM_WRITE)?;
    let (mut fix, btree_ptr) = auto_alloc(&mut *fix, BTree::<u64>::guest_len())?;
    let vt_context = Addr(0);
    btree_new(&mut *fix, btree_ptr, vt_ptr, vt_context, tm_ptr)?;

    let mut tracker = StatsTracker::new("thin2-btree-insert.csv", tm_ptr)?;

    let commit_interval = 1;
    let count = 20000u64;
    let mut commit_counter = commit_interval;
    for i in 0..count {
        btree_insert(&mut *fix, btree_ptr, i, &i)?;
        tracker.checkpoint(&mut *fix)?;

        if commit_counter == 0 {
            tm_commit(&mut *fix, tm_ptr, Addr(0))?;
            check_no_pending_io(&mut *fix, btree_ptr)?;
            check_btree::<u64>(&mut *fix, btree_ptr)?;
            commit_counter = commit_interval;
        } else {
            commit_counter -= 1;
        }
    }

    if commit_counter != commit_interval {
        tm_commit(&mut *fix, tm_ptr, Addr(0))?;
        check_btree::<u64>(&mut *fix, btree_ptr)?;
        check_no_pending_io(&mut *fix, btree_ptr)?;
    }

    for i in 0..count {
        let v = btree_lookup::<u64>(&mut *fix, btree_ptr, i)?.unwrap();
        debug!("v = {}", v);
        ensure!(v == i);
    }

    Ok(())
}

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
            test!("freed-blocks-can-not-be-allocated", test_sm_freed_blocks_can_not_be_allocated)
            test!("freed-blocks-can-be-allocated-after-commit", test_sm_freed_blocks_can_be_allocated_after_commit)
        }

        test_section! {
            "transaction-manager/",
            test!("init", test_tm_init)
            test!("new", test_tm_new)
            test!("get", test_tm_get)
        }

        test_section! {
            "btree/",
            test!("new", test_btree_new)
            test!("insert", test_btree_insert)
        }
    }

    Ok(())
}

//-------------------------------
