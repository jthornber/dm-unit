use anyhow::{ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use rand::prelude::*;
use rand::SeedableRng;
use std::io::{self, Read, Write};

use crate::decode::*;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::block_device::*;
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

struct Waiter {}

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

        // FIXME: write the waiters
        w.write_u64::<LittleEndian>(0)?;
        w.write_u64::<LittleEndian>(0)?;

        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let locked = unpack_bool(r.read_u8()? as u8);
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

//-------------------------------

fn auto_riw<'a>(fix: &'a mut Fixture, riw: &RIWLock) -> Result<(AutoGPtr<'a>, Addr)> {
    auto_guest(fix, riw, PERM_READ | PERM_WRITE)
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

//-------------------------------

fn test_riw_init(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let riw = riw_init(fix)?;
    ensure!(!riw.locked);
    ensure!(!riw.intent);
    ensure!(riw.count == 0);
    ensure!(riw.waiters.len() == 0);

    Ok(())
}

fn test_riw_down_read_unlocked(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let _ = fix.stub("get_current_", 0)?;
    let _ = fix.stub("put_current_", 0)?;

    let riw = riw_init(fix)?;
    let riw = riw_down_read(fix, &riw)?;

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![THIN2_MOD];
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
        "/thinp2/riw/",
        test!("init", test_riw_init)
        test!("down-read-unlocked", test_riw_down_read_unlocked)
    }

    Ok(())
}

//-------------------------------
