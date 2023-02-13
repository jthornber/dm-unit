use crate::emulator::memory::*;
use crate::emulator::riscv::*;
use crate::fixture::*;
use crate::guest::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::bufio::*;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};

use Reg::*;

//-------------------------------

// What can we actually test, given so much of bufio
// is about concurrency and IO.
// FIXME: move to test file
// A cut down buffer used for testing the LRU in isolation.
struct MiniBuffer {
    lru: LruEntry,
    block: u64,
    last_accessed: u64,
}

impl Guest for MiniBuffer {
    fn guest_len() -> usize {
        32
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        self.lru.pack(w)?;
        w.write_u64::<LittleEndian>(self.block)?;
        w.write_u64::<LittleEndian>(self.last_accessed)?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let lru = LruEntry::unpack(r)?;
        let block = r.read_u64::<LittleEndian>()?;
        let last_accessed = r.read_u64::<LittleEndian>()?;
        Ok(Self {
            lru,
            block,
            last_accessed,
        })
    }
}

//-------------------------------

pub fn auto_lru<'a>(fix: &'a mut Fixture) -> Result<(AutoGPtr<'a>, Addr)> {
    let lru = Lru {
        cursor: Addr(0),
        count: 0,
    };
    let ptr = alloc_guest(&mut fix.vm.mem, &lru, PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

fn test_lru_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, lru) = auto_lru(fix)?;
    lru_exit(&mut fix, lru)?;
    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![BUFIO_MOD];
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
        "/bufio/lru/",
        test!("create", test_lru_create)
    };

    Ok(())
}

//-------------------------------
