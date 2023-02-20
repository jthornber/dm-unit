use crate::emulator::memory::*;
use crate::fixture::*;
use crate::guest::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::bufio::*;

use anyhow::{anyhow, Result};
use log::*;
use std::collections::BTreeSet;

//-------------------------------

fn auto_lru<'a>(fix: &'a mut Fixture) -> Result<(AutoGPtr<'a>, Addr)> {
    let lru = Lru {
        cursor: Addr(0),
        count: 0,
    };
    let ptr = alloc_guest(&mut fix.vm.mem, &lru, PERM_READ | PERM_WRITE)?;
    Ok((AutoGPtr::new(fix, ptr), ptr))
}

// The lru entry is the first field of buffers.  Let's put
// this assumption in a single place.
fn entry_to_buf(e: Addr) -> Addr {
    e
}

// Ditto
fn list_to_entry(l: Addr) -> Addr {
    l
}

fn lru_read_buffers(fix: &mut Fixture, lru: Addr) -> Result<Vec<Buffer>> {
    let mut bufs = Vec::new();

    let lru = read_guest::<Lru>(&fix.vm.mem, lru)?;
    let mut cursor = lru.cursor;

    if cursor.0 != 0 {
        let first = cursor;

        loop {
            let buf_addr = entry_to_buf(list_to_entry(cursor));
            let buf = read_guest::<Buffer>(&fix.vm.mem, buf_addr)?;
            cursor = buf.lru.list.next;
            bufs.push(buf);

            if cursor == first {
                break;
            }
        }
    }

    Ok(bufs)
}

fn test_lru_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, lru) = auto_lru(fix)?;
    lru_exit(&mut fix, lru)?;
    Ok(())
}

fn test_lru_inserts(fix: &mut Fixture, blocks: &[u64]) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, lru) = auto_lru(fix)?;

    let bufs: Vec<Buffer> = blocks
        .iter()
        .map({
            |b| Buffer {
                lru: LruEntry::default(),
                block: *b,
                hold_count: 0,
                last_accessed: 0,
                list_mode: LruKind::Clean,
            }
        })
        .collect();

    let (mut fix, guest_bufs) = auto_alloc_vec(&mut fix, &bufs)?;
    for b in &guest_bufs {
        lru_insert(&mut fix, lru, *b)?;
    }

    let count = lru_count(&mut fix, lru)?;

    if count != blocks.len() as u64 {
        return Err(anyhow!(
            "lru counts not correct, actual {}, expected {}",
            count,
            blocks.len()
        ));
    }

    let bufs = lru_read_buffers(&mut fix, lru)?;
    if bufs.len() != blocks.len() {
        return Err(anyhow!("too few buffers"));
    }

    for (i, b) in blocks.iter().enumerate() {
        if bufs[i].block != *b {
            return Err(anyhow!("incorrect block nr"));
        }
    }

    Ok(())
}

fn test_lru_insert_1(fix: &mut Fixture) -> Result<()> {
    test_lru_inserts(fix, &[1234])
}

fn test_lru_insert_many(fix: &mut Fixture) -> Result<()> {
    let blocks: Vec<u64> = (0..1024).into_iter().collect();
    test_lru_inserts(fix, &blocks)
}

fn seq_buffers(b: usize, e: usize) -> Vec<Buffer> {
    (b..e)
        .into_iter()
        .map({
            |b| Buffer {
                lru: LruEntry::default(),
                block: b as u64,
                hold_count: 0,
                last_accessed: 0,
                list_mode: LruKind::Clean,
            }
        })
        .collect()
}

fn test_lru_evict(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, lru) = auto_lru(fix)?;

    let bufs = seq_buffers(0, 1024);
    let (mut fix, guest_bufs) = auto_alloc_vec(&mut fix, &bufs)?;
    for b in &guest_bufs {
        lru_insert(&mut fix, lru, *b)?;
    }

    // reference every other block
    for (i, b) in guest_bufs.iter().enumerate() {
        if i % 2 == 0 {
            lru_reference(&mut fix, *b)?;
        }
    }

    let pred = (&mut fix).const_callback(0)?; // ER_EVICT

    // evict half the buffers, and check they aren't the
    // ones that were referenced.
    for _ in 0..(bufs.len() / 2) {
        let b_ptr = lru_evict(&mut fix, lru, pred, Addr(0))?;
        if b_ptr == Addr(0) {
            return Err(anyhow!("evict failed"));
        }

        let buf = read_guest::<Buffer>(&fix.vm.mem, b_ptr)?;
        if buf.block % 2 != 1 {
            return Err(anyhow!(
                "unexpected block chosen for eviction {}",
                buf.block
            ));
        }
    }

    // Insert another batch
    let bufs2 = seq_buffers(1024, 2048);
    let (mut fix, guest_bufs2) = auto_alloc_vec(&mut fix, &bufs2)?;
    for b in &guest_bufs2 {
        lru_insert(&mut fix, lru, *b)?;
    }

    // Reference the older buffers
    for (i, b) in guest_bufs.iter().enumerate() {
        if i % 2 == 0 {
            lru_reference(&mut fix, *b)?;
        }
    }

    // Evict the second batch
    for _ in 0..bufs2.len() {
        let b_ptr = lru_evict(&mut fix, lru, pred, Addr(0))?;
        if b_ptr == Addr(0) {
            return Err(anyhow!("evict failed"));
        }

        let buf = read_guest::<Buffer>(&fix.vm.mem, b_ptr)?;
        if buf.block < 1024 {
            return Err(anyhow!(
                "unexpected block chosen for eviction {}",
                buf.block
            ));
        }
    }

    fix.trace_func("lru_insert")?;
    fix.trace_func("lru_evict")?;

    // Reinsert the second batch
    for b in &guest_bufs2 {
        lru_insert(&mut fix, lru, *b)?;
    }

    // evict the remains of the original batch.
    for _ in 0..(bufs.len() / 2) {
        let b_ptr = lru_evict(&mut fix, lru, pred, Addr(0))?;
        if b_ptr == Addr(0) {
            return Err(anyhow!("evict failed"));
        }

        let buf = read_guest::<Buffer>(&fix.vm.mem, b_ptr)?;
        if buf.block >= 1024 {
            return Err(anyhow!(
                "unexpected block chosen for eviction {}",
                buf.block
            ));
        }
    }

    Ok(())
}

//-------------------------------

fn auto_cache<'a>(fix: &'a mut Fixture) -> Result<(AutoGPtr<'a>, Addr)> {
    auto_alloc(fix, BUFFER_CACHE_SIZE)
}

fn test_cache_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, cache) = auto_cache(fix)?;
    cache_exit(&mut fix, cache)?;

    Ok(())
}

fn test_cache_insert(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, cache) = auto_cache(fix)?;

    // Insert a bunch of buffers
    let bufs = seq_buffers(0, 1024);
    let (mut fix, guest_bufs) = auto_alloc_vec(&mut fix, &bufs)?;
    for b in &guest_bufs {
        cache_insert(&mut fix, cache, *b)?;
    }

    // Remove them all
    for (i, b) in bufs.iter().enumerate() {
        let b2 = cache_get(&mut fix, cache, b.block)?;
        if guest_bufs[i] != b2 {
            return Err(anyhow!("block mismatch"));
        }
        cache_remove(&mut fix, cache, b2)?;
    }

    cache_exit(&mut fix, cache)?;

    Ok(())
}

fn test_cache_mark(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let (mut fix, cache) = auto_cache(fix)?;

    // Insert a bunch of buffers
    let bufs = seq_buffers(0, 1024);
    let (mut fix, guest_bufs) = auto_alloc_vec(&mut fix, &bufs)?;
    for b in &guest_bufs {
        cache_insert(&mut fix, cache, *b)?;
    }

    // Mark half as dirty
    let mut dirty: BTreeSet<Addr> = BTreeSet::new();
    for b in &bufs {
        if b.block % 2 == 0 {
            continue;
        }

        let b2 = cache_get(&mut fix, cache, b.block)?;
        cache_mark(&mut fix, cache, b2, LruKind::Dirty)?;
        cache_put(&mut fix, cache, b2)?;
        dirty.insert(b2);
    }

    // check they are indeed dirty
    let mut dirty2 = BTreeSet::new();
    loop {
        let pred = (&mut fix).const_callback(0)?; // ER_EVICT
        let b = cache_evict(&mut fix, cache, LruKind::Dirty, pred, Addr(0))?;
        if b.0 == 0 {
            break;
        }

        dirty2.insert(b);
    }

    if dirty != dirty2 {
        return Err(anyhow!("missing dirty buffer"));
    }

    // Remove them all, this time using remove_range
    let pred = (&mut fix).const_callback(0)?; // ER_EVICT
    let release = (&mut fix).const_callback(0)?;
    cache_remove_range(&mut fix, cache, 0, 1024, pred, release)?;

    cache_exit(&mut fix, cache)?;

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
        test!("insert-1", test_lru_insert_1)
        test!("insert-many", test_lru_insert_many)
        test!("evict", test_lru_evict)
    };

    test_section! {
        "/bufio/cache/",
        test!("create", test_cache_create)
        test!("insert", test_cache_insert)
        test!("mark", test_cache_mark)
    };

    Ok(())
}

//-------------------------------
