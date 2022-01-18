use anyhow::{anyhow, ensure, Context, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use crossbeam::thread;
use crossbeam::utils::CachePadded;
use log::*;
use nom::{number::complete::*, IResult};
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::io::{Cursor, Read, Write};
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use thinp::checksum;
use thinp::io_engine::{IoEngine, BLOCK_SIZE};
use thinp::pdata::btree;
use thinp::pdata::btree::*;
use thinp::pdata::btree_builder::*;
use thinp::pdata::btree_walker::*;
use thinp::pdata::unpack::*;
use threadpool::ThreadPool; // FIXME: remove

use crate::block_manager::*;
use crate::emulator::memory::*;
use crate::fixture::*;
use crate::guest::*;
use crate::stats::*;
use crate::stubs::block_manager::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::btree::*;
use crate::wrappers::transaction_manager::*;

//-------------------------------

struct NoopVisitor {}

impl<V: Unpack> NodeVisitor<V> for NoopVisitor {
    fn visit(
        &self,
        _path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        _keys: &[u64],
        _values: &[V],
    ) -> btree::Result<()> {
        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

/*
#[allow(dead_code)]
fn check_btree(root: u64) -> Result<()>? {
    let walker = BTreeWalker::new(get_bm()?, false);
    let visitor = NoopVisitor {};
    let mut path = Vec::new();

    walker.walk::<NoopVisitor, Value64>(&mut path, &visitor, root)?;

    Ok(())
}
*/

//-------------------------------

struct ResidencyVisitor {
    nr_entries: AtomicU32,
    nr_leaves: AtomicU32,
}

impl<V: Unpack> NodeVisitor<V> for ResidencyVisitor {
    fn visit(
        &self,
        _path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        keys: &[u64],
        _values: &[V],
    ) -> btree::Result<()> {
        self.nr_entries
            .fetch_add(keys.len() as u32, Ordering::SeqCst);
        self.nr_leaves.fetch_add(1, Ordering::SeqCst);
        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

// Because this is a walk it implicitly checks the btree.  Returns
// average residency as a _percentage_.
pub fn calc_residency<V: Unpack>(bm: &Arc<BlockManager>, root: u64) -> Result<usize> {
    let walker = BTreeWalker::new(bm.clone(), false);
    let visitor = ResidencyVisitor {
        nr_entries: AtomicU32::new(0),
        nr_leaves: AtomicU32::new(0),
    };
    let mut path = Vec::new();

    walker.walk::<ResidencyVisitor, V>(&mut path, &visitor, root)?;

    let nr_entries = visitor.nr_entries.load(Ordering::SeqCst) as usize;
    let nr_leaves = visitor.nr_leaves.load(Ordering::SeqCst) as usize;
    debug!("nr_leaves = {}, nr_entries = {}", nr_leaves, nr_entries);
    let max_entries = calc_max_entries::<V>();

    let percent = (nr_entries * 100) / (max_entries * nr_leaves);

    Ok(percent)
}

//-------------------------------

#[derive(Debug, Default)]
struct NodeInfo {
    internal_nodes: BTreeMap<u64, KeyRange>,
    leaf_nodes: BTreeMap<u64, KeyRange>,
}

struct NodeDiscovery {
    engine: Arc<dyn IoEngine + Send + Sync>,
    info: NodeInfo,
}

impl NodeDiscovery {
    fn new(engine: Arc<dyn IoEngine + Send + Sync>) -> Self {
        NodeDiscovery {
            engine,
            info: NodeInfo::default(),
        }
    }

    fn walk_node<V: Unpack>(&mut self, kr: &KeyRange, loc: u64, is_root: bool) -> Result<()> {
        let b = self.engine.read(loc)?;
        let bt = checksum::metadata_block_type(b.get_data());
        if bt != checksum::BT::NODE {
            return Err(anyhow!("bad checksum"));
        }

        let path = vec![];
        let node = unpack_node::<V>(&path, &b.get_data(), false, is_root)?;

        match node {
            Node::Internal { keys, values, .. } => {
                let krs = split_key_ranges(&path, kr, &keys)?;
                self.info.internal_nodes.insert(loc, kr.clone());

                for (i, v) in values.iter().enumerate() {
                    self.walk_node::<V>(&krs[i], *v, false)?;
                }
                Ok(())
            }
            Node::Leaf { .. } => {
                self.info.leaf_nodes.insert(loc, kr.clone());
                Ok(())
            }
        }
    }
}

fn discover_nodes<V: Unpack>(
    engine: Arc<dyn IoEngine + Send + Sync>,
    root: u64,
) -> Result<NodeInfo> {
    let mut nd = NodeDiscovery::new(engine);
    let kr = KeyRange {
        start: None,
        end: None,
    };
    nd.walk_node::<V>(&kr, root, true)?;
    Ok(nd.info)
}

//-------------------------------

// Used to confirm all expected keys are present in the tree.
struct EntryVisitor {
    seen: Mutex<BTreeSet<u64>>,
}

fn key_to_value(k: u64) -> u64 {
    k + 12345
}

impl NodeVisitor<Value64> for EntryVisitor {
    fn visit(
        &self,
        _path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        keys: &[u64],
        values: &[Value64],
    ) -> btree::Result<()> {
        for (i, k) in keys.iter().enumerate() {
            let v = values[i];
            if v.0 != key_to_value(*k) {
                return Err(BTreeError::ValueError(format!(
                    "Key has bad value: {} -> {}",
                    k, v.0
                )));
            }

            let mut seen = self.seen.lock().unwrap();
            seen.insert(*k);
        }

        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

fn check_keys_present(bm: &Arc<BlockManager>, root: u64, keys: &[u64]) -> Result<()> {
    let walker = BTreeWalker::new(bm.clone(), false);
    let visitor = EntryVisitor {
        seen: Mutex::new(BTreeSet::new()),
    };

    let mut path = Vec::new();
    walker.walk::<EntryVisitor, Value64>(&mut path, &visitor, root)?;

    let seen = visitor.seen.lock().unwrap();
    for k in keys {
        if !seen.contains(k) {
            return Err(anyhow!("Key missing from btree: {}", *k));
        }
    }

    Ok(())
}

//-------------------------------

/// A little wrapper to let us store u64's in btrees.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Value64(u64);

impl Guest for Value64 {
    fn guest_len() -> usize {
        8
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.0)
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let v = r.read_u64::<LittleEndian>()?;
        Ok(Value64(v))
    }
}

impl Unpack for Value64 {
    fn disk_size() -> u32 {
        8
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Self> {
        let (i, v) = le_u64(data)?;
        Ok((i, Value64(v)))
    }
}

impl Pack for Value64 {
    fn pack<W: WriteBytesExt>(&self, w: &mut W) -> Result<()> {
        w.write_u64::<LittleEndian>(self.0)?;
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Value32(u32);

impl Unpack for Value32 {
    fn disk_size() -> u32 {
        4
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Self> {
        let (i, v) = le_u32(data)?;
        Ok((i, Value32(v)))
    }
}

impl Pack for Value32 {
    fn pack<W: WriteBytesExt>(&self, w: &mut W) -> Result<()> {
        w.write_u32::<LittleEndian>(self.0)?;
        Ok(())
    }
}

#[allow(dead_code)]
fn enable_traces(fix: &mut Fixture) -> Result<()> {
    let traces = [
        "btree_insert_raw",
        "dm_btree_cursor_begin",
        "dm_btree_cursor_end",
        "dm_btree_cursor_get_value",
        "dm_btree_cursor_next",
        "dm_btree_cursor_skip",
        "dm_btree_del",
        "dm_btree_empty",
        "dm_btree_find_highest_key",
        "dm_btree_find_lowest_key",
        "dm_btree_insert",
        "dm_btree_insert_notify",
        "dm_btree_lookup",
        "dm_btree_lookup_next",
        "dm_btree_lookup_next_single",
        "dm_btree_remove",
        "dm_btree_remove_leaves",
        "dm_btree_walk",
        "dm_sm_metadata_create",
        "dm_tm_create",
        "dm_tm_create_with_sm",
        "dm_tm_new_block",
        "dm_tm_unlock",
        "insert",
        "insert_at",
        "lower_bound",
        "metadata_ll_init_index",
        "shadow_current",
        "shadow_step",
        "sm_bootstrap_new_block",
        "sm_bootstrap_new_block",
        "sm_ll_extend",
        "sm_ll_init",
        "sm_ll_new_metadata",
    ];
    for t in &traces {
        fix.trace_func(t)?;
    }
    Ok(())
}

//-------------------------------

// Delete an empty tree.
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let bm = dm_bm_create(fix, 1024)?;
    let (tm, _sm) = dm_tm_create(fix, bm, 0)?;

    let vtype: BTreeValueType<Value64> = BTreeValueType {
        context: Addr(0),
        inc_fn: Addr(0),
        dec_fn: Addr(0),
        eq_fn: Addr(0),
        rust_value_type: PhantomData,
    };
    let info = BTreeInfo {
        tm,
        levels: 1,
        vtype,
    };

    let root = dm_btree_empty(fix, &info)?;
    dm_btree_del(fix, &info, root)?;
    Ok(())
}

#[allow(dead_code)]
#[derive(Clone)]
struct BTreeTest {
    bm: Addr,
    tm: Addr,
    sm: Addr,
    sb: Option<Addr>,
    info: BTreeInfo<Value64>,
    root: u64,
    baseline: Stats,
}

impl BTreeTest {
    fn new(fix: &mut Fixture) -> Result<Self> {
        let bm = dm_bm_create(fix, 1024)?;
        let (tm, sm) = dm_tm_create(fix, bm, 0)?;

        // FIXME: we should increment the superblock within the sm

        let vtype: BTreeValueType<Value64> = BTreeValueType {
            context: Addr(0),
            inc_fn: Addr(0),
            dec_fn: Addr(0),
            eq_fn: Addr(0),
            rust_value_type: PhantomData,
        };
        let info = BTreeInfo {
            tm,
            levels: 1,
            vtype,
        };
        let root = dm_btree_empty(fix, &info)?;
        let baseline = {
            let bm = get_bm(fix, bm);
            Stats::collect_stats(fix, &bm)
        };

        Ok(BTreeTest {
            bm,
            tm,
            sm,
            sb: None,
            info,
            root,
            baseline,
        })
    }

    fn begin(&mut self, fix: &mut Fixture) -> Result<()> {
        if self.sb.is_some() {
            return Err(anyhow!("transaction already begun"));
        }

        self.sb = Some(dm_bm_write_lock_zero(fix, self.bm, 0, Addr(0))?);
        Ok(())
    }

    fn insert(&mut self, fix: &mut Fixture, key: u64) -> Result<()> {
        let ks = vec![key];
        let v = Value64(key_to_value(key));
        self.root = dm_btree_insert(fix, &self.info, self.root, &ks, &v)?;
        Ok(())
    }

    // We call this when fuzzing, it's fine for the dm_btree_insert
    // call to fail.  So we don't return an error in this case.  But we
    // do propogate any failure from the vm itself, such as an invalid
    // memory access.
    fn insert_fuzz(&mut self, fix: &mut Fixture, key: u64) -> Result<()> {
        let ks = vec![key];
        let v = Value64(key_to_value(key));
        let (errno, mroot) = dm_btree_insert_with_errno(fix, &self.info, self.root, &ks, &v)?;
        if let Some(root) = mroot {
            self.root = root;
        }
        Ok(())
    }

    fn remove(&mut self, fix: &mut Fixture, key: u64) -> Result<()> {
        let ks = vec![key];
        let v = Value64(key_to_value(key));
        self.root = dm_btree_remove(fix, &self.info, self.root, &ks)?;
        Ok(())
    }

    fn remove_fuzz(&mut self, fix: &mut Fixture, key: u64) -> Result<()> {
        let ks = vec![key];
        let v = Value64(key_to_value(key));
        let (errno, mroot) = dm_btree_remove_with_errno(fix, &self.info, self.root, &ks)?;
        if let Some(root) = mroot {
            self.root = root;
        }
        Ok(())
    }

    fn lookup(&mut self, fix: &mut Fixture, key: u64) -> Result<()> {
        let keys = vec![key];
        let v = dm_btree_lookup(fix, &self.info, self.root, &keys)?;
        ensure!(v == Value64(key_to_value(key)));
        Ok(())
    }

    // This uses Rust code, rather than doing look ups via the kernel
    // code.
    fn check_keys_present(&self, fix: &mut Fixture, keys: &[u64]) -> Result<()> {
        let bm = get_bm(fix, self.bm);
        check_keys_present(&bm, self.root, keys)
    }

    fn commit(&mut self, fix: &mut Fixture) -> Result<()> {
        dm_tm_pre_commit(fix, self.tm)?;
        dm_tm_commit(fix, self.tm, self.sb.unwrap())?;
        self.sb = None;
        Ok(())
    }

    fn stats_start(&mut self, fix: &mut Fixture) {
        let bm = get_bm(fix, self.bm);
        self.baseline = Stats::collect_stats(fix, &bm);
    }

    fn stats_report(&self, fix: &mut Fixture, desc: &str, count: u64) -> Result<()> {
        let bm = get_bm(fix, self.bm);
        let delta = self.baseline.delta(fix, &bm);
        info!(
            "{}: residency = {}, instrs = {}, read_locks = {:.1}, write_locks = {:.1}",
            desc,
            self.residency(fix)?,
            delta.instrs / count,
            delta.read_locks as f64 / count as f64,
            delta.write_locks as f64 / count as f64
        );
        Ok(())
    }

    fn residency(&self, fix: &mut Fixture) -> Result<usize> {
        let bm = get_bm(fix, self.bm);
        calc_residency::<Value64>(&bm, self.root)
    }

    fn cleanup(&mut self, fix: &mut Fixture) {
        if let Some(sb) = self.sb {
            dm_bm_unlock(fix, sb).expect("unlock superblock");
        }
        dm_tm_destroy(fix, self.tm).expect("destroy tm");
        dm_bm_destroy(fix, self.bm).expect("destroy bm");
    }
}

// keys contains the keys we wish to insert, in the order
// that they should be inserted.
fn do_insert_test_(
    fix: &mut Fixture,
    keys: &[u64],
    pass_count: usize,
    target_residency: usize,
) -> Result<()> {
    standard_globals(fix)?;
    let mut bt = BTreeTest::new(fix)?;
    let commit_interval = 100;

    // First pass inserts, subsequent passes overwrite
    let mut commit_counter = commit_interval;
    for pass in 0..pass_count {
        bt.stats_start(fix);
        bt.begin(fix)?;
        for k in keys {
            bt.insert(fix, *k)?;

            if commit_counter == 0 {
                bt.commit(fix)?;
                bt.begin(fix)?;
                commit_counter = commit_interval;
            }
            commit_counter -= 1;
        }
        bt.commit(fix)?;

        let residency = bt.residency(fix)?;
        if residency < target_residency {
            return Err(anyhow!("Residency is too low ({}%)", residency));
        }

        let desc = if pass == 0 { "insert" } else { "overwrite" };
        bt.stats_report(fix, desc, keys.len() as u64)?;
    }

    // Lookup
    bt.begin(fix)?;
    bt.stats_start(fix);
    for k in keys {
        bt.lookup(fix, *k)?;
    }
    bt.stats_report(fix, "lookup", keys.len() as u64)?;
    bt.commit(fix)?;

    bt.check_keys_present(fix, &keys)?;

    Ok(())
}

const KEY_COUNT: u64 = 10240;

fn test_insert_ascending(fix: &mut Fixture) -> Result<()> {
    let keys: Vec<u64> = (0..KEY_COUNT).collect();
    do_insert_test_(fix, &keys, 2, 75)
}

fn test_insert_descending(fix: &mut Fixture) -> Result<()> {
    let keys: Vec<u64> = (0..KEY_COUNT).rev().collect();
    do_insert_test_(fix, &keys, 2, 49)
}

fn test_insert_random(fix: &mut Fixture) -> Result<()> {
    let mut keys: Vec<u64> = (0..KEY_COUNT).rev().collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    keys.shuffle(&mut rng);
    do_insert_test_(fix, &keys, 2, 75)
}

fn test_insert_runs(fix: &mut Fixture) -> Result<()> {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut endpoints = BTreeSet::new();
    for _ in 0..500 {
        endpoints.insert(rng.gen_range(0..KEY_COUNT));
    }
    endpoints.insert(KEY_COUNT);

    let mut ranges = Vec::new();
    let mut last = 0;
    for e in endpoints {
        if e != last {
            ranges.push(last..e);
        }
        last = e;
    }
    ranges.shuffle(&mut rng);

    let mut shuffled_keys = Vec::new();
    for r in ranges {
        for k in r {
            shuffled_keys.push(k);
        }
    }

    do_insert_test_(fix, &shuffled_keys, 2, 80)
}

//-------------------------------

fn mk_node(fix: &mut Fixture, key_begin: u64, nr_entries: usize) -> Result<(AutoGPtr, Addr)> {
    let header = NodeHeader {
        block: 1,
        is_leaf: true,
        nr_entries: nr_entries as u32,
        max_entries: calc_max_entries::<Value64>() as u32,
        value_size: Value64::guest_len() as u32,
    };
    let keys: Vec<u64> = (key_begin..key_begin + nr_entries as u64).collect();
    let values: Vec<Value64> = (key_begin..key_begin + nr_entries as u64)
        .map(Value64)
        .collect();
    let node = Node::Leaf {
        header,
        keys,
        values,
    };

    let mut buffer = vec![0u8; BLOCK_SIZE];
    let mut w = Cursor::new(&mut buffer);
    pack_node(&node, &mut w)?;
    drop(w);

    let (mut fix, block) = auto_alloc(fix, BLOCK_SIZE)?;
    fix.vm.mem.write(block, &buffer, PERM_WRITE)?;

    Ok((fix, block))
}

fn get_node<V: Unpack>(fix: &mut Fixture, block: Addr, ignore_non_fatal: bool) -> Result<Node<V>> {
    let node = fix.vm.mem.read_some(block, PERM_READ, |bytes| {
        unpack_node(&[0], bytes, ignore_non_fatal, false)
    })??;

    Ok(node)
}

fn check_node(node: &Node<Value64>, key_begin: u64, nr_entries: usize) -> Result<()> {
    let header = node.get_header();
    ensure!(nr_entries as u32 == header.nr_entries);
    ensure!(header.is_leaf);

    let mut i = key_begin;
    for key in node.get_keys().iter() {
        ensure!(*key == i);
        i += 1;
    }

    if let Node::<Value64>::Leaf { values, .. } = node {
        i = key_begin;
        for value in values.iter() {
            ensure!((*value).0 == i);
            i += 1;
        }
    }

    Ok(())
}

//-------------------------------

/*
#[derive(Debug, PartialEq, Eq)]
struct Move {
    dest: Addr,
    src: Addr,
    len: usize,
}

// This checks that we never read a region after writing it.  Since
// the src and dest copy_cursors overlap this is a real concern.
fn check_moves(moves: &[Move]) -> Result<()> {
    // Tracks which bytes have been written
    let mut writes = BTreeSet::new();

    info!("{:?}", moves);
    for m in moves {
        for i in 0..m.len {
            ensure!(!writes.contains(&(m.src.0 + i as u64)));
            writes.insert(m.dest.0 + i as u64);
        }
    }

    Ok(())
}

// We test redistribute_entries() by capturing a trace of the memmove
// calls it makes, and checking for out of order copies.
fn do_redistribute_test(
    fix: &mut Fixture,
    mut dest: CopyCursor,
    mut src: CopyCursor,
) -> Result<()> {
    let moves = Arc::new(Mutex::new(Vec::new()));

    // Register a stub for memmove that captures call details
    // but does nothing.
    {
        let moves = moves.clone();
        let memmove = move |fix: &mut Fixture| -> Result<()> {
            use Reg::*;
            let dest = Addr(fix.vm.reg(A0));
            let src = Addr(fix.vm.reg(A1));
            let len = fix.vm.reg(A2) as usize;
            let mut moves = moves.lock().unwrap();
            moves.push(Move { dest, src, len });
            fix.vm.ret(0);
            Ok(())
        };

        fix.at_func("memmove", Box::new(memmove))?;
    }

    redistribute_entries(&mut *fix, &mut dest, &mut src)?;

    let moves = moves.lock().unwrap();
    check_moves(&moves)?;

    Ok(())
}

fn do_redistribute_2(fix: &mut Fixture, lhs_count: u32, rhs_count: u32) -> Result<()> {
    let total_count = lhs_count + rhs_count;
    let lhs_target = total_count / 2;
    let rhs_target = total_count - lhs_target;

    let (mut fix, node1_ptr) = mk_node(fix, lhs_count as usize)?;
    let (mut fix, node2_ptr) = mk_node(&mut *fix, rhs_count as usize)?;

    let dest = CopyCursor {
        index: 0,
        entries: vec![
            CursorEntry::new(node1_ptr, 0, lhs_target),
            CursorEntry::new(node2_ptr, 0, rhs_target),
        ],
    };

    let src = CopyCursor {
        index: 0,
        entries: vec![
            CursorEntry::new(node1_ptr, 0, lhs_count),
            CursorEntry::new(node2_ptr, 0, rhs_count),
        ],
    };

    info!("dest: {:?}", dest);
    info!("src: {:?}", src);
    do_redistribute_test(&mut *fix, dest, src)
}
*/

/*fn test_redistribute_entries(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    do_redistribute_2(fix, 0, 100)?;
    do_redistribute_2(fix, 25, 75)?;
    do_redistribute_2(fix, 50, 50)?;
    info!("75, 25");
    do_redistribute_2(fix, 75, 25)?;
    info!("100, 0");
    do_redistribute_2(fix, 100, 0)?;
    Ok(())
}*/

//-------------------------------

fn test_redistribute_2(fix: &mut Fixture, nr_left: usize, nr_right: usize) -> Result<()> {
    standard_globals(fix)?;

    let total = nr_left + nr_right;
    let target_left = total / 2;
    let target_right = total - target_left;

    let (mut fix, left_ptr) = mk_node(fix, 0u64, nr_left)?;
    let (mut fix, right_ptr) = mk_node(&mut *fix, nr_left as u64, nr_right)?;
    redistribute2(&mut *fix, left_ptr, right_ptr)?;

    let left = get_node::<Value64>(&mut *fix, left_ptr, true)?;
    let right = get_node::<Value64>(&mut *fix, right_ptr, true)?;
    check_node(&left, 0u64, target_left)?;
    check_node(&right, target_left as u64, target_right)?;

    Ok(())
}

fn test_redistribute2_balanced(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 50, 50)
}

fn test_redistribute2_right_only(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 0, 100)
}

fn test_redistribute2_left_below_target(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 25, 75)
}

fn test_redistribute2_left_only(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 100, 0)
}

fn test_redistribute2_right_below_target(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 75, 25)
}

//-------------------------------

fn test_redistribute_3(
    fix: &mut Fixture,
    nr_left: usize,
    nr_center: usize,
    nr_right: usize,
) -> Result<()> {
    standard_globals(fix)?;

    let total = nr_left + nr_center + nr_right;
    let target_left = total / 3;
    let target_center = (total - target_left) / 2;
    let target_right = total - target_left - target_center;

    let (mut fix, left_ptr) = mk_node(fix, 0u64, nr_left)?;
    let (mut fix, center_ptr) = mk_node(&mut *fix, nr_left as u64, nr_center)?;
    let (mut fix, right_ptr) = mk_node(&mut *fix, (nr_left + nr_center) as u64, nr_right)?;
    redistribute3(&mut *fix, left_ptr, center_ptr, right_ptr)?;

    let left = get_node::<Value64>(&mut *fix, left_ptr, true)?;
    let center = get_node::<Value64>(&mut *fix, center_ptr, true)?;
    let right = get_node::<Value64>(&mut *fix, right_ptr, true)?;
    check_node(&left, 0u64, target_left)?;
    check_node(&center, target_left as u64, target_center)?;
    check_node(&right, (target_left + target_center) as u64, target_right)?;

    Ok(())
}

fn test_redistribute3_both_above_target(fix: &mut Fixture) -> Result<()> {
    test_redistribute_3(fix, 50, 0, 50)
}

fn test_redistribute3_left_below_target(fix: &mut Fixture) -> Result<()> {
    test_redistribute_3(fix, 25, 0, 75)
}

fn test_redistribute3_left_only(fix: &mut Fixture) -> Result<()> {
    test_redistribute_3(fix, 100, 0, 0)
}

fn test_redistribute3_right_below_target(fix: &mut Fixture) -> Result<()> {
    test_redistribute_3(fix, 75, 0, 25)
}

fn test_redistribute3_right_only(fix: &mut Fixture) -> Result<()> {
    test_redistribute_3(fix, 0, 0, 100)
}

//-------------------------------

fn fuzz_insert_(mut fix: Fixture, seed: u64, keys: Vec<u64>) -> Result<()> {
    let mut children: BTreeMap<u32, Vec<u64>> = BTreeMap::new();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);

    let mut bt = BTreeTest::new(&mut fix)?;
    bt.begin(&mut fix)?;
    for k in &keys {
        bt.insert(&mut fix, *k)?
    }
    bt.commit(&mut fix)?;

    let mut probes = 10000;
    for i in 0..probes {
        if i > 100 && i > children.len() * 10 {
            probes = i;
            break;
        }

        let mut fix2 = fix.clone();
        let mut bt = bt.clone();

        let new_key = rng.gen_range(0..1000000);
        fix2.vm.reset_block_hash();
        bt.begin(&mut fix2)?;
        bt.insert(&mut fix2, new_key)?;
        let mut keys = keys.clone();
        keys.push(new_key);
        bt.commit(&mut fix2)?;

        if children.get(&fix2.vm.block_hash).is_none() {
            // only check the btree if we hit a new code path
            bt.check_keys_present(&mut fix2, &keys)?;
            children.insert(fix2.vm.block_hash, vec![new_key]);
        }
    }

    debug!("found {} unique paths, {} probes", children.len(), probes);
    Ok(())
}

fn fuzz_insert(fix: Fixture, seed: u64, keys: Vec<u64>) {
    if let Err(e) = fuzz_insert_(fix, seed, keys) {
        debug!("BANG: {:?}", e);
    }
}

fn search_for_interesting(
    fix: &mut Fixture,
    keys: &[u64],
    interesting: &mut Vec<Vec<u64>>,
) -> Result<()> {
    let mut unique_blocks: BTreeSet<u64> = BTreeSet::new();
    let mut bt = BTreeTest::new(fix)?;
    bt.begin(fix)?;
    for (i, k) in keys.iter().enumerate() {
        let old_instrs = fix.vm.stats.instrs;
        fix.vm.reset_block_hash();
        bt.insert(fix, *k)?;
        let instrs = fix.vm.stats.instrs - old_instrs;

        if !fix.vm.unique_blocks.is_subset(&unique_blocks) {
            // We've found an interesting tree
            debug!("insert {} is interesting, {} instructions", i, instrs);
            unique_blocks.append(&mut fix.vm.unique_blocks.clone());
            interesting.push(keys[0..i].to_vec());
        }
    }
    bt.commit(fix)?;
    Ok(())
}

fn get_nr_threads() -> Result<usize> {
    let n = match std::env::var_os("FUZZ_THREADS") {
        None => num_cpus::get(),
        Some(str) => std::str::FromStr::from_str(str.to_str().unwrap())?,
    };
    Ok(n)
}

fn test_fuzz_insert(fix: &mut Fixture) -> Result<()> {
    const COUNT: u64 = 100000;
    standard_globals(fix)?;

    let mut original_fix = fix.clone();

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    // First pass inserts, subsequent passes overwrite
    let mut interesting: Vec<Vec<u64>> = Vec::new();

    debug!("hunting interesting with random inserts");
    let mut keys: Vec<u64> = Vec::new();
    for _ in 0..COUNT {
        keys.push(rng.gen_range(0..1000000));
    }
    search_for_interesting(fix, &keys[0..], &mut interesting)?;

    debug!(
        "spawning fuzz threads for {} interesting cases",
        interesting.len()
    );
    let nr_threads = get_nr_threads()?;
    let pool = ThreadPool::new(nr_threads);
    let now = Instant::now();

    for keys in interesting {
        let mut fix: Fixture = original_fix.deep_copy();
        let seed = rng.gen_range(0..1000000);
        pool.execute(move || {
            fuzz_insert(fix, seed, keys);
        });
    }

    debug!("waiting for fuzz threads");
    pool.join();

    debug!("fuzz threads took {}", now.elapsed().as_secs_f32());

    Ok(())
}

//-------------------------------

fn fuzz_remove_(mut fix: Fixture, mut bt: BTreeTest, seed: u64, mut keys: Vec<u64>) -> Result<()> {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);

    // Shuffle the keys so we remove in a random order
    keys.shuffle(&mut rng);

    for (i, k) in keys.iter().enumerate() {
        let old_instrs = fix.vm.stats.instrs;
        bt.begin(&mut fix)?;
        bt.remove(&mut fix, *k)?;
        bt.commit(&mut fix)?;

        bt.check_keys_present(&mut fix, &keys[i + 1..])?;

        if i % 1000 == 0 {
            debug!("removed {}", i);
        }
    }

    Ok(())
}

fn fuzz_remove(fix: Fixture, bt: BTreeTest, seed: u64, keys: Vec<u64>, tx: Sender<anyhow::Error>) {
    if let Err(e) = fuzz_remove_(fix, bt, seed, keys) {
        tx.send(e).unwrap();
    }
}

fn test_fuzz_remove(fix: &mut Fixture) -> Result<()> {
    const COUNT: u64 = 10000;
    standard_globals(fix)?;

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut keyset = BTreeSet::new();
    let mut keys: Vec<u64> = Vec::new();
    while keyset.len() < COUNT as usize {
        let k = rng.gen_range(0..1000000);
        if !keyset.contains(&k) {
            keys.push(k);
            keyset.insert(k);
        }
    }

    debug!("building initial btree");
    let mut bt = BTreeTest::new(fix)?;
    bt.begin(fix)?;
    for k in &keys {
        bt.insert(fix, *k)?;
    }
    bt.commit(fix)?;

    let mut initial_fix = fix.clone();
    let mut initial_bt = bt.clone();

    let nr_threads = get_nr_threads()?;
    let nr_jobs = 64;

    let pool = ThreadPool::new(nr_threads);
    let now = Instant::now();

    debug!(
        "spawning {} fuzz jobs across {} threads.",
        nr_jobs, nr_threads
    );

    let (tx, rx) = channel();

    for _ in 0..nr_jobs {
        let mut fix: Fixture = initial_fix.deep_copy();
        let mut bt: BTreeTest = initial_bt.clone();
        let tx = tx.clone();
        let keys = keys.clone();
        let seed = rng.gen_range(0..1000000);
        pool.execute(move || {
            fuzz_remove(fix, bt, seed, keys, tx);
        });
    }
    drop(tx);

    let mut nr_failures = 0;
    while let Ok(v) = rx.recv() {
        debug!("received: {:?}", v);
        nr_failures += 1;
    }
    drop(rx);

    debug!("waiting for fuzz threads");
    pool.join();

    debug!("fuzz threads took {}", now.elapsed().as_secs_f32());

    if nr_failures != 0 {
        warn!("There were {} failures", nr_failures);
        Err(anyhow!("fuzz failures"))
    } else {
        Ok(())
    }
}

//-------------------------------

fn key_from_range(kr: &KeyRange, rng: &mut dyn RngCore) -> u64 {
    match (kr.start, kr.end) {
        (None, None) => 0,
        (None, Some(nr)) => rng.gen_range(0..nr),
        (Some(nr), None) => rng.gen_range(nr..(nr + 1000)),
        (Some(b), Some(e)) => rng.gen_range(b..e),
    }
}

fn fuzz_insert_damaged(
    mut fix: Fixture,
    bt: BTreeTest,
    seed: u64,
    loc: u64,
    kr: &KeyRange,
    tx: Sender<anyhow::Error>,
) {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);
    let mut probes = 40;
    // let _ = fix.stub("printk", 0); // disable printk

    for i in 0..probes {
        let mut fix2 = fix.clone();
        let mut bt = bt.clone();

        let mut bm = get_bm(&mut fix2, bt.bm);
        let engine: Arc<dyn IoEngine + Send + Sync> = bm;
        let block = engine.read(loc).expect("couldn't read block");

        // Damage the node at loc
        for _ in 0..64 {
            let byte = rng.gen_range(0..BLOCK_SIZE);
            let val = rng.gen_range(0..=255);
            block.get_data()[byte] = val;
        }
        checksum::write_checksum(&mut block.get_data(), checksum::BT::NODE)
            .expect("writing checksum failed");

        engine.write(&block).expect("couldn't write block");

        for _ in 0..100 {
            let k = key_from_range(kr, &mut rng);
            // bt.insert_fuzz(&mut fix2, k).expect("bang");

            if let Err(e) = bt
                .insert_fuzz(&mut fix2, k)
                .with_context(|| format!("fuzzing block {}", loc))
            {
                tx.send(e).unwrap();
            }
        }
    }
}

// Build a btree, damage a node (but correct checksum), try some inserts
// near the damaged node.

fn test_fuzz_insert_damaged(fix: &mut Fixture) -> Result<()> {
    const COUNT: u64 = 100000;
    standard_globals(fix)?;
    // enable_traces(fix);

    debug!("building initial tree");
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut bt = BTreeTest::new(fix)?;
    bt.begin(fix)?;
    for i in 0..COUNT {
        if i % 10000 == 0 {
            debug!("inserted {} keys", i);
        }
        let k = rng.gen_range(0..1000000);
        bt.insert(fix, k)?;
    }
    debug!("inserted {} keys", COUNT);
    bt.commit(fix)?;

    debug!("building list of nodes");
    let mut info = discover_nodes::<Value64>(get_bm(fix, bt.bm), bt.root)?;

    // let nr_jobs = nodes.len();
    let nr_threads = get_nr_threads()?;
    let pool = ThreadPool::new(nr_threads);
    let now = Instant::now();

    let (tx, rx) = channel();

    for (loc, kr) in info.internal_nodes {
        let mut fix: Fixture = fix.deep_copy();
        let seed = rng.gen_range(0..1000000);
        let bt = bt.clone();
        let tx = tx.clone();
        pool.execute(move || {
            fuzz_insert_damaged(fix, bt, seed, loc, &kr, tx);
        });
    }

    for (loc, kr) in info.leaf_nodes {
        let mut fix: Fixture = fix.deep_copy();
        let seed = rng.gen_range(0..1000000);
        let bt = bt.clone();
        let tx = tx.clone();
        pool.execute(move || {
            fuzz_insert_damaged(fix, bt, seed, loc, &kr, tx);
        });
    }

    drop(tx);

    let mut nr_failures = 0;
    while let Ok(v) = rx.recv() {
        debug!("received: {:?}", v);
        nr_failures += 1;
    }
    pool.join();

    debug!("fuzz threads took {}", now.elapsed().as_secs_f32());
    debug!("{} failures", nr_failures);

    ensure!(nr_failures == 0);

    Ok(())
}

//----------------------------

fn fuzz_remove_damaged(
    mut fix: Fixture,
    bt: BTreeTest,
    seed: u64,
    loc: u64,
    kr: &KeyRange,
    tx: Sender<anyhow::Error>,
) {
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(seed);
    let mut probes = 200;
    // let _ = fix.stub("printk", 0); // disable printk

    for i in 0..probes {
        let mut fix2 = fix.clone();
        let mut bt = bt.clone();

        let mut bm = get_bm(&mut fix2, bt.bm);
        let engine: Arc<dyn IoEngine + Send + Sync> = bm;
        let block = engine.read(loc).expect("couldn't read block");

        // Damage the node at loc
        for _ in 0..64 {
            let byte = rng.gen_range(0..BLOCK_SIZE);
            let val = rng.gen_range(0..=255);
            block.get_data()[byte] = val;
        }
        checksum::write_checksum(&mut block.get_data(), checksum::BT::NODE)
            .expect("writing checksum failed");

        engine.write(&block).expect("couldn't write block");

        for _ in 0..100 {
            let k = key_from_range(kr, &mut rng);
            // bt.remove_fuzz(&mut fix2, k).expect("bang");

            if let Err(e) = bt
                .remove_fuzz(&mut fix2, k)
                .with_context(|| format!("fuzzing block {}", loc))
            {
                tx.send(e).unwrap();
            }
        }
    }
}

// Build a btree, damage a node (but correct checksum), try some inserts
// near the damaged node.

fn test_fuzz_remove_damaged(fix: &mut Fixture) -> Result<()> {
    const COUNT: u64 = 100000;
    standard_globals(fix)?;
    // enable_traces(fix);

    debug!("building initial tree");
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);

    let mut bt = BTreeTest::new(fix)?;
    bt.begin(fix)?;
    for i in 0..COUNT {
        if i % 10000 == 0 {
            debug!("inserted {} keys", i);
        }
        let k = rng.gen_range(0..1000000);
        bt.insert(fix, k)?;
    }
    debug!("inserted {} keys", COUNT);
    bt.commit(fix)?;

    debug!("building list of nodes");
    let mut info = discover_nodes::<Value64>(get_bm(fix, bt.bm), bt.root)?;

    // let nr_jobs = nodes.len();
    let nr_threads = get_nr_threads()?;
    let pool = ThreadPool::new(nr_threads);
    let now = Instant::now();

    let (tx, rx) = channel();

    for (loc, kr) in info.internal_nodes {
        let mut fix: Fixture = fix.deep_copy();
        let seed = rng.gen_range(0..1000000);
        let bt = bt.clone();
        let tx = tx.clone();
        pool.execute(move || {
            fuzz_insert_damaged(fix, bt, seed, loc, &kr, tx);
        });
    }

    for (loc, kr) in info.leaf_nodes {
        let mut fix: Fixture = fix.deep_copy();
        let seed = rng.gen_range(0..1000000);
        let bt = bt.clone();
        let tx = tx.clone();
        pool.execute(move || {
            fuzz_remove_damaged(fix, bt, seed, loc, &kr, tx);
        });
    }

    drop(tx);

    let mut nr_failures = 0;
    while let Ok(v) = rx.recv() {
        debug!("received: {:?}", v);
        nr_failures += 1;
    }
    pool.join();

    debug!("fuzz threads took {}", now.elapsed().as_secs_f32());
    debug!("{} failures", nr_failures);

    ensure!(nr_failures == 0);

    Ok(())
}

//-------------------------------

struct Counter(u64);

impl Default for Counter {
    fn default() -> Self {
        Counter(0)
    }
}

impl Counter {
    fn inc(&mut self) {
        self.0 += 1;
    }
}

const COUNTER: u64 = 100000000;

fn fuzz_mutex(m: &Mutex<Counter>) {
    for i in 0..COUNTER {
        let mut c = m.lock().unwrap();
        c.inc();
    }
}

// Testing how _different_ Mutexes scale across different threads
fn test_fuzz_mutex(fix: &mut Fixture) -> Result<()> {
    let nr_threads = get_nr_threads()?;
    let spread = 7;

    let mut ms: Vec<Mutex<Counter>> = Vec::new();
    for i in 0..(nr_threads * spread) {
        ms.push(Mutex::new(Counter::default()));
    }

    let now = Instant::now();
    thread::scope(|s| {
        for tid in 0..nr_threads {
            let m = &ms[tid * spread];
            s.spawn(|_| {
                fuzz_mutex(m);
            });
        }
    })
    .unwrap();

    debug!("fuzz threads took {}", now.elapsed().as_secs_f32());

    /*
    for m in ms {
        let c = m.lock().unwrap();
        assert!(c.0 == COUNTER);
    }
    */

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![PDATA_MOD];
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
        "/pdata/btree/",
        test!("del/empty", test_del_empty)

        test_section! {
            "insert-overwrite-lookup/",
            test!("ascending", test_insert_ascending)
            test!("descending", test_insert_descending)
            test!("random", test_insert_random)
            test!("runs", test_insert_runs)
        }

        test_section! {
            "redistribute-2/",
            test!("balanced", test_redistribute2_balanced)
            test!("left-below-target", test_redistribute2_left_below_target)
            test!("left-only", test_redistribute2_left_only)
            test!("right-below-target", test_redistribute2_right_below_target)
            test!("right-only", test_redistribute2_right_only)
        }

        // the center node should be empty
        test_section! {
            "redistribute-3/",
            test!("both-above-target", test_redistribute3_both_above_target)
            test!("left-below-target", test_redistribute3_left_below_target)
            test!("left-only", test_redistribute3_left_only)
            test!("right-below-target", test_redistribute3_right_below_target)
            test!("right-only", test_redistribute3_right_only)
        }

        test_section! {
            "fuzz/",
            test!("insert", test_fuzz_insert)
            test!("remove", test_fuzz_remove)
            test!("insert-damaged", test_fuzz_insert_damaged)
            test!("remove-damaged", test_fuzz_remove_damaged)
            test!("mutex", test_fuzz_mutex)
        }
    };

    Ok(())
}

//-------------------------------
