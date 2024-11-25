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
use crate::wrappers::space_map::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{anyhow, ensure, Result};
use log::*;
use rand::prelude::*;
use rand::SeedableRng;
use std::collections::BTreeSet;
use std::io::Cursor;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use thinp::io_engine::BLOCK_SIZE;
use thinp::pdata::btree;
use thinp::pdata::btree::*;
use thinp::pdata::btree_walker::*;
use thinp::pdata::unpack::*;

//-------------------------------

/*
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

#[allow(dead_code)]
fn check_btree(root: u64) -> Result<()> {
    let walker = BTreeWalker::new(get_bm()?, false);
    let visitor = NoopVisitor {};
    let mut path = Vec::new();

    walker.walk::<NoopVisitor, u64>(&mut path, &visitor, root)?;

    Ok(())
}
*/

//-------------------------------

struct ResidencyVisitor {
    nr_entries: AtomicU32,
    nr_leaves: AtomicU32,
    leaves: Arc<Mutex<Vec<u64>>>,
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
        self.leaves.lock().unwrap().push(_header.block);
        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

fn get_tree_stats<V: Unpack>(bm: &Arc<BlockManager>, root: u64) -> Result<TreeStats> {
    let walker = BTreeWalker::new(bm.clone(), false);
    let visitor = ResidencyVisitor {
        nr_entries: AtomicU32::new(0),
        nr_leaves: AtomicU32::new(0),
        leaves: Arc::new(Mutex::new(Vec::new())),
    };
    let mut path = Vec::new();
    walker.walk::<ResidencyVisitor, V>(&mut path, &visitor, root)?;

    let nr_entries = visitor.nr_entries.load(Ordering::SeqCst) as u64;
    let nr_leaves = visitor.nr_leaves.load(Ordering::SeqCst) as u64;

    Ok(TreeStats {
        nr_entries,
        nr_leaves,
    })
}

struct LayoutVisitor {}

impl<V: Unpack> NodeVisitor<V> for LayoutVisitor {
    fn visit(
        &self,
        path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        keys: &[u64],
        _values: &[V],
    ) -> btree::Result<()> {
        println!("block {} entries {}", path.last().unwrap_or(&0), keys.len());
        Ok(())
    }

    fn visit_again(&self, _path: &[u64], _b: u64) -> btree::Result<()> {
        Ok(())
    }

    fn end_walk(&self) -> btree::Result<()> {
        Ok(())
    }
}

fn print_layout<V: Unpack>(bm: &Arc<BlockManager>, root: u64) {
    let walker = BTreeWalker::new(bm.clone(), false);
    let visitor2 = LayoutVisitor {};
    let mut path = Vec::new();
    let _ = walker.walk::<LayoutVisitor, V>(&mut path, &visitor2, root);
}

pub fn residency<V: Unpack>(stats: &TreeStats) -> Result<usize> {
    let max_entries = calc_max_entries::<V>() as u64;
    let percent = (stats.nr_entries * 100) / (max_entries * stats.nr_leaves);
    Ok(percent as usize)
}

// Because this is a walk it implicitly checks the btree.  Returns
// average residency as a _percentage_.
pub fn calc_residency<V: Unpack>(bm: &Arc<BlockManager>, root: u64) -> Result<usize> {
    let stats = get_tree_stats::<V>(bm, root)?;
    debug!(
        "nr_leaves = {}, nr_entries = {}",
        stats.nr_leaves, stats.nr_entries
    );
    residency::<V>(&stats)
}

//-------------------------------

// Used to confirm all expected keys are present in the tree.
struct EntryVisitor {
    seen: Mutex<BTreeSet<u64>>,
}

fn key_to_value(k: u64) -> u64 {
    k + 12345
}

impl NodeVisitor<u64> for EntryVisitor {
    fn visit(
        &self,
        _path: &[u64],
        _kr: &KeyRange,
        _header: &NodeHeader,
        keys: &[u64],
        values: &[u64],
    ) -> btree::Result<()> {
        for (i, k) in keys.iter().enumerate() {
            let v = values[i];
            if v != key_to_value(*k) {
                return Err(BTreeError::ValueError(format!(
                    "Key has bad value: {} -> {}",
                    k, v
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
    walker.walk::<EntryVisitor, u64>(&mut path, &visitor, root)?;

    let seen = visitor.seen.lock().unwrap();
    for k in keys {
        if !seen.contains(k) {
            return Err(anyhow!("Key missing from btree: {}", *k));
        }
    }

    Ok(())
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

    let mut bt = BTreeTest::new(fix)?;
    bt.begin()?;
    bt.delete()?;

    Ok(())
}

pub struct TreeStats {
    pub nr_leaves: u64,
    pub nr_entries: u64,
}

#[allow(dead_code)]
pub struct BTreeTest<'a> {
    pub fix: &'a mut Fixture,
    bm: Addr,
    tm: Addr,
    sm: Addr,
    sb: Option<Addr>,
    info: BTreeInfoPtr<u64>,
    root: u64,
    baseline: Stats,
}

impl<'a> BTreeTest<'a> {
    pub fn new(fix: &'a mut Fixture) -> Result<Self> {
        let bm = dm_bm_create(fix, 1024)?;
        let (tm, sm) = dm_tm_create(fix, bm, 0)?;

        // FIXME: we should increment the superblock within the sm

        let info = alloc_btree_info(fix, tm, 1, BTreeValueType::<u64>::default())?;
        let root = dm_btree_empty(fix, &info)?;
        let baseline = {
            let bm = get_bm(fix, bm);
            Stats::collect_stats(fix, &bm)
        };

        Ok(BTreeTest {
            fix,
            bm,
            tm,
            sm,
            sb: None,
            info,
            root,
            baseline,
        })
    }

    pub fn begin(&mut self) -> Result<()> {
        if self.sb.is_some() {
            return Err(anyhow!("transaction already begun"));
        }

        self.sb = Some(dm_bm_write_lock_zero(self.fix, self.bm, 0, Addr(0))?);
        Ok(())
    }

    pub fn insert(&mut self, key: u64) -> Result<()> {
        let ks = vec![key];
        let v = key_to_value(key);
        self.root = dm_btree_insert(self.fix, &self.info, self.root, &ks, &v)?;
        Ok(())
    }

    pub fn lookup(&mut self, key: u64) -> Result<()> {
        let keys = vec![key];
        let v = dm_btree_lookup(self.fix, &self.info, self.root, &keys)?;
        ensure!(v == key_to_value(key));
        Ok(())
    }

    pub fn remove(&mut self, key: u64) -> Result<()> {
        let keys = vec![key];
        self.root = dm_btree_remove(self.fix, &self.info, self.root, &keys)?;
        Ok(())
    }

    // This uses Rust code, rather than doing look ups via the kernel
    // code.
    pub fn check_keys_present(&self, keys: &[u64]) -> Result<()> {
        let bm = get_bm(self.fix, self.bm);
        check_keys_present(&bm, self.root, keys)
    }

    pub fn commit(&mut self) -> Result<()> {
        dm_tm_pre_commit(self.fix, self.tm)?;
        dm_tm_commit(self.fix, self.tm, self.sb.unwrap())?;
        self.sb = None;
        Ok(())
    }

    // This function takes ownership as the btree is no longer valid
    pub fn delete(mut self) -> Result<()> {
        dm_btree_del(self.fix, &self.info, self.root)?;
        self.commit()
    }

    pub fn stats_start(&mut self) {
        let bm = get_bm(self.fix, self.bm);
        self.baseline = Stats::collect_stats(self.fix, &bm);
    }

    pub fn stats_delta(&mut self) -> Result<Stats> {
        let bm = get_bm(self.fix, self.bm);
        let delta = self.baseline.delta(self.fix, &bm);
        Ok(delta)
    }

    pub fn stats_report(&self, desc: &str, count: u64) -> Result<()> {
        let bm = get_bm(self.fix, self.bm);
        let delta = self.baseline.delta(self.fix, &bm);
        info!(
            "{}: residency = {}, instrs = {}, read_locks = {:.1}, write_locks = {:.1}",
            desc,
            self.residency()?,
            delta.instrs / count,
            delta.read_locks as f64 / count as f64,
            delta.write_locks as f64 / count as f64
        );
        Ok(())
    }

    pub fn get_tree_stats(&self) -> Result<TreeStats> {
        let bm = get_bm(self.fix, self.bm);
        get_tree_stats::<u64>(&bm, self.root)
    }

    pub fn get_bm(&self) -> Arc<BlockManager> {
        get_bm(self.fix, self.bm)
    }

    pub fn residency(&self) -> Result<usize> {
        let bm = get_bm(self.fix, self.bm);
        calc_residency::<u64>(&bm, self.root)
    }

    pub fn print_layout(&self) -> Result<()> {
        let bm = get_bm(self.fix, self.bm);
        print_layout::<u64>(&bm, self.root);
        Ok(())
    }
}

impl<'a> Drop for BTreeTest<'a> {
    fn drop(&mut self) {
        free_btree_info(self.fix, &mut self.info).expect("release dm_btree_info");
        if let Some(sb) = self.sb {
            dm_bm_unlock(self.fix, sb).expect("unlock superblock");
        }
        dm_tm_destroy(self.fix, self.tm).expect("destroy tm");
        sm_destroy(self.fix, self.sm).expect("destroy sm");
        dm_bm_destroy(self.fix, self.bm).expect("destroy bm");
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
        bt.stats_start();
        bt.begin()?;
        for k in keys {
            bt.insert(*k)?;

            if commit_counter == 0 {
                bt.commit()?;
                bt.begin()?;
                commit_counter = commit_interval;
            }
            commit_counter -= 1;
        }
        bt.commit()?;

        let residency = bt.residency()?;
        if residency < target_residency {
            return Err(anyhow!("Residency is too low ({}%)", residency));
        }

        let desc = if pass == 0 { "insert" } else { "overwrite" };
        bt.stats_report(desc, keys.len() as u64)?;
    }

    // Lookup
    bt.begin()?;
    bt.stats_start();
    for k in keys {
        bt.lookup(*k)?;
    }
    bt.stats_report("lookup", keys.len() as u64)?;
    bt.commit()?;

    bt.check_keys_present(keys)?;

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
        max_entries: calc_max_entries::<u64>() as u32,
        value_size: u64::guest_len() as u32,
    };
    let keys: Vec<u64> = (key_begin..key_begin + nr_entries as u64).collect();
    let values: Vec<u64> = (key_begin..key_begin + nr_entries as u64).collect();
    let node = Node::Leaf {
        header,
        keys,
        values,
    };

    let mut buffer = vec![0u8; BLOCK_SIZE];
    let mut w = Cursor::new(&mut buffer);
    pack_node(&node, &mut w)?;

    let (mut fix, block) = auto_alloc(fix, BLOCK_SIZE)?;
    fix.vm.mem.write(block, &buffer, PERM_WRITE)?;

    Ok((fix, block))
}

fn get_node<V: Unpack>(fix: &Fixture, block: Addr, ignore_non_fatal: bool) -> Result<Node<V>> {
    let node = fix.vm.mem.read_some(block, PERM_READ, |bytes| {
        unpack_node(&[0], bytes, ignore_non_fatal, false)
    })??;

    Ok(node)
}

fn check_node(node: &Node<u64>, key_begin: u64, nr_entries: usize) -> Result<()> {
    let header = node.get_header();
    ensure!(nr_entries as u32 == header.nr_entries);
    ensure!(header.is_leaf);

    let mut i = key_begin;
    for key in node.get_keys().iter() {
        ensure!(*key == i);
        i += 1;
    }

    if let Node::<u64>::Leaf { values, .. } = node {
        i = key_begin;
        for value in values.iter() {
            ensure!(*value == i);
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
    let (mut fix, right_ptr) = mk_node(&mut fix, nr_left as u64, nr_right)?;
    redistribute2(&mut fix, left_ptr, right_ptr)?;

    let left = get_node::<u64>(&fix, left_ptr, true)?;
    let right = get_node::<u64>(&fix, right_ptr, true)?;
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
    let (mut fix, center_ptr) = mk_node(&mut fix, nr_left as u64, nr_center)?;
    let (mut fix, right_ptr) = mk_node(&mut fix, (nr_left + nr_center) as u64, nr_right)?;
    redistribute3(&mut fix, left_ptr, center_ptr, right_ptr)?;

    let left = get_node::<u64>(&fix, left_ptr, true)?;
    let center = get_node::<u64>(&fix, center_ptr, true)?;
    let right = get_node::<u64>(&fix, right_ptr, true)?;
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

fn test_remove_random(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let nr_entries = 100000u64;
    let mut keys: Vec<u64> = (0..nr_entries).collect();

    let mut bt = BTreeTest::new(fix)?;
    let commit_interval = 100;

    // First pass inserts, subsequent passes overwrite
    let mut commit_counter = commit_interval;

    bt.stats_start();
    bt.begin()?;
    for k in &keys {
        bt.insert(*k)?;

        if commit_counter == 0 {
            bt.commit()?;
            bt.begin()?;
            commit_counter = commit_interval;
        }
        commit_counter -= 1;
    }
    bt.commit()?;
    bt.stats_report("insert", keys.len() as u64)?;

    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    keys.shuffle(&mut rng);

    for k in &keys {
        bt.remove(*k)?;
        ensure!(bt.lookup(*k).is_err());
    }

    Ok(())
}

//-------------------------------

pub fn register_tests(tests: &mut TestSet) -> Result<()> {
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
            tests.register(&p, Test::new(kmodules.clone(), Box::new($func)));
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
            "remove/",
            test!("random", test_remove_random)
        }
    };

    Ok(())
}

//-------------------------------
