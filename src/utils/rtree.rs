use anyhow::Result;
use std::sync::Arc;

use crate::tools::pdata::rtree::MAX_LEAF_ENTRIES;
use crate::tools::pdata::rtree_walker::*;
use crate::block_manager::BlockManager;

//-------------------------------

fn residency(stats: &TreeStats) -> Result<usize> {
    let percent = (stats.nr_entries * 100) / (MAX_LEAF_ENTRIES as u64 * stats.nr_leaves);
    Ok(percent as usize)
}

// Because this is a walk it implicitly checks the btree.  Returns
// average residency as a _percentage_.
pub fn calc_residency(bm: Arc<BlockManager>, root: u64) -> Result<usize> {
    let stats = rtree_stat(bm, root)?;
    residency(&stats)
}

//-------------------------------
