use anyhow::{ensure, Result};
use thinp::io_engine::IoEngine;
use thinp::pdata::btree::split_key_ranges;
use thinp::pdata::unpack::Unpack;

use crate::pdata::rtree::*;

pub use thinp::pdata::btree::KeyRange;

//-------------------------------

#[derive(Debug, Default)]
pub struct TreeStats {
    pub nr_internal: u64,
    pub nr_leaves: u64,
    pub nr_entries: u64,
    pub nr_mapped_blocks: u64,
}

fn split_keys(parent_key: &KeyRange, entries: &[(u64, u64)]) -> Result<Vec<KeyRange>> {
    let keys: Vec<u64> = entries.iter().map(|m| m.0).collect();
    split_key_ranges(&[], parent_key, &keys[..]).map_err(|e| e.into())
}

pub fn rtree_check(
    engine: &dyn IoEngine,
    root: u64,
    parent_key: &KeyRange,
    stats: &mut TreeStats,
) -> Result<()> {
    let b = engine.read(root)?;
    let data = b.get_data();
    let (_, node) = Node::unpack(data)?;

    match node {
        Node::Internal { header, entries } => {
            //debug!("internal node {}", root);
            stats.nr_internal += 1;
            ensure!(header.block == root);

            let child_keys = split_keys(parent_key, &entries[..])?;

            for (kr, (_, val)) in child_keys.iter().zip(entries) {
                ensure!(val != 0);
                rtree_check(engine, val, kr, stats)?;
            }
        }
        Node::Leaf { header, entries } => {
            //debug!("leaf node {} entries {}", root, entries.len());
            stats.nr_leaves += 1;
            stats.nr_entries += entries.len() as u64;
            ensure!(header.block == root);

            let mut lowest_key = parent_key.start.unwrap_or(0);
            for m in entries {
                //debug!("  entry {:?}", m);
                ensure!(m.thin_begin >= lowest_key);
                ensure!(m.len > 0);
                stats.nr_mapped_blocks += m.len as u64;
                lowest_key = m.thin_begin + m.len as u64;
            }
            ensure!(lowest_key <= parent_key.end.unwrap_or(u64::MAX));
        }
    }

    Ok(())
}

//-------------------------------

pub trait NodeVisitor {
    fn visit(&mut self, header: Header, entries: Vec<Mapping>) -> Result<()>;
}

pub fn rtree_walk(engine: &dyn IoEngine, root: u64, visitor: &mut dyn NodeVisitor) -> Result<()> {
    let b = engine.read(root)?;
    let data = b.get_data();
    let (_, node) = Node::unpack(data)?;

    match node {
        Node::Internal { header: _, entries } => {
            for (_key, val) in entries {
                rtree_walk(engine, val, visitor)?;
            }
        }
        Node::Leaf { header, entries } => {
            visitor.visit(header, entries)?;
        }
    }

    Ok(())
}

//-------------------------------

pub struct MappingCollector {
    pub entries: Vec<Mapping>,
    pub nr_entries: Vec<u32>,
}

impl MappingCollector {
    pub fn new() -> Self {
        Self {
            entries: Vec::default(),
            nr_entries: Vec::default(),
        }
    }
}

impl NodeVisitor for MappingCollector {
    fn visit(&mut self, header: Header, entries: Vec<Mapping>) -> Result<()> {
        let mut other = entries;
        self.entries.append(&mut other);
        self.nr_entries.push(header.nr_entries);
        Ok(())
    }
}

//-------------------------------
