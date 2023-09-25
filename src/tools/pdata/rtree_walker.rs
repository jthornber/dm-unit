use anyhow::Result;
use std::sync::{Arc, Mutex};
use thinp::io_engine::{Block, IoEngine};
use thinp::pdata::btree::split_key_ranges;

use crate::tools::pdata::rtree::*;
use crate::tools::pdata::rtree_error::*;

pub use thinp::pdata::btree::KeyRange;

//-------------------------------

#[derive(Debug, Default)]
pub struct TreeStats {
    pub nr_internal: u64,
    pub nr_leaves: u64,
    pub nr_entries: u64,
    pub nr_mapped_blocks: u64,
}

fn split_keys(parent_key: &KeyRange, entries: &[(u64, u64)]) -> Result<Vec<KeyRange>, RTreeError> {
    // FIXME: avoid collect
    let keys: Vec<u64> = entries.iter().map(|m| m.0).collect();
    // FIXME: remove the path parameter from split_key_ranges()
    split_key_ranges(&[], parent_key, &keys[..])
        .map_err(|_| RTreeError::ContextError("couldn't split key range".to_string()))
}

//-------------------------------

pub trait NodeVisitor {
    fn visit_internal(&self, _header: &Header, _entries: &[(u64, u64)]) -> Result<(), RTreeError> {
        Ok(())
    }

    fn visit(&self, header: &Header, entries: &[Mapping]) -> Result<(), RTreeError>;
}

//-------------------------------

pub struct RTreeWalker {
    engine: Arc<dyn IoEngine>,
}

impl RTreeWalker {
    pub fn new(engine: Arc<dyn IoEngine>) -> Self {
        Self { engine }
    }

    pub fn walk(&self, visitor: &dyn NodeVisitor, root: u64) -> Result<(), RTreeError> {
        let b = self.engine.read(root).map_err(|_| io_err(&[root]))?;
        let kr = KeyRange {
            start: None,
            end: None,
        };
        let mut path = Vec::new();
        self.visit_node(&mut path, visitor, &kr, &b)
    }

    fn visit_node(
        &self,
        path: &mut Vec<u64>,
        visitor: &dyn NodeVisitor,
        parent_key: &KeyRange,
        b: &Block,
    ) -> Result<(), RTreeError> {
        path.push(b.loc);
        let r = self.visit_node_(path, visitor, parent_key, b);
        path.pop();
        r
    }

    fn visit_node_(
        &self,
        path: &mut Vec<u64>,
        visitor: &dyn NodeVisitor,
        parent_key: &KeyRange,
        b: &Block,
    ) -> Result<(), RTreeError> {
        let node = unpack_node_checked(b).map_err(RTreeError::NodeError)?;

        match node {
            Node::Internal {
                ref header,
                ref entries,
            } => {
                let child_keys = split_keys(parent_key, entries)?;
                let bs: Vec<u64> = entries.iter().map(|m| m.1).collect();
                visitor.visit_internal(header, entries)?;
                self.visit_children(path, visitor, &child_keys, &bs)
            }
            Node::Leaf {
                ref header,
                ref entries,
            } => {
                if !entries.is_empty() {
                    let last = entries.last().unwrap();
                    if entries[0].thin_begin < parent_key.start.unwrap_or(0)
                        || last.thin_begin + last.len as u64 > parent_key.end.unwrap_or(u64::MAX)
                    {
                        return Err(RTreeError::ContextError("keys out of range".to_string()));
                    }
                }
                visitor.visit(header, entries)
            }
        }
    }

    fn visit_children(
        &self,
        path: &mut Vec<u64>,
        visitor: &dyn NodeVisitor,
        krs: &[KeyRange],
        bs: &[u64],
    ) -> Result<(), RTreeError> {
        let mut errs = Vec::new();

        // TODO: ignore shared blocks

        let rblocks = match self.engine.read_many(bs) {
            Ok(blocks) => blocks,
            Err(_) => {
                // IO completely failed
                for b in bs {
                    path.push(*b);
                    errs.push(io_err(path));
                    path.pop();
                }
                return aggregate_err(errs);
            }
        };

        for (i, rb) in rblocks.iter().enumerate() {
            if let Ok(b) = rb {
                if let Err(e) = self.visit_node(path, visitor, &krs[i], b) {
                    errs.push(e);
                }
            } else {
                path.push(bs[i]);
                errs.push(io_err(path));
                path.pop();
            }
        }

        aggregate_err(errs)
    }
}

//-------------------------------

#[derive(Default)]
struct RTreeCounter {
    stats: Mutex<TreeStats>,
}

impl RTreeCounter {
    fn new() -> Self {
        Self::default()
    }
}

impl NodeVisitor for RTreeCounter {
    fn visit_internal(&self, _header: &Header, _entries: &[(u64, u64)]) -> Result<(), RTreeError> {
        let mut stats = self.stats.lock().unwrap();
        stats.nr_internal += 1;
        Ok(())
    }

    fn visit(&self, _header: &Header, entries: &[Mapping]) -> Result<(), RTreeError> {
        let mut stats = self.stats.lock().unwrap();
        stats.nr_leaves += 1;
        stats.nr_entries += entries.len() as u64;

        // count the number of mapped blocks
        for m in entries {
            stats.nr_mapped_blocks += m.len as u64;
        }

        Ok(())
    }
}

pub fn rtree_stat(engine: Arc<dyn IoEngine>, root: u64) -> Result<TreeStats, RTreeError> {
    let w = RTreeWalker::new(engine);
    let v = RTreeCounter::new();
    w.walk(&v, root)?;
    let stats = v.stats.into_inner().unwrap();
    Ok(stats)
}

//-------------------------------

#[derive(Default)]
struct Inner {
    entries: Vec<Mapping>,
    nr_entries: Vec<u32>,
}

#[derive(Default)]
pub struct MappingCollector {
    inner: Mutex<Inner>,
}

impl MappingCollector {
    pub fn new() -> Self {
        Self::default()
    }
}

impl NodeVisitor for MappingCollector {
    fn visit(&self, header: &Header, entries: &[Mapping]) -> Result<(), RTreeError> {
        let mut inner = self.inner.lock().unwrap();
        inner.entries.extend_from_slice(entries);
        inner.nr_entries.push(header.nr_entries);
        Ok(())
    }
}

pub fn extract_rtree_entries(
    engine: Arc<dyn IoEngine>,
    root: u64,
) -> Result<(Vec<Mapping>, Vec<u32>), RTreeError> {
    let w = RTreeWalker::new(engine);
    let v = MappingCollector::new();
    w.walk(&v, root)?;
    let inner = v.inner.into_inner().unwrap();
    Ok((inner.entries, inner.nr_entries))
}

//-------------------------------
