use anyhow::{anyhow, Result};
use std::sync::{Arc, Mutex};
use thinp::hashvec::HashVec;
use thinp::io_engine::{Block, IoEngine};
use thinp::pdata::btree::split_key_ranges;
use thinp::pdata::space_map::RestrictedSpaceMap;
use thinp::pdata::space_map::SpaceMap;

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
    pub internals: Vec<u64>,
    pub leaves: Vec<u64>,
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
    sm: Arc<Mutex<dyn SpaceMap>>,
    node_errs: Mutex<HashVec<NodeError>>,
    subtree_errs: Mutex<HashVec<RTreeError>>,
    krs: Mutex<HashVec<std::ops::Range<u64>>>,
}

impl RTreeWalker {
    pub fn new(engine: Arc<dyn IoEngine>) -> Self {
        let nr_blocks = engine.get_nr_blocks();
        let sm = Arc::new(Mutex::new(RestrictedSpaceMap::new(nr_blocks)));
        Self {
            engine,
            sm,
            node_errs: Mutex::new(HashVec::new()),
            subtree_errs: Mutex::new(HashVec::new()),
            krs: Mutex::new(HashVec::new()),
        }
    }

    pub fn new_with_sm(engine: Arc<dyn IoEngine>, sm: Arc<Mutex<dyn SpaceMap>>) -> Result<Self> {
        {
            let sm = sm.lock().unwrap();
            if sm.get_nr_blocks().unwrap() < engine.get_nr_blocks() {
                return Err(anyhow!("insufficient space map size"));
            }
        }

        Ok(Self {
            engine,
            sm,
            node_errs: Mutex::new(HashVec::new()),
            subtree_errs: Mutex::new(HashVec::new()),
            krs: Mutex::new(HashVec::new()),
        })
    }

    // Atomically increments the ref count, and returns the _old_ count.
    fn sm_inc(&self, b: u64) -> Result<u32, RTreeError> {
        let mut sm = self.sm.lock().unwrap();
        let count = sm.get(b).map_err(|e| value_err(e.to_string()))?;
        sm.inc(b, 1).map_err(|e| value_err(e.to_string()))?;
        Ok(count)
    }

    // FIXME: ugly. to be replaced by ErrorTracker
    fn peek_error(&self, b: u64) -> Result<(), RTreeError> {
        let node_errs = self.node_errs.lock().unwrap();
        let subtree_errs = self.subtree_errs.lock().unwrap();

        if let Some(e) = node_errs.get(b as u32) {
            return Err(RTreeError::Path(
                vec![b],
                Box::new(RTreeError::NodeError(e.clone())),
            ));
        } else if let Some(_e) = subtree_errs.get(b as u32) {
            return Err(RTreeError::Path(
                vec![b],
                Box::new(RTreeError::ContextError(String::new())),
            ));
        }

        Ok(())
    }

    fn check_key_context(&self, b: u64, parent_kr: &KeyRange) -> Result<(), RTreeError> {
        // The child's key range might not be avilable if it is seriously damaged.
        let child_krs = self.krs.lock().unwrap();
        if let Some(child_kr) = child_krs.get(b as u32) {
            if parent_kr.start > Some(child_kr.start)
                || (parent_kr.end.is_some() && parent_kr.end < Some(child_kr.end))
            {
                return Err(RTreeError::Path(
                    vec![b],
                    Box::new(RTreeError::ContextError(String::new())),
                ));
            }
        }

        Ok(())
    }

    pub fn walk(&self, visitor: &dyn NodeVisitor, root: u64) -> Result<(), RTreeError> {
        let old_rc = self.sm_inc(root)?;
        if old_rc > 0 {
            return self.peek_error(root);
        }

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
                // split_key_ranges() implicitly checks the keys against its parent,
                // so we don't need to do further checks explicitly
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
                visitor.visit(header, entries).and_then(|_| {
                    let mut krs = self.krs.lock().unwrap();
                    let start = entries.first().map_or(0, |e| e.thin_begin);
                    let end = entries.last().map_or(0, |e| e.thin_begin + e.len as u64);
                    krs.insert(header.block as u32, std::ops::Range { start, end });
                    Ok(())
                })
            }
        }
    }

    fn filter_visited_blocks(
        &self,
        krs: &[KeyRange],
        bs: &[u64],
    ) -> (Vec<KeyRange>, Vec<u64>, Vec<RTreeError>) {
        let mut filtered_krs = Vec::new();
        let mut filtered_bs = Vec::new();
        let mut errs = Vec::new();

        for (b, kr) in bs.iter().zip(krs) {
            let old_rc = match self.sm_inc(*b) {
                Ok(n) => n,
                Err(e) => {
                    errs.push(e);
                    continue;
                }
            };

            if old_rc > 0 {
                // return previously visited errors
                if let Err(e) = self.peek_error(*b) {
                    errs.push(e);
                }

                // check the key context matches
                if let Err(e) = self.check_key_context(*b, kr) {
                    errs.push(e);
                }

                continue;
            }

            filtered_krs.push(kr.clone());
            filtered_bs.push(*b);
        }

        (filtered_krs, filtered_bs, errs)
    }

    fn visit_children(
        &self,
        path: &mut Vec<u64>,
        visitor: &dyn NodeVisitor,
        krs: &[KeyRange],
        bs: &[u64],
    ) -> Result<(), RTreeError> {
        let (krs, bs, mut errs) = self.filter_visited_blocks(krs, bs);

        let rblocks = match self.engine.read_many(&bs) {
            Ok(blocks) => blocks,
            Err(_) => {
                // IO completely failed
                let mut node_errs = self.node_errs.lock().unwrap();
                for b in bs {
                    node_errs.insert(b as u32, NodeError::IoError);
                    errs.push(io_err(&[b]));
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
                let mut node_errs = self.node_errs.lock().unwrap();
                node_errs.insert(bs[i] as u32, NodeError::IoError);
                errs.push(io_err(&[bs[i]]));
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
        stats.internals.push(_header.block);
        Ok(())
    }

    fn visit(&self, _header: &Header, entries: &[Mapping]) -> Result<(), RTreeError> {
        let mut stats = self.stats.lock().unwrap();
        stats.nr_leaves += 1;
        stats.nr_entries += entries.len() as u64;

        stats.leaves.push(_header.block);
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
