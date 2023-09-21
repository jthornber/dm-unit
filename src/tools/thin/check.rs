use anyhow::{anyhow, Result};
use std::sync::{Arc, Mutex};
use thinp::io_engine::IoEngine;
use thinp::pdata::btree_walker::btree_to_map_with_sm;
use thinp::pdata::space_map::checker::*;
use thinp::pdata::space_map::common::SMRoot;
use thinp::pdata::space_map::core_sm;
use thinp::pdata::space_map::ASpaceMap;
use thinp::pdata::space_map::RestrictedSpaceMap;
use thinp::pdata::unpack::unpack;
use thinp::report::Report;
use thinp::thin::device_detail::DeviceDetail;
use thinp::thin::superblock::*;

use crate::tools::pdata::rtree::Header;
use crate::tools::pdata::rtree::Mapping;
use crate::tools::pdata::rtree_error::RTreeError;
use crate::tools::pdata::rtree_walker::{NodeVisitor, RTreeWalker};

//-------------------------------

pub struct BottomLevelVisitor {
    data_sm: ASpaceMap,
}

impl BottomLevelVisitor {
    pub fn new(data_sm: ASpaceMap) -> Self {
        Self { data_sm }
    }
}

impl NodeVisitor for BottomLevelVisitor {
    fn visit(&self, _header: &Header, entries: &[Mapping]) -> Result<(), RTreeError> {
        if entries.is_empty() {
            return Ok(());
        }

        let mut data_sm = self.data_sm.lock().unwrap();

        let mut start = entries[0].data_begin;
        let mut len = entries[0].len as u64;
        for e in &entries[1..] {
            if e.data_begin == start + len {
                len += e.len as u64;
            } else {
                data_sm
                    .inc(start, len)
                    .map_err(|_| RTreeError::ValueError("block out of bounds".to_string()))?;

                start = e.data_begin;
                len = e.len as u64;
            }
        }
        data_sm
            .inc(start, len)
            .map_err(|_| RTreeError::ValueError("block out of bounds".to_string()))?;

        Ok(())
    }
}

//-------------------------------

// FIXME: remove duplicate function
fn create_metadata_sm(
    engine: &Arc<dyn IoEngine + Send + Sync>,
    sb: &Superblock,
    sb_snap: &Option<Result<Superblock>>,
    ignore_non_fatal: bool,
) -> Result<ASpaceMap> {
    let mut path = vec![0];

    // Use a temporary space map to reach out non-shared leaves so we could get
    // the maximum reference count of a bottom-level leaf it could be.
    let metadata_sm = Arc::new(Mutex::new(RestrictedSpaceMap::new(engine.get_nr_blocks())));

    let roots = btree_to_map_with_sm::<u64>(
        &mut path,
        engine.clone(),
        metadata_sm.clone(),
        ignore_non_fatal,
        sb.mapping_root,
    )?;

    let mut nr_devs = roots.len();

    if let Some(Ok(sb_snap)) = sb_snap {
        let roots_snap = btree_to_map_with_sm::<u64>(
            &mut path,
            engine.clone(),
            metadata_sm,
            ignore_non_fatal,
            sb_snap.mapping_root,
        )?;
        nr_devs += roots_snap.len();
    }

    let metadata_sm = core_sm(engine.get_nr_blocks(), nr_devs as u32);

    Ok(metadata_sm)
}

pub fn check_rtree(engine: Arc<dyn IoEngine + Send + Sync>, report: Arc<Report>) -> Result<()> {
    let sb = read_superblock(engine.as_ref(), SUPERBLOCK_LOCATION)?;

    // Read the superblock in metadata snapshot (allow errors)
    let sb_snap = if sb.metadata_snap > 0 {
        Some(read_superblock(engine.as_ref(), sb.metadata_snap))
    } else {
        None
    };

    let meta_sm = create_metadata_sm(&engine, &sb, &sb_snap, false)?;
    meta_sm.lock().unwrap().inc(SUPERBLOCK_LOCATION, 1)?; // superblock

    let mut path = Vec::new();
    let roots = btree_to_map_with_sm(
        &mut path,
        engine.clone(),
        meta_sm.clone(),
        false,
        sb.mapping_root,
    )?;

    let data_root = unpack::<SMRoot>(&sb.data_sm_root[0..])?;
    let data_sm = core_sm(data_root.nr_blocks, roots.len() as u32);

    // Check the details tree
    btree_to_map_with_sm::<DeviceDetail>(
        &mut path,
        engine.clone(),
        meta_sm.clone(),
        false,
        sb.details_root,
    )?;

    // Check the mapping tree
    let w = RTreeWalker::new_with_sm(engine.clone(), meta_sm.clone())?;
    let v = BottomLevelVisitor::new(data_sm.clone());
    for (_thin_id, root) in roots {
        w.walk(&v, root)?;
    }

    // Check data space map
    let leaks = check_disk_space_map(
        engine.clone(),
        report.clone(),
        data_root,
        data_sm.clone(),
        meta_sm.clone(),
        false,
    )?;
    if !leaks.is_empty() {
        return Err(anyhow!("data space map contains leaks"));
    }

    // Check metadata space map
    let meta_root = unpack::<SMRoot>(&sb.metadata_sm_root[0..])?;
    let leaks = check_metadata_space_map(engine, report, meta_root, meta_sm, false)?;
    if !leaks.is_empty() {
        return Err(anyhow!("metadata space map contains leaks"));
    }

    Ok(())
}

//-------------------------------
