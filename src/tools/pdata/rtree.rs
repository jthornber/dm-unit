use nom::{number::complete::*, IResult};
use thinp::io_engine::{Block, BLOCK_SIZE};
use thinp::pdata::unpack::Unpack;

use crate::tools::pdata::rtree_error::NodeError;

//-------------------------------

// FIXME: round down to a multiple of 3?
pub const MAX_LEAF_ENTRIES: usize = (BLOCK_SIZE - 32) / (8 + 8);
pub const MAX_INTERNAL_ENTRIES: usize = (BLOCK_SIZE - 32) / 16;
pub const MAPPINGS_MAX_LEN: usize = 4095;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub struct Header {
    pub block: u64,
    pub is_leaf: bool,
    pub node_end: u64,
    pub nr_entries: u32,
}

#[allow(dead_code)]
const INTERNAL_NODE: u32 = 1;
const LEAF_NODE: u32 = 2;

impl Unpack for Header {
    fn disk_size() -> u32 {
        32
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Header> {
        let (i, _csum) = le_u32(data)?;
        let (i, flags) = le_u32(i)?;
        let (i, block) = le_u64(i)?;
        let (i, node_end) = le_u64(i)?;
        let (i, nr_entries) = le_u32(i)?;
        let (i, _padding) = le_u32(i)?;

        Ok((
            i,
            Header {
                block,
                is_leaf: flags == LEAF_NODE,
                node_end,
                nr_entries,
            },
        ))
    }
}

//-------------------------------

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mapping {
    pub thin_begin: u64,
    pub data_begin: u64, // FIXME: shrink to u32
    pub len: u32,
    pub time: u32,
}

struct DiskMapping {
    data_begin: u64, // FIXME: shrink to u32
    len: u32,
    time: u32,
}

fn disk_mapping(data: &[u8]) -> IResult<&[u8], DiskMapping> {
    let (i, data_begin) = le_u32(data)?;
    let (i, len_time) = le_u32(i)?;

    Ok((
        i,
        DiskMapping {
            data_begin: data_begin as u64,
            len: len_time >> 20,
            time: len_time & ((1 << 20) - 1),
        },
    ))
}

pub enum Node {
    Internal {
        header: Header,
        entries: Vec<(u64, u64)>,
    },
    Leaf {
        header: Header,
        entries: Vec<Mapping>,
    },
}

impl Node {
    fn get_header(&self) -> &Header {
        match self {
            Self::Internal { header, .. } => header,
            Self::Leaf { header, .. } => header,
        }
    }
}

impl Unpack for Node {
    fn disk_size() -> u32 {
        BLOCK_SIZE as u32
    }

    fn unpack(data: &[u8]) -> IResult<&[u8], Node> {
        use nom::multi::count;

        let (i, header) = Header::unpack(data)?;
        if header.is_leaf {
            let (i, keys) = count(le_u64, header.nr_entries as usize)(i)?;
            let (i, _unused_keys) =
                count(le_u64, MAX_LEAF_ENTRIES - header.nr_entries as usize)(i)?;
            let (i, values) = count(disk_mapping, header.nr_entries as usize)(i)?;

            let entries = keys
                .iter()
                .zip(values)
                .map(|(thin_begin, dm)| Mapping {
                    thin_begin: *thin_begin,
                    data_begin: dm.data_begin,
                    len: dm.len,
                    time: dm.time,
                })
                .collect();
            Ok((i, Node::Leaf { header, entries }))
        } else {
            let (i, keys) = count(le_u64, header.nr_entries as usize)(i)?;
            let (i, _unused_keys) =
                count(le_u64, MAX_INTERNAL_ENTRIES - header.nr_entries as usize)(i)?;
            let (i, values) = count(le_u64, header.nr_entries as usize)(i)?;
            Ok((
                i,
                Node::Internal {
                    header,
                    entries: keys.iter().copied().zip(values).collect(),
                },
            ))
        }
    }
}

fn ensure_ordered_keys(entries: &[(u64, u64)]) -> Result<(), NodeError> {
    let last = entries[0].0;
    for (key, _) in &entries[1..] {
        if *key <= last {
            return Err(NodeError::KeysOutOfOrder);
        }
    }
    Ok(())
}

fn ensure_non_overlapped_entries(entries: &[Mapping]) -> Result<(), NodeError> {
    let mut last = entries[0].clone();
    if last.len == 0 {
        return Err(NodeError::EmptyEntries);
    }

    for m in &entries[1..] {
        if m.len == 0 {
            return Err(NodeError::EmptyEntries);
        }

        if m.thin_begin < last.thin_begin + last.len as u64 {
            return Err(NodeError::EntriesOverlapped);
        }

        last = m.clone();
    }

    Ok(())
}

pub fn unpack_node_checked(b: &Block) -> Result<Node, NodeError> {
    let data = b.get_data();
    let (_, node) = Node::unpack(data).map_err(|_| NodeError::IncompleteData)?;

    let header = node.get_header();
    if header.block != b.loc {
        return Err(NodeError::BlockNrMismatch);
    }

    if header.nr_entries > 1 {
        match node {
            Node::Internal { ref entries, .. } => ensure_ordered_keys(entries)?,
            Node::Leaf { ref entries, .. } => ensure_non_overlapped_entries(entries)?,
        }
    }

    Ok(node)
}

//-------------------------------
