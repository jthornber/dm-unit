use std::fmt;
use thinp::pdata::btree_error::encode_node_path;
use thiserror::Error;

#[derive(Clone, Debug)]
pub enum NodeError {
    IoError,
    NotANode,
    ChecksumError,
    BlockNrMismatch,
    KeysOutOfOrder,
    EntriesOverlapped,
    EmptyEntries,
    IncompleteData,
}

impl fmt::Display for NodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use NodeError::*;

        match self {
            IoError => write!(f, "io error"),
            NotANode => write!(f, "not a btree node"),
            ChecksumError => write!(f, "checksum error"),
            BlockNrMismatch => write!(f, "blocknr mismatch"),
            KeysOutOfOrder => write!(f, "keys out of order"),
            EntriesOverlapped => write!(f, "entries overlapped"),
            EmptyEntries => write!(f, "empty entries"),
            IncompleteData => write!(f, "incomplete data"),
        }
    }
}

#[derive(Error, Clone, Debug)]
pub enum RTreeError {
    NodeError(NodeError),
    Path(Vec<u64>, Box<RTreeError>),
    ContextError(String),
    ValueError(String),
    Aggregate(Vec<RTreeError>),
}

impl fmt::Display for RTreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RTreeError::NodeError(e) => write!(f, "node error: {}", e),
            RTreeError::Path(path, e) => write!(f, "{} {}", e, encode_node_path(path)),
            RTreeError::ContextError(msg) => write!(f, "context error: {}", msg),
            RTreeError::ValueError(msg) => write!(f, "value eror: {}", msg),
            RTreeError::Aggregate(errs) => {
                for e in errs {
                    write!(f, "{}", e)?
                }
                Ok(())
            }
        }
    }
}

pub fn io_err(path: &[u64]) -> RTreeError {
    RTreeError::Path(
        path.to_vec(),
        Box::new(RTreeError::NodeError(NodeError::IoError)),
    )
}

pub fn value_err(s: String) -> RTreeError {
    RTreeError::ValueError(s)
}

pub fn aggregate_err(errs: Vec<RTreeError>) -> Result<(), RTreeError> {
    match errs.len() {
        0 => Ok(()),
        1 => Err(errs[0].clone()),
        _ => Err(RTreeError::Aggregate(errs)),
    }
}
