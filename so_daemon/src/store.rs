//! Persistence seam: how contract nodes and their evidence blobs are stored.
//!
//! Two responsibilities are split behind two traits so the graph topology and
//! the (potentially large) captured bytes can live in different systems and
//! scale independently:
//!
//!   * [`NodeStore`] — the contract nodes: identity, the projected
//!     assume-guarantee contract, and embedded evidence *metadata*. The
//!     production implementation is [`crate::arango::ArangoNodeStore`], a graph
//!     database chosen so the same product scales from a laptop to a cluster by
//!     relocation rather than by swapping engines.
//!   * [`BlobStore`] — the content-addressed snapshot bytes, kept out of the
//!     graph so the topology stays small and the bytes can sit in cheap object
//!     storage.
//!
//! A node document therefore carries only a `snapshot.content_hash` pointer into
//! the blob store; the captured bytes themselves are never written into the
//! graph (`Snapshot::content` is `#[serde(skip)]`).

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

use thiserror::Error;

use crate::domain::Node;

/// Persists and retrieves contract nodes (the graph vertices).
///
/// Edge methods (refinement/composition/conjunction/quotient) are deliberately
/// absent — edges are out of scope — but they slot in behind this same seam
/// without disturbing the ingest use case.
pub trait NodeStore {
    /// Persist a node. Idempotent on the node id: re-persisting the same id
    /// replaces it with identical content.
    fn add_contract(&self, node: &Node) -> Result<(), StoreError>;

    /// Fetch a node by id, or `None` if no such node exists.
    fn get_contract(&self, id: &str) -> Result<Option<Node>, StoreError>;
}

/// Stores content-addressed snapshot bytes, keyed by their SHA-256 hex hash.
pub trait BlobStore {
    /// Write a captured blob under its content hash. Idempotent: an existing
    /// blob with the same hash is left untouched (identical content ⇒ identical
    /// bytes).
    fn put_blob(&self, hash: &str, bytes: &[u8]) -> Result<(), StoreError>;

    /// Read a blob by its content hash, or `None` if it is not present.
    fn get_blob(&self, hash: &str) -> Result<Option<Vec<u8>>, StoreError>;
}

#[derive(Debug, Error)]
pub enum StoreError {
    #[error("failed to create store directory '{path}': {source}")]
    CreateDir {
        path: String,
        source: std::io::Error,
    },
    #[error("failed to write '{path}': {source}")]
    Write {
        path: String,
        source: std::io::Error,
    },
    #[error("failed to read '{path}': {source}")]
    Read {
        path: String,
        source: std::io::Error,
    },
    #[error("failed to serialize node: {0}")]
    Serialize(#[from] serde_json::Error),
    /// A failure reported by the graph-database backend, rendered to a message
    /// so this trait module stays independent of any particular driver.
    #[error("graph store backend error: {0}")]
    Backend(String),
}

/// A content-addressed blob store backed by a local directory, one file per
/// blob named by its hash.
pub struct FileBlobStore {
    root: PathBuf,
}

impl FileBlobStore {
    /// Open (creating if needed) a blob store rooted at `dir`.
    pub fn open(dir: &Path) -> Result<FileBlobStore, StoreError> {
        std::fs::create_dir_all(dir).map_err(|source| StoreError::CreateDir {
            path: dir.to_string_lossy().to_string(),
            source,
        })?;
        Ok(FileBlobStore {
            root: dir.to_path_buf(),
        })
    }

    /// The on-disk path a blob with `hash` would occupy.
    pub fn blob_path(&self, hash: &str) -> PathBuf {
        self.root.join(hash)
    }
}

impl BlobStore for FileBlobStore {
    fn put_blob(&self, hash: &str, bytes: &[u8]) -> Result<(), StoreError> {
        let path = self.blob_path(hash);
        if path.exists() {
            return Ok(());
        }
        std::fs::write(&path, bytes).map_err(|source| StoreError::Write {
            path: path.to_string_lossy().to_string(),
            source,
        })
    }

    fn get_blob(&self, hash: &str) -> Result<Option<Vec<u8>>, StoreError> {
        let path = self.blob_path(hash);
        match std::fs::read(&path) {
            Ok(bytes) => Ok(Some(bytes)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(source) => Err(StoreError::Read {
                path: path.to_string_lossy().to_string(),
                source,
            }),
        }
    }
}

/// An in-memory [`NodeStore`] for tests, so the ingest use case can be exercised
/// hermetically without a running graph database.
#[derive(Default)]
pub struct InMemoryNodeStore {
    nodes: RefCell<HashMap<String, Node>>,
}

impl InMemoryNodeStore {
    pub fn new() -> InMemoryNodeStore {
        InMemoryNodeStore::default()
    }

    /// Number of nodes held — a test convenience.
    pub fn len(&self) -> usize {
        self.nodes.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.borrow().is_empty()
    }
}

impl NodeStore for InMemoryNodeStore {
    fn add_contract(&self, node: &Node) -> Result<(), StoreError> {
        self.nodes
            .borrow_mut()
            .insert(node.id.clone(), node.clone());
        Ok(())
    }

    fn get_contract(&self, id: &str) -> Result<Option<Node>, StoreError> {
        Ok(self.nodes.borrow().get(id).cloned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blob_is_written_under_hash() {
        let tmp = tempfile::tempdir().unwrap();
        let store = FileBlobStore::open(tmp.path()).unwrap();
        store.put_blob("the-hash", b"some-content").unwrap();
        assert_eq!(
            store.get_blob("the-hash").unwrap().as_deref(),
            Some(&b"some-content"[..])
        );
    }

    #[test]
    fn put_blob_is_idempotent() {
        let tmp = tempfile::tempdir().unwrap();
        let store = FileBlobStore::open(tmp.path()).unwrap();
        store.put_blob("h", b"first").unwrap();
        // A second put with the same hash must not overwrite (content-addressed).
        store.put_blob("h", b"second").unwrap();
        assert_eq!(store.get_blob("h").unwrap().as_deref(), Some(&b"first"[..]));
    }

    #[test]
    fn missing_blob_is_none() {
        let tmp = tempfile::tempdir().unwrap();
        let store = FileBlobStore::open(tmp.path()).unwrap();
        assert!(store.get_blob("absent").unwrap().is_none());
    }

    #[test]
    fn in_memory_node_store_round_trips() {
        use crate::domain::{Meta, Node};
        use so_lang::grammar::{Assumption, Guarantee};

        let store = InMemoryNodeStore::new();
        let node = Node {
            id: "n1".to_string(),
            statement: "The pump shall stop.".to_string(),
            assumption: Assumption::Top,
            guarantee: Guarantee {
                subject: "pump".to_string(),
                response: "stop".to_string(),
            },
            meta: Meta {
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
            },
        };
        store.add_contract(&node).unwrap();
        assert_eq!(store.get_contract("n1").unwrap().as_ref(), Some(&node));
        assert!(store.get_contract("absent").unwrap().is_none());
    }
}
