//! Persistence seam: how specification nodes and their evidence blobs are stored.
//!
//! Two responsibilities are split behind two traits so the graph topology and
//! the (potentially large) captured bytes can live in different systems and
//! scale independently:
//!
//!   * [`NodeStore`] — the specification nodes: identity, the raw sentence
//!     text with its language version, and embedded evidence *metadata*. The
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

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use thiserror::Error;

use crate::domain::{Edge, Node};

/// A bounded, keyset-paginated page of nodes.
///
/// The read path never materializes the whole graph; it hands back one page and
/// a cursor to resume from. `next_cursor` is `Some` while more pages remain and
/// `None` on the final page. Treat the cursor as opaque — it is the store's
/// resume key (today, the last node id), not a stable public handle.
pub struct NodePage {
    pub nodes: Vec<Node>,
    pub next_cursor: Option<String>,
}

/// Persists and retrieves individual specification nodes — the write seam the
/// ingest use case (`spec add`) needs, and nothing more.
///
/// This is deliberately narrow: reading the graph back is a separate concern
/// ([`GraphStore`]), so an ingest-only collaborator (a test fault-injector, a
/// write-only backend) is not forced to know about pagination. Growing the read
/// surface never disturbs this trait or its implementors.
pub trait NodeStore {
    /// Persist a node. Idempotent on the node id: re-persisting the same id
    /// replaces it with identical content.
    fn add_node(&self, node: &Node) -> Result<(), StoreError>;

    /// Fetch a node by id, or `None` if no such node exists.
    fn get_node(&self, id: &str) -> Result<Option<Node>, StoreError>;

    /// Remove a node by id. Idempotent: deleting an absent id succeeds.
    /// Ingest uses this to roll back already-persisted sentences when a later
    /// sentence of the same specification fails to persist.
    fn delete_node(&self, id: &str) -> Result<(), StoreError>;
}

/// Reads the graph topology back, a bounded page at a time.
///
/// Separated from [`NodeStore`] (which it extends) so only the graph read path
/// depends on it. It is deliberately paginated: the graph can hold billions of
/// nodes, so there is no "return everything" method — only [`list_nodes`], a
/// bounded keyset page. Edges have no producer yet (the model is all vertices),
/// but [`list_edges`] is present so the read is graph-shaped ahead of edge
/// derivation; it returns an empty set until an edge collection lands.
///
/// [`list_nodes`]: GraphStore::list_nodes
/// [`list_edges`]: GraphStore::list_edges
pub trait GraphStore: NodeStore {
    /// Read one bounded page of nodes, ordered by a stable key.
    ///
    /// Keyset pagination: `after` is the cursor from a prior page's
    /// `next_cursor` (`None` starts from the beginning), and `limit` bounds the
    /// page. Cost is independent of how deep the cursor sits — never an offset
    /// scan — so paging stays O(page) at any graph size. The returned page's
    /// `next_cursor` is `Some` iff at least one more node follows.
    fn list_nodes(&self, after: Option<&str>, limit: usize) -> Result<NodePage, StoreError>;

    /// Best-effort total node count for the whole graph. Must be cheap at any
    /// scale (a maintained count, never a full scan): it exists so a caller can
    /// show progress without ever fetching every node.
    fn count_nodes(&self) -> Result<u64, StoreError>;

    /// The edges induced among a set of nodes (both endpoints in `among`).
    ///
    /// Returns empty today — the model has no edges yet — but the seam is here
    /// so the read is graph-shaped: when refinement/composition/contradiction
    /// edges land, this returns the ones internal to the page the caller passes.
    fn list_edges(&self, among: &[String]) -> Result<Vec<Edge>, StoreError>;
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

/// A non-persistent, in-memory graph store — a first-class backend, not a test
/// helper. It implements the full seam ([`NodeStore`] + [`GraphStore`]) and is
/// selectable in `specd` (`--store memory`) to run the daemon without ArangoDB,
/// e.g. for local development, demos, or the graph UI. Its state lives only in
/// process memory and is lost on restart.
///
/// Backed by a `Mutex`-guarded `BTreeMap`: the mutex makes it `Send + Sync` (so
/// it can cross the daemon's `spawn_blocking` boundary, exactly as the ArangoDB
/// store does), and the `BTreeMap`'s sorted key order *is* the keyset order, so
/// pagination reads a contiguous range with no separate sort.
#[derive(Default)]
pub struct InMemoryNodeStore {
    nodes: Mutex<BTreeMap<String, Node>>,
}

impl InMemoryNodeStore {
    pub fn new() -> InMemoryNodeStore {
        InMemoryNodeStore::default()
    }

    /// Number of nodes held.
    pub fn len(&self) -> usize {
        self.nodes.lock().expect("node store mutex poisoned").len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes
            .lock()
            .expect("node store mutex poisoned")
            .is_empty()
    }
}

impl NodeStore for InMemoryNodeStore {
    fn add_node(&self, node: &Node) -> Result<(), StoreError> {
        self.nodes
            .lock()
            .expect("node store mutex poisoned")
            .insert(node.id.clone(), node.clone());
        Ok(())
    }

    fn get_node(&self, id: &str) -> Result<Option<Node>, StoreError> {
        Ok(self
            .nodes
            .lock()
            .expect("node store mutex poisoned")
            .get(id)
            .cloned())
    }

    fn delete_node(&self, id: &str) -> Result<(), StoreError> {
        self.nodes
            .lock()
            .expect("node store mutex poisoned")
            .remove(id);
        Ok(())
    }
}

impl GraphStore for InMemoryNodeStore {
    fn list_nodes(&self, after: Option<&str>, limit: usize) -> Result<NodePage, StoreError> {
        let nodes = self.nodes.lock().expect("node store mutex poisoned");
        // The BTreeMap iterates in sorted key order — the keyset order — so this
        // is a range scan from just past `after`. Take one past `limit` to learn
        // whether a further page exists, mirroring the ArangoDB backend.
        let mut page: Vec<Node> = nodes
            .range::<str, _>((cursor_bound(after), std::ops::Bound::Unbounded))
            .take(limit + 1)
            .map(|(_, node)| node.clone())
            .collect();
        let next_cursor = if page.len() > limit {
            page.truncate(limit);
            page.last().map(|n| n.id.clone())
        } else {
            None
        };
        Ok(NodePage {
            nodes: page,
            next_cursor,
        })
    }

    fn count_nodes(&self) -> Result<u64, StoreError> {
        Ok(self.nodes.lock().expect("node store mutex poisoned").len() as u64)
    }

    fn list_edges(&self, _among: &[String]) -> Result<Vec<Edge>, StoreError> {
        // No edges are produced yet; the graph is all vertices.
        Ok(Vec::new())
    }
}

/// The exclusive lower bound for a keyset scan: everything strictly after the
/// cursor, or the whole map when there is no cursor.
fn cursor_bound(after: Option<&str>) -> std::ops::Bound<&str> {
    match after {
        Some(cursor) => std::ops::Bound::Excluded(cursor),
        None => std::ops::Bound::Unbounded,
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

        let store = InMemoryNodeStore::new();
        let node = Node {
            id: "n1".to_string(),
            statement: "The pump shall stop.".to_string(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
            },
        };
        store.add_node(&node).unwrap();
        assert_eq!(store.get_node("n1").unwrap().as_ref(), Some(&node));
        assert!(store.get_node("absent").unwrap().is_none());
    }

    fn node_with_id(id: &str) -> crate::domain::Node {
        use crate::domain::{Meta, Node};
        Node {
            id: id.to_string(),
            statement: "The pump shall stop.".to_string(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
            },
        }
    }

    #[test]
    fn list_nodes_pages_by_keyset_covering_every_node_once() {
        let store = InMemoryNodeStore::new();
        // Insert out of order; paging must still be by sorted key.
        for id in ["n03", "n01", "n05", "n02", "n04"] {
            store.add_node(&node_with_id(id)).unwrap();
        }

        // Walk the whole graph in pages of 2, following the cursor.
        let mut seen = Vec::new();
        let mut cursor: Option<String> = None;
        let mut pages = 0;
        loop {
            let page = store.list_nodes(cursor.as_deref(), 2).unwrap();
            assert!(page.nodes.len() <= 2, "a page never exceeds the limit");
            seen.extend(page.nodes.iter().map(|n| n.id.clone()));
            pages += 1;
            match page.next_cursor {
                Some(c) => cursor = Some(c),
                None => break,
            }
            assert!(pages < 10, "cursor must terminate");
        }

        // Every node exactly once, in sorted order, no duplicates across pages.
        assert_eq!(seen, ["n01", "n02", "n03", "n04", "n05"]);
        assert_eq!(pages, 3); // 2 + 2 + 1
    }

    #[test]
    fn list_nodes_cursor_terminates_on_exact_multiple() {
        let store = InMemoryNodeStore::new();
        for id in ["a", "b", "c", "d"] {
            store.add_node(&node_with_id(id)).unwrap();
        }
        // A full page whose successor is empty: the cursor may be Some here, but
        // following it yields an empty final page with no further cursor.
        let first = store.list_nodes(None, 4).unwrap();
        assert_eq!(first.nodes.len(), 4);
        assert!(first.next_cursor.is_none(), "exact fill has no next page");
    }

    #[test]
    fn list_nodes_from_cursor_excludes_the_cursor_itself() {
        let store = InMemoryNodeStore::new();
        for id in ["a", "b", "c"] {
            store.add_node(&node_with_id(id)).unwrap();
        }
        let page = store.list_nodes(Some("a"), 10).unwrap();
        let ids: Vec<&str> = page.nodes.iter().map(|n| n.id.as_str()).collect();
        assert_eq!(ids, ["b", "c"]);
    }

    #[test]
    fn count_nodes_tracks_inserts() {
        let store = InMemoryNodeStore::new();
        assert_eq!(store.count_nodes().unwrap(), 0);
        store.add_node(&node_with_id("a")).unwrap();
        store.add_node(&node_with_id("b")).unwrap();
        assert_eq!(store.count_nodes().unwrap(), 2);
    }

    #[test]
    fn list_edges_is_empty_until_edges_exist() {
        let store = InMemoryNodeStore::new();
        store.add_node(&node_with_id("a")).unwrap();
        assert!(store
            .list_edges(&["a".to_string()])
            .unwrap()
            .is_empty());
    }
}
