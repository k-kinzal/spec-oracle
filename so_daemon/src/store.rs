//! Persistence seam: how specification nodes and their evidence blobs are stored.
//!
//! Two responsibilities are split behind two traits so the graph topology and
//! the (potentially large) captured bytes can live in different systems and
//! scale independently:
//!
//!   * [`NodeStore`] — the authored specification nodes: identity, the raw sentence
//!     text with its language version, and embedded evidence *metadata*. The
//!     production implementation is [`crate::arango::ArangoNodeStore`], a graph
//!     database chosen so the same product scales from a laptop to a cluster by
//!     relocation rather than by swapping engines.
//!   * [`BlobStore`] — the content-addressed snapshot bytes, kept out of the
//!     graph so the topology stays small and the bytes can sit in cheap object
//!     storage.
//!
//! Captured Evidence and ingest Assumption/Guarantee values also become shared
//! content-addressed vertices through [`GraphStore`]. A specification node
//! document therefore carries only a `snapshot.content_hash` pointer into
//! the blob store; the captured bytes themselves are never written into the
//! graph (`Snapshot::content` is `#[serde(skip)]`).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use thiserror::Error;

use crate::domain::{
    DerivedNode, Edge, EdgeKind, MetaUpdate, Node, RelationAssessment, SelectionPopulation,
    TermNode,
};

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

/// A bounded, keyset-paginated page of immutable Ledger Edges.
pub struct EdgePage {
    pub edges: Vec<Edge>,
    pub next_cursor: Option<String>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GraphWrite {
    pub term_inserted: bool,
    pub edge_inserted: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DerivedGraphWrite {
    pub node_inserted: bool,
    pub edge_inserted: bool,
}

/// Persists and retrieves individual specification nodes — the write seam the
/// ingest use case (`spec add`) needs, and nothing more.
///
/// This is deliberately narrow: reading the graph back is a separate concern
/// ([`GraphStore`]), so an ingest-only collaborator (a test fault-injector, a
/// write-only backend) is not forced to know about pagination. Growing the read
/// surface never disturbs this trait or its implementors.
pub trait NodeStore {
    /// Persist an immutable accepted Node. Idempotent on Node id: re-executing
    /// the same Add command is a no-op and cannot erase later Consumer results.
    fn add_node(&self, node: &Node) -> Result<bool, StoreError>;

    /// Find the selected existing Node with identical authored content. This
    /// keeps content deduplication compatible with rows created before Node ids
    /// became content-addressed.
    fn find_node(&self, statement: &str, lang_version: &str) -> Result<Option<Node>, StoreError>;

    /// Merge retryable Evidence descriptors into an existing Specification
    /// Node and return its current stored state. Repeated descriptors are a
    /// no-op; new descriptors make Evidence capture reconcilable without
    /// creating another authored Node.
    fn merge_evidence_requests(
        &self,
        node_id: &str,
        requests: &[String],
    ) -> Result<Node, StoreError>;

    /// Replace the complete desired Evidence descriptor set and append the
    /// request-generation update atomically. This is the explicit freshness
    /// boundary: later capture replaces the convenient current Evidence view,
    /// while prior Evidence Nodes and GroundedBy Edges remain in the Ledger.
    fn replace_evidence_requests(
        &self,
        node_id: &str,
        requests: &[String],
        update_id: &str,
        update: &MetaUpdate,
    ) -> Result<Node, StoreError>;

    /// Fetch a node by id, or `None` if no such node exists.
    fn get_node(&self, id: &str) -> Result<Option<Node>, StoreError>;

    /// Atomically persist one successful Command update and, for Evidence capture,
    /// replace the current captured-evidence view. The versioned update
    /// retains the complete capture as append-only history.
    fn apply_command_update(
        &self,
        node_id: &str,
        command_id: &str,
        update: &MetaUpdate,
        evidence: Option<&[crate::domain::Evidence]>,
    ) -> Result<(), StoreError>;
}

/// Reads the graph topology back, a bounded page at a time.
///
/// Separated from [`NodeStore`] (which it extends) so only the graph read path
/// depends on it. It is deliberately paginated: the graph can hold billions of
/// nodes, so there is no "return everything" method — only [`list_nodes`], a
/// bounded keyset page. Derived term, Evidence, Assumption, and Guarantee
/// vertices and the selected current versions of their Edges are exposed
/// alongside each specification page.
///
/// [`list_nodes`]: GraphStore::list_nodes
/// [`list_edges`]: GraphStore::list_edges
pub trait GraphStore: NodeStore {
    /// Idempotently persist one derived term form and the specification's
    /// anchored mention edge to it.
    fn put_term_mention(&self, term: &TermNode, edge: &Edge) -> Result<GraphWrite, StoreError>;

    /// Idempotently persist one content-addressed Evidence, Assumption, or
    /// Guarantee node and the projection edge that connects it to a
    /// specification.
    fn put_derived_node(
        &self,
        node: &DerivedNode,
        edge: &Edge,
    ) -> Result<DerivedGraphWrite, StoreError>;

    /// Idempotently append one graph-established edge. Stable derivation-derived
    /// ids turn retries into no-ops; a changed derivation version creates new
    /// history rather than overwriting old topology.
    fn append_edge(&self, edge: &Edge) -> Result<bool, StoreError>;

    /// Fetch one immutable Ledger Edge by its content-derived id.
    fn get_edge(&self, id: &str) -> Result<Option<Edge>, StoreError>;

    /// Read append-only Ledger topology by Edge id, independently of current
    /// derivation selection. This is the historical audit surface.
    fn list_ledger_edges(&self, after: Option<&str>, limit: usize) -> Result<EdgePage, StoreError>;

    /// Cheap maintained Ledger Edge count.
    fn count_edges(&self) -> Result<u64, StoreError>;

    /// Idempotently append an audit record for an assessed candidate pair.
    /// These records include `Unknown` and `Independent` but are never exposed
    /// as graph topology.
    fn append_relation_assessment(
        &self,
        assessment: &RelationAssessment,
    ) -> Result<bool, StoreError>;

    fn get_relation_assessment(&self, id: &str) -> Result<Option<RelationAssessment>, StoreError>;

    /// Audit records canonically owned by the supplied specification ids.
    fn list_relation_assessments(
        &self,
        owners: &[String],
    ) -> Result<Vec<RelationAssessment>, StoreError>;

    fn get_term_nodes(&self, ids: &[String]) -> Result<Vec<TermNode>, StoreError>;

    fn get_derived_nodes(&self, ids: &[String]) -> Result<Vec<DerivedNode>, StoreError>;

    /// Return a bounded, keyset page of specification Nodes that mention any
    /// supplied term under the selected lexical derivation. This is a
    /// versioned candidate search, not a semantic judgment: omitted Nodes are
    /// unsearched, and a returned Node may still assess to `Unknown`.
    fn list_term_candidates(
        &self,
        term_ids: &[String],
        term_derivation: &crate::domain::Derivation,
        exclude_node_id: &str,
        after: Option<&str>,
        limit: usize,
    ) -> Result<NodePage, StoreError>;

    /// Read one bounded page of nodes, ordered by a stable key.
    ///
    /// Keyset pagination: `after` is the cursor from a prior page's
    /// `next_cursor` (`None` starts from the beginning), and `limit` bounds the
    /// page. Cost is independent of how deep the cursor sits — never an offset
    /// scan — so paging stays O(page) at any graph size. The returned page's
    /// `next_cursor` is `Some` iff at least one more node follows.
    fn list_nodes(&self, after: Option<&str>, limit: usize) -> Result<NodePage, StoreError>;

    /// Best-effort total count of authored specification nodes. Must be cheap
    /// at any scale (a maintained count, never a full scan): derived historical
    /// vertices do not distort specification-page progress.
    fn count_nodes(&self) -> Result<u64, StoreError>;

    /// Read the complete current dependency closure for the supplied Nodes:
    /// semantic competitors, incoming explicit selection judgments and
    /// supporters, their own competitors and selection sources, and the direct
    /// Evidence needed to evaluate them. Whole-closure selection prevents a
    /// rejected intermediary or receded relationship from affecting a current
    /// candidate invisibly.
    fn selection_population(
        &self,
        node_ids: &[String],
        current_derivations: &[crate::domain::Derivation],
    ) -> Result<SelectionPopulation, StoreError>;

    /// Current assume-guarantee pairing Edges directed into one target
    /// contract. The native inbound lookup keeps aggregate pairing validation
    /// proportional to that contract's actual dependencies, not Ledger size.
    fn list_pairing_edges(
        &self,
        target: &str,
        derivation: &crate::domain::Derivation,
    ) -> Result<Vec<Edge>, StoreError>;

    /// Current derived Edges owned by a specification page. The current set is
    /// selected independently for each derivation method. Mention Edges are
    /// owned by their mentioner; semantic and selection Edges by the lexically
    /// smaller endpoint, so a complete Node-page walk returns each Edge once.
    fn list_edges(
        &self,
        owners: &[String],
        current_derivations: &[crate::domain::Derivation],
    ) -> Result<Vec<Edge>, StoreError>;
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
    #[error("node '{0}' does not exist")]
    MissingNode(String),
    #[error("invalid graph Edge: {0}")]
    InvalidEdge(String),
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
    terms: Mutex<BTreeMap<String, TermNode>>,
    derived_nodes: Mutex<BTreeMap<String, DerivedNode>>,
    edges: Mutex<EdgeState>,
    assessments: Mutex<BTreeMap<String, RelationAssessment>>,
}

#[derive(Default)]
struct EdgeState {
    by_identity: BTreeMap<String, Edge>,
    identity_by_id: BTreeMap<String, String>,
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
    fn add_node(&self, node: &Node) -> Result<bool, StoreError> {
        let mut nodes = self.nodes.lock().expect("node store mutex poisoned");
        if nodes.contains_key(&node.id) {
            Ok(false)
        } else {
            nodes.insert(node.id.clone(), node.clone());
            Ok(true)
        }
    }

    fn find_node(&self, statement: &str, lang_version: &str) -> Result<Option<Node>, StoreError> {
        Ok(self
            .nodes
            .lock()
            .expect("node store mutex poisoned")
            .values()
            .find(|node| node.statement == statement && node.lang_version == lang_version)
            .cloned())
    }

    fn merge_evidence_requests(
        &self,
        node_id: &str,
        requests: &[String],
    ) -> Result<Node, StoreError> {
        let mut nodes = self.nodes.lock().expect("node store mutex poisoned");
        let node = nodes
            .get_mut(node_id)
            .ok_or_else(|| StoreError::MissingNode(node_id.to_string()))?;
        node.meta.evidence_requests.extend(requests.iter().cloned());
        node.meta.evidence_requests.sort();
        node.meta.evidence_requests.dedup();
        Ok(node.clone())
    }

    fn replace_evidence_requests(
        &self,
        node_id: &str,
        requests: &[String],
        update_id: &str,
        update: &MetaUpdate,
    ) -> Result<Node, StoreError> {
        let mut nodes = self.nodes.lock().expect("node store mutex poisoned");
        let node = nodes
            .get_mut(node_id)
            .ok_or_else(|| StoreError::MissingNode(node_id.to_string()))?;
        node.meta.evidence_requests = requests.to_vec();
        node.meta.evidence_requests.sort();
        node.meta.evidence_requests.dedup();
        node.meta.evidence_request_generation = update_id.to_string();
        if node.meta.evidence_requests.is_empty() {
            node.meta.evidence.clear();
        }
        node.meta
            .updates
            .insert(update_id.to_string(), update.clone());
        Ok(node.clone())
    }

    fn get_node(&self, id: &str) -> Result<Option<Node>, StoreError> {
        Ok(self
            .nodes
            .lock()
            .expect("node store mutex poisoned")
            .get(id)
            .cloned())
    }

    fn apply_command_update(
        &self,
        node_id: &str,
        command_id: &str,
        update: &MetaUpdate,
        evidence: Option<&[crate::domain::Evidence]>,
    ) -> Result<(), StoreError> {
        let mut nodes = self.nodes.lock().expect("node store mutex poisoned");
        let node = nodes
            .get_mut(node_id)
            .ok_or_else(|| StoreError::MissingNode(node_id.to_string()))?;
        if let Some(evidence) = evidence {
            node.meta.evidence = evidence.to_vec();
        }
        node.meta
            .updates
            .insert(command_id.to_string(), update.clone());
        Ok(())
    }
}

impl GraphStore for InMemoryNodeStore {
    fn put_term_mention(&self, term: &TermNode, edge: &Edge) -> Result<GraphWrite, StoreError> {
        edge.validate().map_err(StoreError::InvalidEdge)?;
        let term_inserted = self
            .terms
            .lock()
            .expect("term store mutex poisoned")
            .insert(term.id.clone(), term.clone())
            .is_none();
        let edge_inserted = insert_edge(
            &mut self.edges.lock().expect("edge store mutex poisoned"),
            edge,
        )?;
        Ok(GraphWrite {
            term_inserted,
            edge_inserted,
        })
    }

    fn put_derived_node(
        &self,
        node: &DerivedNode,
        edge: &Edge,
    ) -> Result<DerivedGraphWrite, StoreError> {
        edge.validate().map_err(StoreError::InvalidEdge)?;
        if edge.target != node.id() || edge.target_kind != node.vertex_kind() {
            return Err(StoreError::InvalidEdge(format!(
                "derived edge target '{}:{:?}' does not match node '{}:{:?}'",
                edge.target,
                edge.target_kind,
                node.id(),
                node.vertex_kind()
            )));
        }
        let mut nodes = self
            .derived_nodes
            .lock()
            .expect("derived node store mutex poisoned");
        let node_inserted = if nodes.contains_key(node.id()) {
            false
        } else {
            nodes.insert(node.id().to_string(), node.clone());
            true
        };
        drop(nodes);
        let edge_inserted = insert_edge(
            &mut self.edges.lock().expect("edge store mutex poisoned"),
            edge,
        )?;
        Ok(DerivedGraphWrite {
            node_inserted,
            edge_inserted,
        })
    }

    fn append_edge(&self, edge: &Edge) -> Result<bool, StoreError> {
        edge.validate().map_err(StoreError::InvalidEdge)?;
        insert_edge(
            &mut self.edges.lock().expect("edge store mutex poisoned"),
            edge,
        )
    }

    fn get_edge(&self, id: &str) -> Result<Option<Edge>, StoreError> {
        let edges = self.edges.lock().expect("edge store mutex poisoned");
        let Some(identity) = edges.identity_by_id.get(id) else {
            return Ok(None);
        };
        Ok(edges.by_identity.get(identity).cloned())
    }

    fn list_ledger_edges(&self, after: Option<&str>, limit: usize) -> Result<EdgePage, StoreError> {
        let edges = self.edges.lock().expect("edge store mutex poisoned");
        let mut ids: Vec<String> = edges
            .identity_by_id
            .range::<str, _>((cursor_bound(after), std::ops::Bound::Unbounded))
            .take(limit.saturating_add(1))
            .map(|(id, _)| id.clone())
            .collect();
        let next_cursor = if ids.len() > limit {
            ids.truncate(limit);
            ids.last().cloned()
        } else {
            None
        };
        let rows = ids
            .into_iter()
            .filter_map(|id| {
                edges
                    .identity_by_id
                    .get(&id)
                    .and_then(|identity| edges.by_identity.get(identity))
                    .cloned()
            })
            .collect();
        Ok(EdgePage {
            edges: rows,
            next_cursor,
        })
    }

    fn count_edges(&self) -> Result<u64, StoreError> {
        Ok(self
            .edges
            .lock()
            .expect("edge store mutex poisoned")
            .by_identity
            .len() as u64)
    }

    fn append_relation_assessment(
        &self,
        assessment: &RelationAssessment,
    ) -> Result<bool, StoreError> {
        let mut assessments = self
            .assessments
            .lock()
            .expect("assessment store mutex poisoned");
        if assessments.contains_key(&assessment.id) {
            Ok(false)
        } else {
            assessments.insert(assessment.id.clone(), assessment.clone());
            Ok(true)
        }
    }

    fn get_relation_assessment(&self, id: &str) -> Result<Option<RelationAssessment>, StoreError> {
        Ok(self
            .assessments
            .lock()
            .expect("assessment store mutex poisoned")
            .get(id)
            .cloned())
    }

    fn list_relation_assessments(
        &self,
        owners: &[String],
    ) -> Result<Vec<RelationAssessment>, StoreError> {
        let owners: std::collections::BTreeSet<&str> = owners.iter().map(String::as_str).collect();
        Ok(self
            .assessments
            .lock()
            .expect("assessment store mutex poisoned")
            .values()
            .filter(|assessment| owners.contains(assessment.left.as_str()))
            .cloned()
            .collect())
    }

    fn get_term_nodes(&self, ids: &[String]) -> Result<Vec<TermNode>, StoreError> {
        let terms = self.terms.lock().expect("term store mutex poisoned");
        Ok(ids.iter().filter_map(|id| terms.get(id).cloned()).collect())
    }

    fn get_derived_nodes(&self, ids: &[String]) -> Result<Vec<DerivedNode>, StoreError> {
        let nodes = self
            .derived_nodes
            .lock()
            .expect("derived node store mutex poisoned");
        Ok(ids.iter().filter_map(|id| nodes.get(id).cloned()).collect())
    }

    fn list_term_candidates(
        &self,
        term_ids: &[String],
        term_derivation: &crate::domain::Derivation,
        exclude_node_id: &str,
        after: Option<&str>,
        limit: usize,
    ) -> Result<NodePage, StoreError> {
        let terms: std::collections::BTreeSet<&str> = term_ids.iter().map(String::as_str).collect();
        let candidate_ids: std::collections::BTreeSet<String> = self
            .edges
            .lock()
            .expect("edge store mutex poisoned")
            .by_identity
            .values()
            .filter(|edge| {
                edge.kind == EdgeKind::MentionsTerm
                    && edge.source_role == crate::domain::EndpointRole::Mentioner
                    && edge.target_role == crate::domain::EndpointRole::MentionedTerm
                    && edge.derivation == *term_derivation
                    && edge.source != exclude_node_id
                    && terms.contains(edge.target.as_str())
            })
            .map(|edge| edge.source.clone())
            .collect();
        let mut ids: Vec<String> = candidate_ids
            .into_iter()
            .filter(|id| after.is_none_or(|cursor| id.as_str() > cursor))
            .take(limit.saturating_add(1))
            .collect();
        let next_cursor = if ids.len() > limit {
            ids.truncate(limit);
            ids.last().cloned()
        } else {
            None
        };
        let nodes = self.nodes.lock().expect("node store mutex poisoned");
        Ok(NodePage {
            nodes: ids
                .into_iter()
                .filter_map(|id| nodes.get(&id).cloned())
                .collect(),
            next_cursor,
        })
    }

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

    fn selection_population(
        &self,
        node_ids: &[String],
        current_derivations: &[crate::domain::Derivation],
    ) -> Result<SelectionPopulation, StoreError> {
        let edges = self.edges.lock().expect("edge store mutex poisoned");
        let current: Vec<&Edge> = edges
            .by_identity
            .values()
            .filter(|edge| current_derivations.contains(&edge.derivation))
            .collect();
        let mut component_ids: std::collections::BTreeSet<String> =
            node_ids.iter().cloned().collect();
        let mut relations = BTreeMap::new();
        loop {
            let mut expanded = false;
            let adjacent: Vec<&Edge> = current
                .iter()
                .copied()
                .filter(|edge| {
                    edge.kind.family() == crate::domain::EdgeFamily::Semantic
                        && crate::selection::is_semantic_competition(edge.kind)
                        && (component_ids.contains(&edge.source)
                            || component_ids.contains(&edge.target))
                })
                .collect();
            for edge in adjacent {
                expanded |= component_ids.insert(edge.source.clone());
                expanded |= component_ids.insert(edge.target.clone());
                relations.insert(edge.id.clone(), edge.clone());
            }
            if !expanded {
                break;
            }
        }
        let mut scored_ids = component_ids;
        for edge in relations.values() {
            scored_ids.insert(edge.source.clone());
            scored_ids.insert(edge.target.clone());
        }
        let current_evidence: BTreeMap<String, std::collections::BTreeSet<String>> = self
            .nodes
            .lock()
            .expect("node store mutex poisoned")
            .values()
            .filter(|node| scored_ids.contains(&node.id))
            .filter_map(|node| {
                crate::selection::current_evidence_node_ids(node).map(|ids| (node.id.clone(), ids))
            })
            .collect();
        let evidence_edges: Vec<Edge> = current
            .iter()
            .copied()
            .filter(|edge| {
                edge.kind == EdgeKind::GroundedBy
                    && scored_ids.contains(edge.source.as_str())
                    && current_evidence
                        .get(&edge.source)
                        .is_none_or(|ids| ids.contains(&edge.target))
            })
            .cloned()
            .collect();
        drop(edges);
        let evidence_ids: std::collections::BTreeSet<&str> = evidence_edges
            .iter()
            .map(|edge| edge.target.as_str())
            .collect();
        let evidence_nodes = self
            .derived_nodes
            .lock()
            .expect("derived node store mutex poisoned")
            .values()
            .filter(|node| evidence_ids.contains(node.id()))
            .cloned()
            .collect();
        Ok(SelectionPopulation {
            relation_edges: relations.into_values().collect(),
            evidence_edges,
            evidence_nodes,
        })
    }

    fn list_pairing_edges(
        &self,
        target: &str,
        derivation: &crate::domain::Derivation,
    ) -> Result<Vec<Edge>, StoreError> {
        Ok(self
            .edges
            .lock()
            .expect("edge store mutex poisoned")
            .by_identity
            .values()
            .filter(|edge| {
                edge.target == target && edge.derivation == *derivation && edge.kind.is_pairing()
            })
            .cloned()
            .collect())
    }

    fn list_edges(
        &self,
        owners: &[String],
        current_derivations: &[crate::domain::Derivation],
    ) -> Result<Vec<Edge>, StoreError> {
        let owners: std::collections::BTreeSet<&str> = owners.iter().map(String::as_str).collect();
        let edge_guard = self.edges.lock().expect("edge store mutex poisoned");
        let current: Vec<Edge> = edge_guard
            .by_identity
            .values()
            .filter(|edge| current_derivations.contains(&edge.derivation))
            .cloned()
            .collect();
        let edges: Vec<Edge> = current
            .iter()
            .filter(|edge| owners.contains(edge.page_owner()))
            .cloned()
            .collect();
        let contract_context: Vec<Edge> = current
            .into_iter()
            .filter(|edge| {
                edge.kind == EdgeKind::HasContract || is_contract_operation_edge(edge.kind)
            })
            .collect();
        drop(edge_guard);
        let current_evidence: BTreeMap<String, std::collections::BTreeSet<String>> = self
            .nodes
            .lock()
            .expect("node store mutex poisoned")
            .values()
            .filter_map(|node| {
                crate::selection::current_evidence_node_ids(node).map(|ids| (node.id.clone(), ids))
            })
            .collect();
        Ok(select_current_contract_graph(
            select_current_assumption_projections(edges),
            &contract_context,
        )
        .into_iter()
        .filter(|edge| {
            edge.kind != EdgeKind::GroundedBy
                || current_evidence
                    .get(&edge.source)
                    .is_none_or(|ids| ids.contains(&edge.target))
        })
        .collect())
    }
}

fn is_contract_operation_edge(kind: EdgeKind) -> bool {
    matches!(
        kind,
        EdgeKind::CompositionOperand
            | EdgeKind::QuotientDividend
            | EdgeKind::QuotientDivisor
            | EdgeKind::MergeOperand
    )
}

/// Select the active content-addressed contract subgraph. A changed paired
/// assumption selects a new HasContract target; semantic edges about the old
/// target remain Ledger facts but recede from the current graph. Explicit
/// algebra results remain active only while all of their operand contracts are
/// active.
pub(crate) fn select_current_contract_graph(visible: Vec<Edge>, context: &[Edge]) -> Vec<Edge> {
    let selected_projections = select_current_contract_projections(context.to_vec());
    let selected_ids: std::collections::BTreeSet<&str> = selected_projections
        .iter()
        .filter(|edge| edge.kind == EdgeKind::HasContract)
        .map(|edge| edge.id.as_str())
        .collect();
    let mut active: std::collections::BTreeSet<String> = selected_projections
        .iter()
        .filter(|edge| edge.kind == EdgeKind::HasContract)
        .map(|edge| edge.target.clone())
        .collect();

    loop {
        let mut changed = false;
        let mut by_result: BTreeMap<&str, Vec<&Edge>> = BTreeMap::new();
        for edge in context
            .iter()
            .filter(|edge| is_contract_operation_edge(edge.kind))
        {
            by_result
                .entry(edge.target.as_str())
                .or_default()
                .push(edge);
        }
        for (result, operands) in by_result {
            if operands
                .iter()
                .all(|edge| active.contains(edge.source.as_str()))
            {
                changed |= active.insert(result.to_string());
            }
        }
        if !changed {
            break;
        }
    }

    visible
        .into_iter()
        .filter(|edge| match edge.kind {
            EdgeKind::HasContract => selected_ids.contains(edge.id.as_str()),
            EdgeKind::ContractRefines | EdgeKind::ContractEquivalent => {
                active.contains(edge.source.as_str()) && active.contains(edge.target.as_str())
            }
            kind if is_contract_operation_edge(kind) => {
                active.contains(edge.source.as_str()) && active.contains(edge.target.as_str())
            }
            _ => true,
        })
        .collect()
}

pub(crate) fn select_current_contract_projections(edges: Vec<Edge>) -> Vec<Edge> {
    let mut selected: BTreeMap<String, (u8, usize, String, String)> = BTreeMap::new();
    for edge in &edges {
        if edge.kind != EdgeKind::HasContract {
            continue;
        }
        let preference = (
            u8::from(edge.derivation.method == crate::pairing::PAIRED_PROJECTION_METHOD),
            edge.basis_spec_ids.len(),
            edge.recorded_at.clone(),
            edge.id.clone(),
        );
        let slot = selected
            .entry(edge.source.clone())
            .or_insert_with(|| preference.clone());
        if preference > *slot {
            *slot = preference;
        }
    }
    edges
        .into_iter()
        .filter(|edge| {
            edge.kind != EdgeKind::HasContract
                || selected
                    .get(&edge.source)
                    .is_some_and(|choice| choice.3 == edge.id)
        })
        .collect()
}

/// A paired (A,G) supersedes the provisional ingest (Top,G) projection in the
/// current view while both remain in the append-only Ledger. Within paired
/// projections, a larger authored basis is the later aggregate; stable time/id
/// tie-breakers handle equal-size alternatives deterministically.
pub(crate) fn select_current_assumption_projections(edges: Vec<Edge>) -> Vec<Edge> {
    let mut selected: BTreeMap<String, (u8, usize, String, String)> = BTreeMap::new();
    for edge in &edges {
        if edge.kind != EdgeKind::HasAssumption {
            continue;
        }
        let preference = (
            u8::from(edge.derivation.method == crate::pairing::PAIRED_PROJECTION_METHOD),
            edge.basis_spec_ids.len(),
            edge.recorded_at.clone(),
            edge.id.clone(),
        );
        let slot = selected
            .entry(edge.source.clone())
            .or_insert_with(|| preference.clone());
        if preference > *slot {
            *slot = preference;
        }
    }
    edges
        .into_iter()
        .filter(|edge| {
            edge.kind != EdgeKind::HasAssumption
                || selected
                    .get(&edge.source)
                    .is_some_and(|choice| choice.3 == edge.id)
        })
        .collect()
}

fn insert_edge(state: &mut EdgeState, edge: &Edge) -> Result<bool, StoreError> {
    let identity = edge.identity_key();
    if state.by_identity.contains_key(&identity) {
        return Ok(false);
    }
    if let Some(existing_identity) = state.identity_by_id.get(&edge.id) {
        return Err(StoreError::InvalidEdge(format!(
            "Edge id '{}' is already used by a different relationship ({existing_identity})",
            edge.id
        )));
    }
    state
        .identity_by_id
        .insert(edge.id.clone(), identity.clone());
    state.by_identity.insert(identity, edge.clone());
    Ok(true)
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
                evidence_requests: vec![],
                evidence_request_generation: String::new(),
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
                updates: Default::default(),
            },
        };
        store.add_node(&node).unwrap();
        assert_eq!(store.get_node("n1").unwrap().as_ref(), Some(&node));
        assert!(store.get_node("absent").unwrap().is_none());
    }

    #[test]
    fn meta_update_is_idempotent_on_command_id() {
        use crate::domain::MetaUpdate;

        let store = InMemoryNodeStore::new();
        store.add_node(&node_with_id("n1")).unwrap();
        let first = MetaUpdate {
            source: "example".to_string(),
            applied_at: "t1".to_string(),
            value: serde_json::json!({"attempt": 1}),
        };
        let second = MetaUpdate {
            source: "example".to_string(),
            applied_at: "t2".to_string(),
            value: serde_json::json!({"attempt": 2}),
        };
        store
            .apply_command_update("n1", "command-1", &first, None)
            .unwrap();
        store
            .apply_command_update("n1", "command-1", &second, None)
            .unwrap();

        let node = store.get_node("n1").unwrap().unwrap();
        assert_eq!(node.meta.updates.len(), 1);
        assert_eq!(node.meta.updates["command-1"], second);

        // Re-executing the originating Add command must not erase a Consumer result.
        store.add_node(&node_with_id("n1")).unwrap();
        let node = store.get_node("n1").unwrap().unwrap();
        assert_eq!(node.meta.updates["command-1"], second);
    }

    fn node_with_id(id: &str) -> crate::domain::Node {
        use crate::domain::{Meta, Node};
        Node {
            id: id.to_string(),
            statement: "The pump shall stop.".to_string(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence_requests: vec![],
                evidence_request_generation: String::new(),
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
                updates: Default::default(),
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
    fn graph_structure_is_idempotent_and_page_edges_are_queryable() {
        let store = InMemoryNodeStore::new();
        store.add_node(&node_with_id("a")).unwrap();
        let term = TermNode {
            id: "term-stop".into(),
            form: "stop command".into(),
            head: "command".into(),
            lang_version: "v".into(),
            derivation_version: "g1".into(),
        };
        let edge = Edge {
            id: "mention-a-stop".into(),
            source: "a".into(),
            source_kind: crate::domain::VertexKind::Specification,
            source_role: crate::domain::EndpointRole::Mentioner,
            target: term.id.clone(),
            target_kind: crate::domain::VertexKind::Term,
            target_role: crate::domain::EndpointRole::MentionedTerm,
            kind: EdgeKind::MentionsTerm,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: None,
            basis_spec_ids: vec![],
            derivation: crate::domain::Derivation {
                method: "test".into(),
                version: "g1".into(),
            },
            recorded_at: "t".into(),
        };
        assert_eq!(
            store.put_term_mention(&term, &edge).unwrap(),
            GraphWrite {
                term_inserted: true,
                edge_inserted: true
            }
        );
        assert_eq!(
            store.put_term_mention(&term, &edge).unwrap(),
            GraphWrite::default()
        );
        assert_eq!(
            store
                .list_edges(&["a".into()], std::slice::from_ref(&edge.derivation))
                .unwrap(),
            vec![edge]
        );
    }

    #[test]
    fn term_candidate_search_is_versioned_deduplicated_and_paginated() {
        let store = InMemoryNodeStore::new();
        for id in ["a", "b", "c"] {
            store.add_node(&node_with_id(id)).unwrap();
        }
        let derivation = crate::domain::Derivation {
            method: "term-search".into(),
            version: "v1".into(),
        };
        for (id, target) in [("ma1", "t1"), ("ma2", "t2"), ("mb", "t1"), ("mc", "t1")] {
            let source = if id.starts_with("ma") {
                "a"
            } else if id == "mb" {
                "b"
            } else {
                "c"
            };
            let term = TermNode {
                id: target.into(),
                form: target.into(),
                head: target.into(),
                lang_version: "v".into(),
                derivation_version: "v1".into(),
            };
            let mention = Edge {
                id: id.into(),
                source: source.into(),
                source_kind: crate::domain::VertexKind::Specification,
                source_role: crate::domain::EndpointRole::Mentioner,
                target: target.into(),
                target_kind: crate::domain::VertexKind::Term,
                target_role: crate::domain::EndpointRole::MentionedTerm,
                kind: EdgeKind::MentionsTerm,
                source_anchor: None,
                target_anchor: None,
                relied_spec_id: None,
                basis_spec_ids: vec![],
                derivation: derivation.clone(),
                recorded_at: "t".into(),
            };
            store.put_term_mention(&term, &mention).unwrap();
        }

        let first = store
            .list_term_candidates(&["t1".into(), "t2".into()], &derivation, "c", None, 1)
            .unwrap();
        assert_eq!(
            first
                .nodes
                .iter()
                .map(|n| n.id.as_str())
                .collect::<Vec<_>>(),
            ["a"]
        );
        let second = store
            .list_term_candidates(
                &["t1".into(), "t2".into()],
                &derivation,
                "c",
                first.next_cursor.as_deref(),
                1,
            )
            .unwrap();
        assert_eq!(
            second
                .nodes
                .iter()
                .map(|n| n.id.as_str())
                .collect::<Vec<_>>(),
            ["b"]
        );
        assert!(second.next_cursor.is_none());

        let wrong_version = crate::domain::Derivation {
            version: "v2".into(),
            ..derivation
        };
        assert!(store
            .list_term_candidates(&["t1".into()], &wrong_version, "c", None, 10)
            .unwrap()
            .nodes
            .is_empty());
    }

    #[test]
    fn semantic_edge_is_returned_once_on_lexical_owner_page() {
        let store = InMemoryNodeStore::new();
        store.add_node(&node_with_id("a")).unwrap();
        store.add_node(&node_with_id("z")).unwrap();
        let derivation = crate::domain::Derivation {
            method: "semantic".into(),
            version: "v1".into(),
        };
        let edge = Edge {
            id: "refines-z-a".into(),
            source: "z".into(),
            source_kind: crate::domain::VertexKind::Specification,
            source_role: crate::domain::EndpointRole::Refiner,
            target: "a".into(),
            target_kind: crate::domain::VertexKind::Specification,
            target_role: crate::domain::EndpointRole::Refined,
            kind: EdgeKind::Refines,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: None,
            basis_spec_ids: vec![],
            derivation: derivation.clone(),
            recorded_at: "t".into(),
        };
        store.append_edge(&edge).unwrap();
        assert_eq!(
            store
                .list_edges(&["a".into()], std::slice::from_ref(&derivation))
                .unwrap(),
            [edge]
        );
        let old = crate::domain::Derivation {
            method: "semantic".into(),
            version: "old".into(),
        };
        assert!(store.list_edges(&["a".into()], &[old]).unwrap().is_empty());
        assert!(store
            .list_edges(&["z".into()], &[derivation])
            .unwrap()
            .is_empty());
    }

    #[test]
    fn selection_population_contains_the_complete_competition_component() {
        let store = InMemoryNodeStore::new();
        for id in ["a", "b", "c"] {
            store.add_node(&node_with_id(id)).unwrap();
        }
        let derivation = crate::domain::Derivation {
            method: "semantic".into(),
            version: "v1".into(),
        };
        for (source, target) in [("a", "b"), ("b", "c")] {
            let edge = Edge::specification_relation(
                EdgeKind::HardContradiction,
                source,
                target,
                vec![],
                derivation.clone(),
                "t",
            )
            .unwrap();
            store.append_edge(&edge).unwrap();
        }

        let population = store
            .selection_population(&["c".into()], &[derivation])
            .unwrap();
        let endpoint_pairs: std::collections::BTreeSet<(&str, &str)> = population
            .relation_edges
            .iter()
            .map(|edge| (edge.source.as_str(), edge.target.as_str()))
            .collect();
        assert_eq!(endpoint_pairs, [("a", "b"), ("b", "c")].into());
    }

    #[test]
    fn duplicate_edge_content_is_reused_even_with_a_different_id_and_time() {
        let store = InMemoryNodeStore::new();
        let edge = Edge::specification_relation(
            EdgeKind::HardContradiction,
            "a",
            "b",
            vec!["basis".into()],
            crate::domain::Derivation {
                method: "semantic".into(),
                version: "v1".into(),
            },
            "t1",
        )
        .unwrap();
        assert!(store.append_edge(&edge).unwrap());

        let mut duplicate = edge.clone();
        duplicate.id = "caller-chose-another-id".into();
        duplicate.recorded_at = "t2".into();
        assert!(!store.append_edge(&duplicate).unwrap());
        assert_eq!(
            store
                .list_edges(&["a".into()], std::slice::from_ref(&edge.derivation))
                .unwrap(),
            [edge]
        );
    }

    #[test]
    fn equal_derived_nodes_are_shared_while_each_projection_edge_is_kept() {
        let store = InMemoryNodeStore::new();
        let assumption = DerivedNode::assumption("⊤", "v1");
        let derivation = crate::domain::Derivation {
            method: "contract".into(),
            version: "v1".into(),
        };
        let a = Edge::projection(
            EdgeKind::HasAssumption,
            "a",
            assumption.id(),
            derivation.clone(),
            "t1",
        )
        .unwrap();
        let b = Edge::projection(
            EdgeKind::HasAssumption,
            "b",
            assumption.id(),
            derivation,
            "t2",
        )
        .unwrap();
        assert_eq!(
            store.put_derived_node(&assumption, &a).unwrap(),
            DerivedGraphWrite {
                node_inserted: true,
                edge_inserted: true,
            }
        );
        assert_eq!(
            store.put_derived_node(&assumption, &b).unwrap(),
            DerivedGraphWrite {
                node_inserted: false,
                edge_inserted: true,
            }
        );
        assert_eq!(
            store
                .get_derived_nodes(&[assumption.id().to_string()])
                .unwrap(),
            [assumption]
        );
    }

    #[test]
    fn append_rejects_roles_that_reinterpret_the_edge_direction() {
        let store = InMemoryNodeStore::new();
        let mut edge = Edge {
            id: "invalid-refines".into(),
            source: "a".into(),
            source_kind: crate::domain::VertexKind::Specification,
            source_role: crate::domain::EndpointRole::Refined,
            target: "b".into(),
            target_kind: crate::domain::VertexKind::Specification,
            target_role: crate::domain::EndpointRole::Refiner,
            kind: EdgeKind::Refines,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: None,
            basis_spec_ids: vec![],
            derivation: crate::domain::Derivation {
                method: "test".into(),
                version: "v1".into(),
            },
            recorded_at: "t".into(),
        };
        assert!(matches!(
            store.append_edge(&edge),
            Err(StoreError::InvalidEdge(_))
        ));
        edge.source_role = crate::domain::EndpointRole::Refiner;
        edge.target_role = crate::domain::EndpointRole::Refined;
        assert!(store.append_edge(&edge).unwrap());
    }
}
