//! ArangoDB-backed [`NodeStore`].
//!
//! ArangoDB is the single graph-database product chosen to span the whole
//! deployment spectrum: the same `arangod`/RocksDB engine runs as a local
//! single node, a self-hosted cluster (Agency + Coordinators + DB-Servers), and
//! managed cloud. Growth is therefore a *relocation* of one product, not a swap
//! between products behind an abstraction. The driver is the community
//! `arangors` crate over HTTP/AQL, used in its **blocking** mode. Because the
//! daemon runs on an async (tonic) reactor, every call into this store must be
//! dispatched via `tokio::task::spawn_blocking` — the store itself is
//! deliberately synchronous and knows nothing about the runtime.
//!
//! Data model:
//!   * database `spec_oracle`;
//!   * document collection `nodes`, one document per node, `_key` = node id.
//!     (An earlier iteration used a `contracts` collection; that data was
//!     dev-only and is deliberately left behind, not migrated.)
//!   * the current captured-evidence view embedded in the document. Snapshot *bytes* are not stored here —
//!     only the `content_hash` pointer into the [`BlobStore`](crate::store);
//!     `Snapshot::content` is `#[serde(skip)]`, so a fetched node's content is
//!     empty and the blob store remains the byte authority.
//!
//!   * `term_nodes`, `derived_nodes`, and the native `edges` collection hold
//!     append-only graph topology. The derived collection contains
//!     content-addressed Evidence, Assumption, and Guarantee vertices;
//!   * `relation_assessments` holds append-only candidate-pair audit records,
//!     including Unknown/Independent outcomes that must not become topology.

use std::collections::HashMap;

use arangors::client::reqwest::ReqwestClient;
use arangors::index::{Index, IndexSettings};
use arangors::{ClientError, Connection, Database};
use serde_json::Value;

use crate::domain::{
    DerivedNode, Edge, EdgeKind, MetaUpdate, Node, RelationAssessment, TermNode, VertexKind,
};

use crate::store::{DerivedGraphWrite, GraphStore, GraphWrite, NodePage, NodeStore, StoreError};

/// The document collection holding one specification node per document.
const COLLECTION: &str = "nodes";
const TERM_COLLECTION: &str = "term_nodes";
const DERIVED_COLLECTION: &str = "derived_nodes";
const EDGE_COLLECTION: &str = "edges";
const ASSESSMENT_COLLECTION: &str = "relation_assessments";

/// Connection parameters for an ArangoDB deployment. Borrowed so the caller owns
/// the strings (typically CLI flags and environment variables).
pub struct ArangoConfig<'a> {
    pub url: &'a str,
    pub database: &'a str,
    pub username: &'a str,
    pub password: &'a str,
}

/// A [`NodeStore`] backed by an ArangoDB database.
pub struct ArangoNodeStore {
    db: Database<ReqwestClient>,
}

impl ArangoNodeStore {
    /// Connect and ensure the target database and the `nodes` collection
    /// exist. Idempotent: an existing database/collection is reused, and a
    /// concurrent creation (409) is tolerated.
    pub fn connect(cfg: &ArangoConfig) -> Result<ArangoNodeStore, StoreError> {
        let _span = tracing::info_span!(
            "spec.store.arango.connect",
            "db.system" = "arangodb",
            "db.name" = %cfg.database,
        )
        .entered();
        let conn = Connection::establish_basic_auth(cfg.url, cfg.username, cfg.password)
            .map_err(backend)?;
        let db = ensure_database(&conn, cfg.database)?;
        ensure_collection(&db, COLLECTION)?;
        ensure_collection(&db, TERM_COLLECTION)?;
        ensure_collection(&db, DERIVED_COLLECTION)?;
        ensure_edge_collection(&db, EDGE_COLLECTION)?;
        ensure_collection(&db, ASSESSMENT_COLLECTION)?;
        ensure_edge_read_projection(&db)?;
        ensure_edge_identities(&db)?;
        ensure_edge_read_index(&db)?;
        ensure_edge_identity_index(&db)?;
        ensure_node_identity_index(&db)?;
        Ok(ArangoNodeStore { db })
    }
}

impl NodeStore for ArangoNodeStore {
    fn add_node(&self, node: &Node) -> Result<bool, StoreError> {
        let _span = tracing::debug_span!(
            "spec.store.arango.add_node",
            "db.system" = "arangodb",
            "db.collection.name" = COLLECTION,
            "node.id" = %node.id,
        )
        .entered();
        // Serialize the node, then stamp `_key` so ArangoDB keys the document by
        // the node id. `snapshot.content` is skipped on serialize, so the bytes
        // stay in the blob store and only the hash pointer is persisted here.
        let mut doc = serde_json::to_value(node)?;
        if let Value::Object(ref mut map) = doc {
            map.insert("_key".to_string(), Value::String(node.id.clone()));
        }
        // A Specification Node is immutable once accepted. Retrying the same
        // Mailbox message is a no-op, so asynchronously appended Evidence and
        // Job results can never be erased by a repeated Add execution.
        upsert_immutable(&self.db, COLLECTION, &node.id, doc)
    }

    fn find_node(&self, statement: &str, lang_version: &str) -> Result<Option<Node>, StoreError> {
        let query = format!(
            "FOR node IN {COLLECTION} \
               FILTER node.statement == @statement \
               FILTER node.lang_version == @lang_version \
               SORT node._key ASC LIMIT 1 \
               RETURN UNSET(node, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("statement", Value::String(statement.to_string()));
        vars.insert("lang_version", Value::String(lang_version.to_string()));
        let nodes: Vec<Node> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        Ok(nodes.into_iter().next())
    }

    fn merge_evidence_requests(
        &self,
        node_id: &str,
        requests: &[String],
    ) -> Result<Node, StoreError> {
        let query = format!(
            "FOR node IN {COLLECTION} FILTER node._key == @node_id LIMIT 1 \
             LET requests = SORTED_UNIQUE(APPEND(NOT_NULL(node.meta.evidence_requests, []), @requests)) \
             UPDATE node WITH {{ meta: {{ evidence_requests: requests }} }} IN {COLLECTION} \
             OPTIONS {{ mergeObjects: true }} \
             RETURN UNSET(NEW, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("node_id", Value::String(node_id.to_string()));
        vars.insert("requests", serde_json::to_value(requests)?);
        let nodes: Vec<Node> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        nodes
            .into_iter()
            .next()
            .ok_or_else(|| StoreError::MissingNode(node_id.to_string()))
    }

    fn get_node(&self, id: &str) -> Result<Option<Node>, StoreError> {
        let _span = tracing::debug_span!(
            "spec.store.arango.get_node",
            "db.system" = "arangodb",
            "db.collection.name" = COLLECTION,
            "node.id" = %id,
        )
        .entered();
        // Strip the ArangoDB system attributes so the row deserializes straight
        // back into a `Node` (whose own `id` field is stored alongside `_key`).
        let query = format!(
            "FOR d IN {COLLECTION} FILTER d._key == @key \
             RETURN UNSET(d, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("key", Value::String(id.to_string()));
        let nodes: Vec<Node> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        Ok(nodes.into_iter().next())
    }

    fn apply_job_result(
        &self,
        node_id: &str,
        job_id: &str,
        update: &MetaUpdate,
        evidence: Option<&[crate::domain::Evidence]>,
    ) -> Result<(), StoreError> {
        let _span = tracing::debug_span!(
            "spec.store.arango.apply_job_result",
            "db.system" = "arangodb",
            "db.collection.name" = COLLECTION,
            "node.id" = %node_id,
            "job.id" = %job_id,
        )
        .entered();
        let meta_patch = if evidence.is_some() {
            "{ evidence: @evidence, updates: MERGE(NOT_NULL(node.meta.updates, {}), ZIP([@job_id], [@update])) }"
        } else {
            "{ updates: MERGE(NOT_NULL(node.meta.updates, {}), ZIP([@job_id], [@update])) }"
        };
        let query = format!(
            "FOR node IN {COLLECTION} FILTER node._key == @node_id LIMIT 1 \
             UPDATE node WITH {{ meta: {meta_patch} }} IN {COLLECTION} \
             OPTIONS {{ mergeObjects: true }} RETURN true"
        );
        let mut vars = HashMap::new();
        vars.insert("node_id", Value::String(node_id.to_string()));
        vars.insert("job_id", Value::String(job_id.to_string()));
        vars.insert("update", serde_json::to_value(update)?);
        if let Some(evidence) = evidence {
            vars.insert("evidence", serde_json::to_value(evidence)?);
        }
        let updated: Vec<bool> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        if updated.is_empty() {
            Err(StoreError::MissingNode(node_id.to_string()))
        } else {
            Ok(())
        }
    }
}

impl GraphStore for ArangoNodeStore {
    fn put_term_mention(&self, term: &TermNode, edge: &Edge) -> Result<GraphWrite, StoreError> {
        let mut term_doc = serde_json::to_value(term)?;
        term_doc
            .as_object_mut()
            .expect("term serializes as object")
            .insert("_key".into(), Value::String(term.id.clone()));
        let term_inserted = upsert_immutable(&self.db, TERM_COLLECTION, &term.id, term_doc)?;
        let edge_inserted = self.append_edge(edge)?;
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
        let mut doc = serde_json::to_value(node)?;
        doc.as_object_mut()
            .expect("derived node serializes as object")
            .insert("_key".into(), Value::String(node.id().to_string()));
        let node_inserted = upsert_immutable(&self.db, DERIVED_COLLECTION, node.id(), doc)?;
        let edge_inserted = self.append_edge(edge)?;
        Ok(DerivedGraphWrite {
            node_inserted,
            edge_inserted,
        })
    }

    fn append_edge(&self, edge: &Edge) -> Result<bool, StoreError> {
        edge.validate().map_err(StoreError::InvalidEdge)?;
        let from_collection = match edge.source_kind {
            VertexKind::Specification => COLLECTION,
            VertexKind::Term => TERM_COLLECTION,
            VertexKind::Evidence | VertexKind::Assumption | VertexKind::Guarantee => {
                DERIVED_COLLECTION
            }
        };
        let to_collection = match edge.target_kind {
            VertexKind::Specification => COLLECTION,
            VertexKind::Term => TERM_COLLECTION,
            VertexKind::Evidence | VertexKind::Assumption | VertexKind::Guarantee => {
                DERIVED_COLLECTION
            }
        };
        let identity_key = edge.identity_key();
        let doc = serde_json::json!({
            "_key": edge.id,
            "_from": format!("{from_collection}/{}", edge.source),
            "_to": format!("{to_collection}/{}", edge.target),
            "kind": edge_kind_name(edge.kind),
            "family": edge.family(),
            "page_owner": edge.page_owner(),
            "derivation_method": edge.derivation.method,
            "derivation_version": edge.derivation.version,
            "derivation_key": derivation_key(&edge.derivation),
            "identity_key": identity_key,
            "edge": edge,
        });
        upsert_edge_immutable(&self.db, &edge.id, &edge.identity_key(), doc)
    }

    fn append_relation_assessment(
        &self,
        assessment: &RelationAssessment,
    ) -> Result<bool, StoreError> {
        let mut doc = serde_json::to_value(assessment)?;
        if let Value::Object(ref mut map) = doc {
            map.insert("_key".to_string(), Value::String(assessment.id.clone()));
        }
        upsert_immutable(&self.db, ASSESSMENT_COLLECTION, &assessment.id, doc)
    }

    fn get_relation_assessment(&self, id: &str) -> Result<Option<RelationAssessment>, StoreError> {
        let query = format!(
            "FOR assessment IN {ASSESSMENT_COLLECTION} \
               FILTER assessment._key == @key LIMIT 1 \
               RETURN UNSET(assessment, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("key", Value::String(id.to_string()));
        let rows: Vec<RelationAssessment> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        Ok(rows.into_iter().next())
    }

    fn get_term_nodes(&self, ids: &[String]) -> Result<Vec<TermNode>, StoreError> {
        let query = format!(
            "FOR id IN @ids \
               LET term = DOCUMENT(CONCAT(\"{TERM_COLLECTION}/\", id)) \
               FILTER term != null \
               RETURN UNSET(term, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("ids", serde_json::to_value(ids)?);
        self.db.aql_bind_vars(&query, vars).map_err(backend)
    }

    fn get_derived_nodes(&self, ids: &[String]) -> Result<Vec<DerivedNode>, StoreError> {
        let query = format!(
            "FOR id IN @ids \
               LET node = DOCUMENT(CONCAT(\"{DERIVED_COLLECTION}/\", id)) \
               FILTER node != null \
               RETURN UNSET(node, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("ids", serde_json::to_value(ids)?);
        self.db.aql_bind_vars(&query, vars).map_err(backend)
    }

    fn list_term_candidates(
        &self,
        term_ids: &[String],
        term_derivation: &crate::domain::Derivation,
        exclude_node_id: &str,
        after: Option<&str>,
        limit: usize,
    ) -> Result<NodePage, StoreError> {
        if term_ids.is_empty() {
            return Ok(NodePage {
                nodes: Vec::new(),
                next_cursor: None,
            });
        }
        let fetch = limit.saturating_add(1);
        let after_filter = if after.is_some() {
            "FILTER node_id > @after"
        } else {
            ""
        };
        // The native edge index serves each INBOUND hop from a term vertex.
        // COLLECT deduplicates a specification that shares several terms with
        // the added Node; the candidate id remains the keyset cursor.
        let query = format!(
            "FOR term_id IN @term_ids \
               FOR vertex, mention IN 1..1 INBOUND \
                   CONCAT(\"{TERM_COLLECTION}/\", term_id) {EDGE_COLLECTION} \
                 FILTER mention.edge.kind == \"mentions_term\" \
                 FILTER mention.edge.source_role == \"mentioner\" \
                 FILTER mention.edge.target_role == \"mentioned_term\" \
                 FILTER mention.edge.derivation == @derivation \
                 FILTER vertex._key != @exclude \
                 COLLECT node_id = vertex._key \
                 {after_filter} \
                 SORT node_id ASC \
                 LIMIT @fetch \
                 LET node = DOCUMENT(CONCAT(\"{COLLECTION}/\", node_id)) \
                 FILTER node != null \
                 RETURN UNSET(node, \"_key\", \"_id\", \"_rev\")"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("term_ids", serde_json::to_value(term_ids)?);
        vars.insert("derivation", serde_json::to_value(term_derivation)?);
        vars.insert("exclude", Value::String(exclude_node_id.to_string()));
        vars.insert("fetch", Value::from(fetch as u64));
        if let Some(after) = after {
            vars.insert("after", Value::String(after.to_string()));
        }
        let mut rows: Vec<Node> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        let next_cursor = if rows.len() > limit {
            rows.truncate(limit);
            rows.last().map(|node| node.id.clone())
        } else {
            None
        };
        Ok(NodePage {
            nodes: rows,
            next_cursor,
        })
    }

    fn list_nodes(&self, after: Option<&str>, limit: usize) -> Result<NodePage, StoreError> {
        let _span = tracing::debug_span!(
            "spec.store.arango.list_nodes",
            "db.system" = "arangodb",
            "db.collection.name" = COLLECTION,
            "spec.page.limit" = limit as u64,
            "spec.page.after" = tracing::field::Empty,
            "spec.page.returned" = tracing::field::Empty,
        )
        .entered();

        // Keyset pagination on `_key`, served by the primary index (a sorted
        // index on `_key`): `FILTER d._key > @after SORT d._key ASC` is a range
        // scan, not an offset scan, so cost stays O(page) at any graph size. Two
        // query shapes keep the first page free of a redundant filter. Fetch one
        // past `limit` to learn whether a further page exists in the same round
        // trip. `UNSET` strips the system attributes so each row deserializes
        // straight back into a `Node` (whose own `id` field mirrors `_key`).
        let fetch = limit.saturating_add(1);
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("limit", Value::from(fetch as u64));
        let query = match after {
            Some(cursor) => {
                tracing::Span::current().record("spec.page.after", cursor);
                vars.insert("after", Value::String(cursor.to_string()));
                format!(
                    "FOR d IN {COLLECTION} FILTER d._key > @after SORT d._key ASC \
                     LIMIT @limit RETURN UNSET(d, \"_key\", \"_id\", \"_rev\")"
                )
            }
            None => format!(
                "FOR d IN {COLLECTION} SORT d._key ASC \
                 LIMIT @limit RETURN UNSET(d, \"_key\", \"_id\", \"_rev\")"
            ),
        };
        let mut rows: Vec<Node> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        let next_cursor = if rows.len() > limit {
            rows.truncate(limit);
            rows.last().map(|n| n.id.clone())
        } else {
            None
        };
        tracing::Span::current().record("spec.page.returned", rows.len() as u64);
        Ok(NodePage {
            nodes: rows,
            next_cursor,
        })
    }

    fn count_nodes(&self) -> Result<u64, StoreError> {
        let _span = tracing::debug_span!(
            "spec.store.arango.count_nodes",
            "db.system" = "arangodb",
            "db.collection.name" = COLLECTION,
        )
        .entered();
        // `LENGTH(collection)` reads ArangoDB's maintained document count in
        // O(1) — it does not scan — so this stays cheap as the graph grows.
        let query = format!("RETURN LENGTH({COLLECTION})");
        let counts: Vec<u64> = self.db.aql_str(&query).map_err(backend)?;
        Ok(counts.into_iter().next().unwrap_or(0))
    }

    fn list_edges(
        &self,
        owners: &[String],
        current_derivations: &[crate::domain::Derivation],
    ) -> Result<Vec<Edge>, StoreError> {
        let query = format!(
            "FOR e IN {EDGE_COLLECTION} \
               FILTER e.page_owner IN @owners \
               FILTER e.derivation_key IN @current \
               SORT e._key ASC \
               RETURN e.edge"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("owners", serde_json::to_value(owners)?);
        let current: Vec<String> = current_derivations.iter().map(derivation_key).collect();
        vars.insert("current", serde_json::to_value(current)?);
        self.db.aql_bind_vars(&query, vars).map_err(backend)
    }
}

fn derivation_key(derivation: &crate::domain::Derivation) -> String {
    // Both components are daemon-controlled identifiers and `|` is excluded
    // from their version vocabulary. Keeping one materialized scalar lets the
    // persistent page-owner index serve a method+version current-view query.
    format!("{}|{}", derivation.method, derivation.version)
}

fn edge_kind_name(kind: EdgeKind) -> &'static str {
    kind.as_str()
}

fn upsert_immutable(
    db: &Database<ReqwestClient>,
    collection: &str,
    key: &str,
    doc: Value,
) -> Result<bool, StoreError> {
    let query = format!(
        "UPSERT {{ _key: @key }} INSERT @doc UPDATE {{}} IN {collection} \
         RETURN OLD == null"
    );
    let mut vars: HashMap<&str, Value> = HashMap::new();
    vars.insert("key", Value::String(key.to_string()));
    vars.insert("doc", doc);
    let inserted: Vec<bool> = db.aql_bind_vars(&query, vars).map_err(backend)?;
    Ok(inserted.into_iter().next().unwrap_or(false))
}

fn upsert_edge_immutable(
    db: &Database<ReqwestClient>,
    key: &str,
    identity_key: &str,
    doc: Value,
) -> Result<bool, StoreError> {
    // Check both identities: `_key` protects deterministic historical writers;
    // `identity_key` rejects the same typed relationship even if a caller
    // supplies a different Edge id. The unique persistent index closes races
    // between concurrent Jobs.
    let query = format!(
        "LET existing = FIRST( \
           FOR edge IN {EDGE_COLLECTION} \
             FILTER edge._key == @key OR edge.identity_key == @identity_key \
             LIMIT 1 RETURN edge._key \
         ) \
         FILTER existing == null \
         INSERT @doc INTO {EDGE_COLLECTION} \
         RETURN true"
    );
    let mut vars: HashMap<&str, Value> = HashMap::new();
    vars.insert("key", Value::String(key.to_string()));
    vars.insert("identity_key", Value::String(identity_key.to_string()));
    vars.insert("doc", doc);
    match db.aql_bind_vars::<bool>(&query, vars) {
        Ok(inserted) => Ok(inserted.into_iter().next().unwrap_or(false)),
        // A concurrent writer may pass the read before us. The unique index
        // converts that race into the same idempotent "already exists" result.
        Err(ref error) if is_status(error, 409) => Ok(false),
        Err(error) => Err(backend(error)),
    }
}

/// Map a driver error into the backend-agnostic [`StoreError`].
fn backend(e: ClientError) -> StoreError {
    StoreError::Backend(e.to_string())
}

fn is_status(e: &ClientError, code: u16) -> bool {
    matches!(e, ClientError::Arango(a) if a.code() == code)
}

fn ensure_database(conn: &Connection, name: &str) -> Result<Database<ReqwestClient>, StoreError> {
    match conn.db(name) {
        Ok(db) => Ok(db),
        Err(ref e) if is_status(e, 404) => match conn.create_database(name) {
            Ok(db) => Ok(db),
            // Lost a creation race — the database now exists; re-open it.
            Err(ref e2) if is_status(e2, 409) => conn.db(name).map_err(backend),
            Err(e2) => Err(backend(e2)),
        },
        // Auth/connection failures surface immediately rather than being masked
        // by a create attempt.
        Err(e) => Err(backend(e)),
    }
}

fn ensure_collection(db: &Database<ReqwestClient>, name: &str) -> Result<(), StoreError> {
    match db.collection(name) {
        Ok(_) => Ok(()),
        Err(ref e) if is_status(e, 404) => match db.create_collection(name) {
            Ok(_) => Ok(()),
            Err(ref e2) if is_status(e2, 409) => Ok(()),
            Err(e2) => Err(backend(e2)),
        },
        Err(e) => Err(backend(e)),
    }
}

fn ensure_edge_collection(db: &Database<ReqwestClient>, name: &str) -> Result<(), StoreError> {
    match db.collection(name) {
        Ok(_) => Ok(()),
        Err(ref e) if is_status(e, 404) => match db.create_edge_collection(name) {
            Ok(_) => Ok(()),
            Err(ref e2) if is_status(e2, 409) => Ok(()),
            Err(e2) => Err(backend(e2)),
        },
        Err(e) => Err(backend(e)),
    }
}

/// Backfill query-only scalar projections on historical Edge documents. The
/// immutable nested `edge` fact is never changed; these fields only make the
/// append-only history indexable by page owner and derivation.
fn ensure_edge_read_projection(db: &Database<ReqwestClient>) -> Result<(), StoreError> {
    let query = format!(
        "FOR e IN {EDGE_COLLECTION} \
           FILTER e.page_owner == null OR e.derivation_key == null OR e.family == null \
           LET owner = e.edge.target_kind != \"specification\" \
             ? e.edge.source \
             : MIN([e.edge.source, e.edge.target]) \
           LET key = CONCAT(e.edge.derivation.method, \"|\", e.edge.derivation.version) \
           LET family = e.edge.kind == \"mentions_term\" \
             ? \"lexical\" \
             : POSITION([\"grounded_by\", \"has_assumption\", \"has_guarantee\"], e.edge.kind) \
               ? \"projection\" \
             : POSITION([\"supports\", \"defeats\", \"supersedes\"], e.edge.kind) \
               ? \"selection\" \
               : \"semantic\" \
           UPDATE e WITH {{ \
             page_owner: owner, \
             family: family, \
             derivation_method: e.edge.derivation.method, \
             derivation_version: e.edge.derivation.version, \
             derivation_key: key \
           }} IN {EDGE_COLLECTION} \
           RETURN true"
    );
    let _: Vec<bool> = db.aql_str(&query).map_err(backend)?;
    Ok(())
}

fn ensure_edge_identities(db: &Database<ReqwestClient>) -> Result<(), StoreError> {
    // Compute the exact Rust domain identity for historical rows. If historical
    // data already contains duplicates, preserve every Ledger row but give only
    // the first one the canonical identity; future writes then reuse it.
    let query = format!(
        "FOR e IN {EDGE_COLLECTION} SORT e._key ASC \
         RETURN {{ key: e._key, identity: e.identity_key, edge: e.edge }}"
    );
    let rows: Vec<Value> = db.aql_str(&query).map_err(backend)?;
    let mut groups: std::collections::BTreeMap<String, Vec<(String, Option<String>)>> =
        std::collections::BTreeMap::new();
    for row in rows {
        let key = row
            .get("key")
            .and_then(Value::as_str)
            .ok_or_else(|| StoreError::Backend("historical Edge row has no key".into()))?;
        let edge: Edge = serde_json::from_value(
            row.get("edge")
                .cloned()
                .ok_or_else(|| StoreError::Backend("historical Edge row has no edge".into()))?,
        )?;
        let canonical = edge.identity_key();
        let current = row
            .get("identity")
            .and_then(Value::as_str)
            .map(str::to_string);
        groups
            .entry(canonical)
            .or_default()
            .push((key.to_string(), current));
    }
    for (canonical, entries) in groups {
        // Preserve an already-canonical representative; otherwise the first
        // lexical key becomes the selected historical representative.
        let keeper = entries
            .iter()
            .position(|(_, current)| current.as_deref() == Some(canonical.as_str()))
            .unwrap_or(0);
        for (index, (key, current)) in entries.into_iter().enumerate() {
            let identity = if index == keeper {
                canonical.clone()
            } else {
                format!("legacy-duplicate:{canonical}:{key}")
            };
            if current.as_deref() == Some(identity.as_str()) {
                continue;
            }
            let update = format!(
                "UPDATE @key WITH {{ identity_key: @identity }} IN {EDGE_COLLECTION} RETURN true"
            );
            let mut vars: HashMap<&str, Value> = HashMap::new();
            vars.insert("key", Value::String(key));
            vars.insert("identity", Value::String(identity));
            let _: Vec<bool> = db.aql_bind_vars(&update, vars).map_err(backend)?;
        }
    }
    Ok(())
}

fn ensure_edge_identity_index(db: &Database<ReqwestClient>) -> Result<(), StoreError> {
    let index = Index::builder()
        .name("edge_unique_identity")
        .fields(vec!["identity_key".to_string()])
        .settings(IndexSettings::Persistent {
            unique: true,
            sparse: false,
            deduplicate: false,
        })
        .build();
    db.create_index(EDGE_COLLECTION, &index)
        .map(|_| ())
        .map_err(backend)
}

fn ensure_node_identity_index(db: &Database<ReqwestClient>) -> Result<(), StoreError> {
    let index = Index::builder()
        .name("node_by_authored_content")
        .fields(vec!["statement".to_string(), "lang_version".to_string()])
        .settings(IndexSettings::Persistent {
            unique: false,
            sparse: false,
            deduplicate: false,
        })
        .build();
    db.create_index(COLLECTION, &index)
        .map(|_| ())
        .map_err(backend)
}

fn ensure_edge_read_index(db: &Database<ReqwestClient>) -> Result<(), StoreError> {
    let index = Index::builder()
        .name("edge_current_by_owner")
        .fields(vec!["page_owner".to_string(), "derivation_key".to_string()])
        .settings(IndexSettings::Persistent {
            unique: false,
            sparse: false,
            deduplicate: false,
        })
        .build();
    db.create_index(EDGE_COLLECTION, &index)
        .map(|_| ())
        .map_err(backend)
}
