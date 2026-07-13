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
//! Data model (the only collection this scope touches):
//!   * database `spec_oracle`;
//!   * document collection `nodes`, one document per node, `_key` = node id.
//!     (An earlier iteration used a `contracts` collection; that data was
//!     dev-only and is deliberately left behind, not migrated.)
//!   * evidence embedded in the document. Snapshot *bytes* are not stored here —
//!     only the `content_hash` pointer into the [`BlobStore`](crate::store);
//!     `Snapshot::content` is `#[serde(skip)]`, so a fetched node's content is
//!     empty and the blob store remains the byte authority.
//!
//! Edge collections (refinement/composition/…) are deliberately absent — edges
//! are out of scope — but they attach behind this same store later.

use std::collections::HashMap;

use arangors::client::reqwest::ReqwestClient;
use arangors::{ClientError, Connection, Database};
use serde_json::Value;

use crate::domain::{Edge, EdgeKind, MetaUpdate, Node, TermNode, VertexKind};

use crate::store::{GraphStore, GraphWrite, NodePage, NodeStore, StoreError};

/// The document collection holding one specification node per document.
const COLLECTION: &str = "nodes";
const TERM_COLLECTION: &str = "term_nodes";
const EDGE_COLLECTION: &str = "edges";

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
        ensure_edge_collection(&db, EDGE_COLLECTION)?;
        Ok(ArangoNodeStore { db })
    }
}

impl NodeStore for ArangoNodeStore {
    fn add_node(&self, node: &Node) -> Result<(), StoreError> {
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
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("doc", doc);
        // A Specification Node is immutable once accepted. Retrying the same
        // Mailbox message is a no-op, so asynchronously appended Evidence and
        // Job results can never be erased by a repeated Add execution.
        let query = format!(
            "INSERT @doc INTO {COLLECTION} OPTIONS {{ \
               overwriteMode: \"ignore\" \
             }}"
        );
        let _: Vec<Value> = self.db.aql_bind_vars(&query, vars).map_err(backend)?;
        Ok(())
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

    fn append_edge(&self, edge: &Edge) -> Result<bool, StoreError> {
        let from_collection = match edge.source_kind {
            VertexKind::Specification => COLLECTION,
            VertexKind::Term => TERM_COLLECTION,
        };
        let to_collection = match edge.target_kind {
            VertexKind::Specification => COLLECTION,
            VertexKind::Term => TERM_COLLECTION,
        };
        let doc = serde_json::json!({
            "_key": edge.id,
            "_from": format!("{from_collection}/{}", edge.source),
            "_to": format!("{to_collection}/{}", edge.target),
            "kind": edge_kind_name(edge.kind),
            "derivation_version": edge.derivation.version,
            "edge": edge,
        });
        upsert_immutable(&self.db, EDGE_COLLECTION, &edge.id, doc)
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
        among: &[String],
        derivation_version: &str,
    ) -> Result<Vec<Edge>, StoreError> {
        let query = format!(
            "FOR e IN {EDGE_COLLECTION} \
               FILTER e.derivation_version == @version \
               FILTER e.kind == \"mentions_term\" AND e.edge.source IN @among \
               SORT e._key ASC \
               RETURN e.edge"
        );
        let mut vars: HashMap<&str, Value> = HashMap::new();
        vars.insert("among", serde_json::to_value(among)?);
        vars.insert("version", Value::String(derivation_version.to_string()));
        self.db.aql_bind_vars(&query, vars).map_err(backend)
    }
}

fn edge_kind_name(kind: EdgeKind) -> &'static str {
    match kind {
        EdgeKind::MentionsTerm => "mentions_term",
    }
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
