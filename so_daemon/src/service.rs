//! The tonic service implementing the `spec_oracle.v1.SpecificationGraph`
//! wire contract.
//!
//! The RPC layer is thin: it decodes the request, stamps the daemon-authoritative
//! creation instant (sense ③), and sends an owned command to the Add Mailbox.
//! The Mailbox parses one sentence and runs only the blocking Node save off the
//! async reactor. It replies with one stored-facts-only Node; Evidence capture,
//! graph generation, and other processing run from the subsequent NodeAdded
//! Jobs. Add errors map to gRPC status codes the client turns into exit codes
//! (`INVALID_ARGUMENT` → bad input, `INTERNAL` → runtime failure).

use std::sync::Arc;

use tonic::{Request, Response, Status};
use tracing::Instrument;

use crate::domain::Edge;
use so_protocol::pb;
use so_protocol::pb::specification_graph_server::SpecificationGraph;

use crate::add::AddError;
use crate::add_mailbox::{AddInput, AddMailbox, AddMailboxError};
use crate::convert;
use crate::store::{GraphStore, NodePage, StoreError};

/// Page size used when the request leaves `page_size` at 0.
const DEFAULT_PAGE_SIZE: u32 = 100;
/// Hard cap on a page: the server never returns more nodes than this in one
/// response, whatever the caller asks for. This is the backstop that keeps a
/// graph read bounded no matter how large the graph grows.
const MAX_PAGE_SIZE: u32 = 1000;

type GraphReadResult = (NodePage, Vec<crate::domain::TermNode>, Vec<Edge>, u64);

/// The service, holding the two persistence seams behind `Arc`s so each request
/// can hand them to a blocking task. Both trait objects are `Send + Sync` so they
/// can cross the `spawn_blocking` boundary and be shared across requests.
///
/// The node store is a [`GraphStore`] (which extends [`NodeStore`]): ingest uses
/// its write side and the bounded graph read uses its read side, from one shared
/// handle.
pub struct SpecificationGraphService {
    nodes: Arc<dyn GraphStore + Send + Sync>,
    adds: AddMailbox,
}

impl SpecificationGraphService {
    pub fn new(
        nodes: Arc<dyn GraphStore + Send + Sync>,
        adds: AddMailbox,
    ) -> SpecificationGraphService {
        SpecificationGraphService { nodes, adds }
    }
}

#[tonic::async_trait]
impl SpecificationGraph for SpecificationGraphService {
    async fn add_specification(
        &self,
        request: Request<pb::AddSpecificationRequest>,
    ) -> Result<Response<pb::AddSpecificationResponse>, Status> {
        let policy = so_tracing::capture_policy();
        let span = tracing::info_span!(
            "spec.daemon.add_specification",
            "spec.telemetry.capture" = policy.as_str(),
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "AddSpecification",
            "client.name" = tracing::field::Empty,
            "client.version" = tracing::field::Empty,
            "spec.specification.length" = tracing::field::Empty,
            "spec.evidence.request_count" = tracing::field::Empty,
            "spec.sentence.count" = tracing::field::Empty,
            "spec.specification.hash" = tracing::field::Empty,
            "spec.specification.text" = tracing::field::Empty,
            "error.category" = tracing::field::Empty,
            "error.stage" = tracing::field::Empty,
            "error.kind" = tracing::field::Empty,
            "error.message" = tracing::field::Empty,
            "node.id" = tracing::field::Empty,
            "node.count" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move { self.add_specification_inner(request).await }
            .instrument(span)
            .await
    }

    async fn get_graph(
        &self,
        request: Request<pb::GetGraphRequest>,
    ) -> Result<Response<pb::GetGraphResponse>, Status> {
        let span = tracing::info_span!(
            "spec.daemon.get_graph",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "GetGraph",
            "spec.page.requested_size" = tracing::field::Empty,
            "spec.page.limit" = tracing::field::Empty,
            "spec.page.has_cursor" = tracing::field::Empty,
            "spec.page.node_count" = tracing::field::Empty,
            "spec.page.edge_count" = tracing::field::Empty,
            "spec.page.has_next" = tracing::field::Empty,
            "spec.graph.total_nodes" = tracing::field::Empty,
            "error.message" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move { self.get_graph_inner(request).await }
            .instrument(span)
            .await
    }
}

impl SpecificationGraphService {
    async fn add_specification_inner(
        &self,
        request: Request<pb::AddSpecificationRequest>,
    ) -> Result<Response<pb::AddSpecificationResponse>, Status> {
        let policy = so_tracing::capture_policy();
        let req = request.into_inner();

        // The client identifies itself; fall back to sane defaults so the record
        // is always complete (sense ③).
        let cli = if req.client.is_empty() {
            "spec".to_string()
        } else {
            req.client
        };
        let cli_version = if req.client_version.is_empty() {
            "unknown".to_string()
        } else {
            req.client_version
        };
        // Creation time is the daemon's, not the client's — one authoritative clock.
        let now = chrono::Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Secs, true);

        let specification = req.specification;
        let evidence = req.evidence;
        tracing::Span::current().record("client.name", cli.as_str());
        tracing::Span::current().record("client.version", cli_version.as_str());
        tracing::Span::current().record("spec.specification.length", specification.len() as u64);
        tracing::Span::current().record("spec.evidence.request_count", evidence.len() as u64);
        let current = tracing::Span::current();
        so_tracing::record_specification_on_span(&current, policy, &specification);

        let node = match self
            .adds
            .add(AddInput {
                specification,
                evidence,
                now,
                cli,
                cli_version,
            })
            .await
        {
            Ok(node) => node,
            Err(AddMailboxError::Add(e)) => {
                record_add_error(policy, &e);
                return Err(add_error_to_status(e));
            }
            Err(error) => {
                let message = error.to_string();
                tracing::Span::current().record("error.message", message.as_str());
                return Err(Status::internal(message));
            }
        };
        tracing::Span::current().record("spec.sentence.count", 1_u64);
        tracing::Span::current().record("node.count", 1_u64);
        tracing::Span::current().record("node.id", node.id.as_str());
        tracing::info!(
            "node.id" = %node.id,
            "specification accepted; post-acceptance work scheduled as Jobs"
        );
        Ok(Response::new(pb::AddSpecificationResponse {
            node: Some(convert::accepted_node_to_pb(&node)),
        }))
    }

    async fn get_graph_inner(
        &self,
        request: Request<pb::GetGraphRequest>,
    ) -> Result<Response<pb::GetGraphResponse>, Status> {
        let req = request.into_inner();

        // Resolve the page size against the server's own bounds: 0 means "use
        // the default", and any request is clamped to the hard maximum. The
        // caller can never coerce an unbounded read.
        let requested = req.page_size;
        let limit = clamp_page_size(requested) as usize;
        let after = if req.page_token.is_empty() {
            None
        } else {
            Some(req.page_token)
        };
        tracing::Span::current().record("spec.page.requested_size", requested as u64);
        tracing::Span::current().record("spec.page.limit", limit as u64);
        tracing::Span::current().record("spec.page.has_cursor", after.is_some());

        let nodes = self.nodes.clone();

        // The ArangoDB driver is blocking, so the read runs off the async
        // reactor, mirroring the ingest path. Each current Edge is assigned to
        // one deterministic specification-page owner. A semantic Edge may
        // therefore precede its other endpoint; full-graph consumers collect
        // all pages, while bounded consumers defer it until both endpoints are
        // loaded. The total is a cheap maintained count, not a scan.
        let read_span = tracing::info_span!("spec.daemon.read_blocking");
        let outcome =
            tokio::task::spawn_blocking(move || -> Result<GraphReadResult, StoreError> {
                let _entered = read_span.enter();
                let page = nodes.list_nodes(after.as_deref(), limit)?;
                let ids: Vec<String> = page.nodes.iter().map(|n| n.id.clone()).collect();
                let edges =
                    nodes.list_edges(&ids, &crate::graph_generation::current_derivations())?;
                let mut term_ids: Vec<String> = edges
                    .iter()
                    .filter(|edge| {
                        edge.target_kind == crate::domain::VertexKind::Term
                            && edge.target_role == crate::domain::EndpointRole::MentionedTerm
                    })
                    .map(|edge| edge.target.clone())
                    .collect();
                term_ids.sort();
                term_ids.dedup();
                let terms = nodes.get_term_nodes(&term_ids)?;
                let total = nodes.count_nodes()?;
                Ok((page, terms, edges, total))
            })
            .await
            .map_err(|e| Status::internal(format!("graph read task failed to run: {e}")))?;

        let (page, terms, edges, total) = match outcome {
            Ok(result) => result,
            Err(e) => {
                let message = e.to_string();
                tracing::Span::current().record("error.message", message.as_str());
                tracing::warn!("error.message" = %message, "graph read failed");
                return Err(Status::internal(message));
            }
        };

        let next_page_token = page.next_cursor.unwrap_or_default();
        tracing::Span::current().record("spec.page.node_count", page.nodes.len() as u64);
        tracing::Span::current().record("spec.page.edge_count", edges.len() as u64);
        tracing::Span::current().record("spec.page.has_next", !next_page_token.is_empty());
        tracing::Span::current().record("spec.graph.total_nodes", total);
        tracing::info!(
            "spec.page.node_count" = page.nodes.len() as u64,
            "spec.graph.total_nodes" = total,
            "graph read completed"
        );

        Ok(Response::new(pb::GetGraphResponse {
            nodes: page.nodes.iter().map(convert::node_to_pb).collect(),
            edges: edges.iter().map(convert::edge_to_pb).collect(),
            next_page_token,
            total_nodes: total,
            term_nodes: terms.iter().map(convert::term_node_to_pb).collect(),
        }))
    }
}

/// Resolve a requested page size to a concrete limit: `0` becomes the default,
/// and any value is capped at [`MAX_PAGE_SIZE`]. Always returns at least 1.
fn clamp_page_size(requested: u32) -> u32 {
    let size = if requested == 0 {
        DEFAULT_PAGE_SIZE
    } else {
        requested
    };
    size.clamp(1, MAX_PAGE_SIZE)
}

fn record_add_error(policy: so_tracing::CapturePolicy, error: &AddError) {
    tracing::Span::current().record("error.category", error.category());
    tracing::Span::current().record("error.stage", error.stage());

    match policy {
        so_tracing::CapturePolicy::Ops => {
            tracing::warn!(
                "error.category" = error.category(),
                "error.stage" = error.stage(),
                "spec.telemetry.capture" = policy.as_str(),
                "specification ingest failed"
            );
        }
        so_tracing::CapturePolicy::Diagnostic => {
            tracing::Span::current().record("error.kind", error.diagnostic_kind());
            tracing::warn!(
                "error.category" = error.category(),
                "error.stage" = error.stage(),
                "error.kind" = error.diagnostic_kind(),
                "spec.telemetry.capture" = policy.as_str(),
                "specification ingest failed"
            );
        }
        so_tracing::CapturePolicy::Content => {
            tracing::Span::current().record("error.kind", error.diagnostic_kind());
            let message = error.to_string();
            tracing::Span::current().record("error.message", message.as_str());
            tracing::warn!(
                "error.category" = error.category(),
                "error.stage" = error.stage(),
                "error.kind" = error.diagnostic_kind(),
                "error.message" = %message,
                "spec.telemetry.capture" = policy.as_str(),
                "specification ingest failed"
            );
        }
    }
}

/// Only syntax/sentence-count validation and Node persistence occur here.
fn add_error_to_status(e: AddError) -> Status {
    match &e {
        AddError::Grammar(_) | AddError::SentenceCount { .. } => {
            Status::invalid_argument(e.to_string())
        }
        AddError::Store(_) => Status::internal(e.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::add_mailbox::AddMailbox;
    use crate::domain::{Edge, EdgeKind, Meta, Node, VertexKind};
    use crate::jobs::JobMailbox;
    use crate::store::{BlobStore, InMemoryNodeStore, NodeStore, StoreError};

    #[test]
    fn clamp_page_size_applies_default_floor_and_ceiling() {
        assert_eq!(clamp_page_size(0), DEFAULT_PAGE_SIZE); // 0 → default
        assert_eq!(clamp_page_size(50), 50); // within range → passthrough
        assert_eq!(clamp_page_size(MAX_PAGE_SIZE + 1), MAX_PAGE_SIZE); // clamped
        assert_eq!(clamp_page_size(u32::MAX), MAX_PAGE_SIZE); // never unbounded
    }

    struct NoBlobs;
    impl BlobStore for NoBlobs {
        fn put_blob(&self, _hash: &str, _bytes: &[u8]) -> Result<(), StoreError> {
            Ok(())
        }
        fn get_blob(&self, _hash: &str) -> Result<Option<Vec<u8>>, StoreError> {
            Ok(None)
        }
    }

    fn node(id: &str) -> Node {
        Node {
            id: id.to_string(),
            statement: "The pump shall stop.".to_string(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence_requests: vec![],
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
                updates: Default::default(),
            },
        }
    }

    #[tokio::test]
    async fn get_graph_returns_a_bounded_page_with_cursor_and_total() {
        // The production in-memory backend — no bespoke test double needed.
        let store = Arc::new(InMemoryNodeStore::new());
        for id in ["n1", "n2", "n3"] {
            store.add_node(&node(id)).unwrap();
        }
        let blobs = Arc::new(NoBlobs);
        let (jobs, jobs_task) = JobMailbox::start(store.clone(), blobs.clone());
        let (adds, adds_task) = AddMailbox::start(store.clone(), jobs.clone());
        let service = SpecificationGraphService::new(store, adds.clone());

        // Page size 2 over 3 nodes: a full page plus a continuation token.
        let resp = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 2,
                page_token: String::new(),
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(resp.nodes.len(), 2);
        assert_eq!(resp.total_nodes, 3);
        assert!(resp.edges.is_empty(), "no edges exist yet");
        assert!(!resp.next_page_token.is_empty(), "a further page remains");

        // Following the cursor yields the last node and ends the walk.
        let resp2 = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 2,
                page_token: resp.next_page_token.clone(),
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(resp2.nodes.len(), 1);
        assert_eq!(resp2.nodes[0].id, "n3");
        assert!(resp2.next_page_token.is_empty(), "walk is complete");

        adds.shutdown().await.unwrap();
        adds_task.await.unwrap();
        jobs.shutdown().await.unwrap();
        jobs_task.await.unwrap();
    }

    #[tokio::test]
    async fn semantic_edge_crossing_pages_is_returned_once_by_its_owner() {
        let store = Arc::new(InMemoryNodeStore::new());
        for id in ["a", "z"] {
            store.add_node(&node(id)).unwrap();
        }
        store
            .append_edge(&Edge {
                id: "semantic-z-a".into(),
                source: "z".into(),
                source_kind: VertexKind::Specification,
                source_role: crate::domain::EndpointRole::Refiner,
                target: "a".into(),
                target_kind: VertexKind::Specification,
                target_role: crate::domain::EndpointRole::Refined,
                kind: EdgeKind::Refines,
                source_anchor: None,
                target_anchor: None,
                basis_spec_ids: vec![],
                derivation: crate::graph_generation::semantic_edge_derivation(),
                recorded_at: "t".into(),
            })
            .unwrap();
        let blobs = Arc::new(NoBlobs);
        let (jobs, jobs_task) = JobMailbox::start(store.clone(), blobs);
        let (adds, adds_task) = AddMailbox::start(store.clone(), jobs.clone());
        let service = SpecificationGraphService::new(store, adds.clone());

        let first = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 1,
                page_token: String::new(),
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(first.nodes[0].id, "a");
        assert_eq!(first.edges.len(), 1);
        assert_eq!(first.edges[0].source, "z");
        assert_eq!(first.edges[0].target, "a");
        assert_eq!(first.edges[0].kind, pb::EdgeKind::Refines as i32);
        assert_eq!(first.edges[0].family, pb::EdgeFamily::Semantic as i32);
        assert_eq!(
            first.edges[0].source_role,
            pb::EdgeEndpointRole::Refiner as i32
        );

        let second = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 1,
                page_token: first.next_page_token,
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(second.nodes[0].id, "z");
        assert!(
            second.edges.is_empty(),
            "owner paging must not duplicate the Edge"
        );

        adds.shutdown().await.unwrap();
        adds_task.await.unwrap();
        jobs.shutdown().await.unwrap();
        jobs_task.await.unwrap();
    }
}
