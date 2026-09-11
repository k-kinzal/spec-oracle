//! The tonic service implementing the `spec_oracle.v1.SpecificationGraph`
//! wire contract.
//!
//! The RPC layer is thin: it decodes the request, stamps the daemon-authoritative
//! creation instant (sense ③), and sends an owned command to the Command Bus.
//! The handler parses one sentence and runs only the blocking Node save off the
//! async reactor. It replies with one stored-facts-only Node; Evidence capture,
//! graph generation, and other processing run from subsequent Events and
//! Consumers. Add errors map to gRPC status codes the client turns into exit codes
//! (`INVALID_ARGUMENT` → bad input, `INTERNAL` → runtime failure).

use std::collections::BTreeMap;
use std::sync::Arc;

use tonic::{Request, Response, Status};
use tracing::Instrument;

use crate::domain::Edge;
use so_protocol::pb;
use so_protocol::pb::specification_graph_server::SpecificationGraph;

use crate::add::AddError;
use crate::command_bus::{
    AddEvidenceRelationInput, AddNodeInput, CommandBus, CommandBusError, GraphCommandError,
    StartGraphRebuildInput,
};
use crate::convert;
use crate::store::{EdgePage, GraphStore, NodePage, StoreError};

/// Page size used when the request leaves `page_size` at 0.
const DEFAULT_PAGE_SIZE: u32 = 100;
/// Hard cap on a page: the server never returns more nodes than this in one
/// response, whatever the caller asks for. A graph page also carries the
/// current relation-assessment audit rows owned by its specifications, whose
/// count is not bounded by Node count. At 1,000 Nodes a mature Ledger can
/// exceed tonic's 64 MiB message limit, so the backstop stays at 100 and
/// clients follow continuation tokens without data loss.
const MAX_PAGE_SIZE: u32 = 100;

type GraphReadResult = (
    NodePage,
    Vec<crate::domain::TermNode>,
    Vec<crate::domain::DerivedNode>,
    Vec<Edge>,
    Vec<crate::domain::RelationAssessment>,
    BTreeMap<String, crate::domain::SelectionView>,
    u64,
);

type LedgerReadResult = (
    EdgePage,
    Vec<crate::domain::TermNode>,
    Vec<crate::domain::DerivedNode>,
    std::collections::BTreeSet<String>,
    u64,
);

/// The service, holding the two persistence seams behind `Arc`s so each request
/// can hand them to a blocking task. Both trait objects are `Send + Sync` so they
/// can cross the `spawn_blocking` boundary and be shared across requests.
///
/// The node store is a [`GraphStore`] (which extends [`NodeStore`]): ingest uses
/// its write side and the bounded graph read uses its read side, from one shared
/// handle.
pub struct SpecificationGraphService {
    nodes: Arc<dyn GraphStore + Send + Sync>,
    commands: CommandBus,
}

impl SpecificationGraphService {
    pub fn new(
        nodes: Arc<dyn GraphStore + Send + Sync>,
        commands: CommandBus,
    ) -> SpecificationGraphService {
        SpecificationGraphService { nodes, commands }
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

    async fn add_evidence_relation(
        &self,
        request: Request<pb::AddEvidenceRelationRequest>,
    ) -> Result<Response<pb::AddEvidenceRelationResponse>, Status> {
        let span = tracing::info_span!(
            "spec.daemon.add_evidence_relation",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "AddEvidenceRelation",
            "evidence.target" = tracing::field::Empty,
            "evidence.relation" = tracing::field::Empty,
            "edge.id" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move { self.add_evidence_relation_inner(request).await }
            .instrument(span)
            .await
    }

    async fn query_evidence_graph(
        &self,
        request: Request<pb::QueryEvidenceGraphRequest>,
    ) -> Result<Response<pb::QueryEvidenceGraphResponse>, Status> {
        let span = tracing::info_span!(
            "spec.daemon.query_evidence_graph",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "QueryEvidenceGraph",
            "evidence.page.node_count" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move { self.query_evidence_graph_inner(request).await }
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

    async fn get_ledger(
        &self,
        request: Request<pb::GetLedgerRequest>,
    ) -> Result<Response<pb::GetLedgerResponse>, Status> {
        let span = tracing::info_span!(
            "spec.daemon.get_ledger",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "GetLedger",
            "ledger.page.requested_size" = tracing::field::Empty,
            "ledger.page.edge_count" = tracing::field::Empty,
            "ledger.page.has_next" = tracing::field::Empty,
            "ledger.total_edges" = tracing::field::Empty,
            "error.message" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move { self.get_ledger_inner(request).await }
            .instrument(span)
            .await
    }

    async fn start_graph_rebuild(
        &self,
        request: Request<pb::StartGraphRebuildRequest>,
    ) -> Result<Response<pb::StartGraphRebuildResponse>, Status> {
        let span = tracing::info_span!(
            "spec.daemon.start_graph_rebuild",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "StartGraphRebuild",
            "client.name" = tracing::field::Empty,
            "client.version" = tracing::field::Empty,
            "command.id" = tracing::field::Empty,
            "spec.graph.total_nodes" = tracing::field::Empty,
            "error.message" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move {
            let request = request.into_inner();
            let client = if request.client.is_empty() {
                "spec".to_string()
            } else {
                request.client
            };
            let client_version = if request.client_version.is_empty() {
                "unknown".to_string()
            } else {
                request.client_version
            };
            tracing::Span::current().record("client.name", client.as_str());
            tracing::Span::current().record("client.version", client_version.as_str());
            let (ack, total_nodes) = self
                .commands
                .start_graph_rebuild(StartGraphRebuildInput {
                    client,
                    client_version,
                })
                .await
                .map_err(|error| {
                    let message = error.to_string();
                    tracing::Span::current().record("error.message", message.as_str());
                    Status::internal(message)
                })?;
            tracing::Span::current().record("command.id", ack.command_id.as_str());
            tracing::Span::current().record("spec.graph.total_nodes", total_nodes);
            Ok(Response::new(pb::StartGraphRebuildResponse {
                rebuild_id: ack.command_id,
                started_at: ack.acknowledged_at,
                total_nodes,
            }))
        }
        .instrument(span)
        .await
    }
}

impl SpecificationGraphService {
    async fn add_evidence_relation_inner(
        &self,
        request: Request<pb::AddEvidenceRelationRequest>,
    ) -> Result<Response<pb::AddEvidenceRelationResponse>, Status> {
        let req = request.into_inner();
        let relation = match pb::EvidenceRelationKind::try_from(req.relation)
            .unwrap_or(pb::EvidenceRelationKind::Unspecified)
        {
            pb::EvidenceRelationKind::Affirms => crate::evidence_graph::Relation::Affirms,
            pb::EvidenceRelationKind::Denies => crate::evidence_graph::Relation::Denies,
            pb::EvidenceRelationKind::Unspecified => {
                return Err(Status::invalid_argument(
                    "Evidence relation must be affirms or denies",
                ))
            }
        };
        let relation_name = match relation {
            crate::evidence_graph::Relation::Affirms => "affirms",
            crate::evidence_graph::Relation::Denies => "denies",
        };
        tracing::Span::current().record("evidence.target", req.target.as_str());
        tracing::Span::current().record("evidence.relation", relation_name);
        let client = if req.client.is_empty() {
            "spec".into()
        } else {
            req.client
        };
        let client_version = if req.client_version.is_empty() {
            "unknown".into()
        } else {
            req.client_version
        };
        let (_, result) = self
            .commands
            .add_evidence_relation(AddEvidenceRelationInput {
                evidence: req.evidence,
                target: req.target,
                relation,
                now: chrono::Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Secs, true),
                client,
                client_version,
            })
            .await
            .map_err(evidence_command_status)?;
        tracing::Span::current().record("edge.id", result.edge.id.as_str());
        Ok(Response::new(pb::AddEvidenceRelationResponse {
            evidence_node: Some(convert::derived_node_to_pb(&result.evidence_node)),
            edge: Some(convert::edge_to_pb(&result.edge)),
            evidence_node_inserted: result.evidence_node_inserted,
            edge_inserted: result.edge_inserted,
        }))
    }

    async fn query_evidence_graph_inner(
        &self,
        request: Request<pb::QueryEvidenceGraphRequest>,
    ) -> Result<Response<pb::QueryEvidenceGraphResponse>, Status> {
        let req = request.into_inner();
        let query = crate::graph_query::GraphQuery::parse(&req.query)
            .and_then(|query| {
                query.validate(&crate::evidence_graph::query_schema())?;
                Ok(query)
            })
            .map_err(|error| Status::invalid_argument(error.to_string()))?;
        let limit = clamp_page_size(req.page_size) as usize;
        let after = (!req.page_token.is_empty()).then_some(req.page_token);
        let nodes = self.nodes.clone();
        let page = tokio::task::spawn_blocking(move || {
            nodes.query_evidence_graph(&query, after.as_deref(), limit)
        })
        .await
        .map_err(|error| Status::internal(format!("Evidence graph task failed: {error}")))?
        .map_err(|error| Status::internal(error.to_string()))?;
        tracing::Span::current().record(
            "evidence.page.node_count",
            page.selected_evidence_ids.len() as u64,
        );
        Ok(Response::new(pb::QueryEvidenceGraphResponse {
            evidence_nodes: page
                .evidence_nodes
                .iter()
                .map(convert::derived_node_to_pb)
                .collect(),
            edges: page.edges.iter().map(convert::edge_to_pb).collect(),
            specification_nodes: page
                .specification_nodes
                .iter()
                .map(convert::node_to_pb)
                .collect(),
            selected_evidence_ids: page.selected_evidence_ids,
            next_page_token: page.next_cursor.unwrap_or_default(),
            paths: page
                .paths
                .into_iter()
                .map(|path| pb::GraphPath {
                    id: path.id,
                    node_ids: path.node_ids,
                    edge_ids: path.edge_ids,
                })
                .collect(),
        }))
    }

    async fn get_ledger_inner(
        &self,
        request: Request<pb::GetLedgerRequest>,
    ) -> Result<Response<pb::GetLedgerResponse>, Status> {
        let req = request.into_inner();
        tracing::Span::current().record("ledger.page.requested_size", req.page_size as u64);
        let limit = clamp_page_size(req.page_size) as usize;
        let after = (!req.page_token.is_empty()).then_some(req.page_token);
        let nodes = self.nodes.clone();
        let read = tokio::task::spawn_blocking(move || -> Result<LedgerReadResult, StoreError> {
            let page = nodes.list_ledger_edges(after.as_deref(), limit)?;
            let mut owners: Vec<String> = page
                .edges
                .iter()
                .map(|edge| edge.page_owner().to_string())
                .collect();
            owners.sort();
            owners.dedup();
            let current: std::collections::BTreeSet<String> = nodes
                .list_edges(&owners, &crate::graph_generation::current_derivations())?
                .into_iter()
                .map(|edge| edge.id)
                .collect();
            let mut term_ids = Vec::new();
            let mut derived_ids = Vec::new();
            for edge in &page.edges {
                for (id, kind) in [
                    (&edge.source, edge.source_kind),
                    (&edge.target, edge.target_kind),
                ] {
                    match kind {
                        crate::domain::VertexKind::Term => term_ids.push(id.clone()),
                        crate::domain::VertexKind::Evidence
                        | crate::domain::VertexKind::Assumption
                        | crate::domain::VertexKind::Guarantee
                        | crate::domain::VertexKind::Contract
                        | crate::domain::VertexKind::Entity
                        | crate::domain::VertexKind::Behavior => derived_ids.push(id.clone()),
                        crate::domain::VertexKind::Specification => {}
                    }
                }
            }
            term_ids.sort();
            term_ids.dedup();
            derived_ids.sort();
            derived_ids.dedup();
            let terms = nodes.get_term_nodes(&term_ids)?;
            let derived = nodes.get_derived_nodes(&derived_ids)?;
            let total = nodes.count_edges()?;
            Ok((page, terms, derived, current, total))
        })
        .await
        .map_err(|error| Status::internal(format!("ledger read task failed to run: {error}")))?;
        let (page, terms, derived, current, total) = read.map_err(|error| {
            let message = error.to_string();
            tracing::Span::current().record("error.message", message.as_str());
            Status::internal(message)
        })?;
        let next_page_token = page.next_cursor.unwrap_or_default();
        tracing::Span::current().record("ledger.page.edge_count", page.edges.len() as u64);
        tracing::Span::current().record("ledger.page.has_next", !next_page_token.is_empty());
        tracing::Span::current().record("ledger.total_edges", total);
        Ok(Response::new(pb::GetLedgerResponse {
            edges: page
                .edges
                .iter()
                .map(|edge| convert::edge_to_pb_with_current(edge, current.contains(&edge.id)))
                .collect(),
            next_page_token,
            total_edges: total,
            term_nodes: terms.iter().map(convert::term_node_to_pb).collect(),
            derived_nodes: derived.iter().map(convert::derived_node_to_pb).collect(),
        }))
    }

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
            .commands
            .add(AddNodeInput {
                specification,
                evidence,
                now,
                cli,
                cli_version,
            })
            .await
        {
            Ok(node) => node,
            Err(CommandBusError::Add(e)) => {
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
            "specification accepted; post-acceptance Event published"
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
        let include_relation_assessments = req.include_relation_assessments;

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
        let read = tokio::task::spawn_blocking(move || -> Result<GraphReadResult, StoreError> {
            let _entered = read_span.enter();
            let page = nodes.list_nodes(after.as_deref(), limit)?;
            let ids: Vec<String> = page.nodes.iter().map(|n| n.id.clone()).collect();
            let derivations = crate::graph_generation::current_derivations();
            let population = nodes.selection_population(&ids, &derivations)?;
            let selection = crate::selection::derive_views(&ids, &population);
            let edges = nodes.list_edges(&ids, &derivations)?;
            let assessments = if include_relation_assessments {
                nodes.list_relation_assessments(&ids)?
            } else {
                Vec::new()
            };
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
            let mut derived_ids = Vec::new();
            for edge in &edges {
                for (id, kind) in [
                    (&edge.source, edge.source_kind),
                    (&edge.target, edge.target_kind),
                ] {
                    if matches!(
                        kind,
                        crate::domain::VertexKind::Evidence
                            | crate::domain::VertexKind::Assumption
                            | crate::domain::VertexKind::Guarantee
                            | crate::domain::VertexKind::Contract
                            | crate::domain::VertexKind::Entity
                            | crate::domain::VertexKind::Behavior
                    ) {
                        derived_ids.push(id.clone());
                    }
                }
            }
            derived_ids.sort();
            derived_ids.dedup();
            let derived = nodes.get_derived_nodes(&derived_ids)?;
            let total = nodes.count_nodes()?;
            Ok((page, terms, derived, edges, assessments, selection, total))
        })
        .await
        .map_err(|e| Status::internal(format!("graph read task failed to run: {e}")))?;

        let (page, terms, derived, edges, assessments, selection, total) = match read {
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

        let assumption_expressions: BTreeMap<&str, &str> = derived
            .iter()
            .filter_map(|node| match node {
                crate::domain::DerivedNode::Assumption { id, expression, .. } => {
                    Some((id.as_str(), expression.as_str()))
                }
                _ => None,
            })
            .collect();
        let current_assumptions: BTreeMap<&str, &str> = edges
            .iter()
            .filter(|edge| edge.kind == crate::domain::EdgeKind::HasAssumption)
            .filter_map(|edge| {
                assumption_expressions
                    .get(edge.target.as_str())
                    .copied()
                    .map(|expression| (edge.source.as_str(), expression))
            })
            .collect();

        Ok(Response::new(pb::GetGraphResponse {
            nodes: page
                .nodes
                .iter()
                .map(|node| {
                    let view = selection.get(&node.id).cloned().unwrap_or_default();
                    let mut wire = convert::node_to_pb_with_selection(node, &view);
                    if let Some(expression) = current_assumptions.get(node.id.as_str()) {
                        if let Some(contract) = wire
                            .sentence
                            .as_mut()
                            .and_then(|sentence| sentence.contract.as_mut())
                        {
                            contract.assumption = (*expression).to_string();
                        }
                    }
                    wire
                })
                .collect(),
            edges: edges.iter().map(convert::edge_to_pb).collect(),
            next_page_token,
            total_nodes: total,
            term_nodes: terms.iter().map(convert::term_node_to_pb).collect(),
            derived_nodes: derived.iter().map(convert::derived_node_to_pb).collect(),
            relation_assessments: assessments
                .iter()
                .map(convert::relation_assessment_to_pb)
                .collect(),
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

fn evidence_command_status(error: GraphCommandError) -> Status {
    let message = error.to_string();
    match error {
        GraphCommandError::Evidence(
            crate::evidence_graph::EvidenceRelationError::EmptyEvidence
            | crate::evidence_graph::EvidenceRelationError::EmptyTarget
            | crate::evidence_graph::EvidenceRelationError::Descriptor(_)
            | crate::evidence_graph::EvidenceRelationError::MultipleDescriptors
            | crate::evidence_graph::EvidenceRelationError::InvalidTarget(_)
            | crate::evidence_graph::EvidenceRelationError::InvalidEdge(_),
        ) => Status::invalid_argument(message),
        GraphCommandError::Evidence(
            crate::evidence_graph::EvidenceRelationError::MissingEvidence(_)
            | crate::evidence_graph::EvidenceRelationError::MissingTarget(_),
        ) => Status::not_found(message),
        _ => Status::internal(message),
    }
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
    use crate::command_bus::{
        CommandBus, EstablishContractRelationInput, ReplaceEvidenceRequestsInput,
    };
    use crate::consumer::{built_in_consumers, ConsumerRuntime};
    use crate::domain::{
        Anchor, DerivedNode, Edge, EdgeKind, Evidence, Kind, Locator, Meta, Node, Origin, Snapshot,
        VertexKind,
    };
    use crate::event_bus::EventBus;
    use crate::event_sink::EventTap;
    use crate::store::{BlobStore, GraphStore, InMemoryNodeStore, NodeStore, StoreError};

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

    fn start_runtime(
        store: Arc<InMemoryNodeStore>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
    ) -> (
        CommandBus,
        tokio::task::JoinHandle<()>,
        EventBus,
        tokio::task::JoinHandle<()>,
    ) {
        let (events, events_task) = EventBus::start(EventTap::default());
        let (commands, commands_task) = CommandBus::start(store, blobs, events.clone());
        (commands, commands_task, events, events_task)
    }

    async fn stop_runtime(
        commands: CommandBus,
        commands_task: tokio::task::JoinHandle<()>,
        events: EventBus,
        events_task: tokio::task::JoinHandle<()>,
    ) {
        events.shutdown().await.unwrap();
        events_task.await.unwrap();
        commands.shutdown().await.unwrap();
        commands_task.await.unwrap();
    }

    fn node(id: &str) -> Node {
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

    fn mark_graph_complete(store: &InMemoryNodeStore, id: &str) {
        let updates = [
            (
                "test-term",
                "term-projection",
                serde_json::json!({
                    "method": crate::graph_generation::TERM_DERIVATION_METHOD,
                    "version": crate::graph_generation::GENERATION_VERSION,
                    "operational_method": crate::graph_generation::OPERATIONAL_PROJECTION_METHOD,
                    "operational_version": crate::graph_generation::operational_projection_derivation().version,
                }),
            ),
            (
                "test-contract",
                "contract-projection",
                serde_json::json!({
                    "method": crate::graph_generation::CONTRACT_PROJECTION_METHOD,
                    "version": crate::graph_generation::CONTRACT_PROJECTION_VERSION,
                }),
            ),
            (
                "test-semantic",
                "semantic-relation",
                serde_json::json!({
                    "candidate_method": crate::graph_generation::CANDIDATE_METHOD,
                    "candidate_version": crate::graph_generation::CANDIDATE_VERSION,
                    "lexical_edge_method": crate::graph_generation::LEXICAL_AFFINITY_METHOD,
                    "lexical_edge_version": crate::graph_generation::lexical_affinity_derivation().version,
                    "edge_method": crate::graph_generation::SEMANTIC_EDGE_METHOD,
                    "edge_version": crate::graph_generation::semantic_edge_derivation().version,
                }),
            ),
        ];
        for (command_id, source, value) in updates {
            store
                .apply_command_update(
                    id,
                    command_id,
                    &crate::domain::MetaUpdate {
                        source: source.into(),
                        applied_at: "2026-01-01T00:00:00Z".into(),
                        value,
                    },
                    None,
                )
                .unwrap();
        }
    }

    fn ground(store: &InMemoryNodeStore, specification: &str, kind: Kind, locator: &str) {
        let evidence = DerivedNode::evidence(Evidence {
            kind,
            locator: Locator::parse(locator),
            snapshot: Snapshot {
                content: String::new(),
                content_hash: format!("hash-{locator}"),
                bytes: 1,
                captured_at: "t".into(),
                anchor: Anchor::Worktree,
            },
            origin: Origin::default(),
        });
        let edge = Edge::projection(
            EdgeKind::GroundedBy,
            specification,
            evidence.id(),
            crate::evidence_capture::evidence_derivation(),
            "t",
        )
        .unwrap();
        store.put_derived_node(&evidence, &edge).unwrap();
    }

    #[tokio::test]
    async fn get_graph_returns_a_bounded_page_with_cursor_and_total() {
        // The production in-memory backend — no bespoke test double needed.
        let store = Arc::new(InMemoryNodeStore::new());
        for id in ["n1", "n2", "n3"] {
            store.add_node(&node(id)).unwrap();
        }
        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) =
            start_runtime(store.clone(), blobs.clone());
        let service = SpecificationGraphService::new(store, commands.clone());

        // Page size 2 over 3 nodes: a full page plus a continuation token.
        let resp = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 2,
                page_token: String::new(),
                include_relation_assessments: false,
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
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(resp2.nodes.len(), 1);
        assert_eq!(resp2.nodes[0].id, "n3");
        assert!(resp2.next_page_token.is_empty(), "walk is complete");

        stop_runtime(commands, commands_task, events, events_task).await;
    }

    #[tokio::test]
    async fn start_graph_rebuild_returns_the_accepted_command_and_node_count() {
        let store = Arc::new(InMemoryNodeStore::new());
        for id in ["n1", "n2"] {
            store.add_node(&node(id)).unwrap();
        }
        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let service = SpecificationGraphService::new(store, commands.clone());

        let response = service
            .start_graph_rebuild(Request::new(pb::StartGraphRebuildRequest {
                client: "spec".to_string(),
                client_version: "test".to_string(),
            }))
            .await
            .unwrap()
            .into_inner();

        assert!(!response.rebuild_id.is_empty());
        assert!(!response.started_at.is_empty());
        assert_eq!(response.total_nodes, 2);

        stop_runtime(commands, commands_task, events, events_task).await;
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
                relied_spec_id: None,
                basis_spec_ids: vec![],
                derivation: crate::graph_generation::semantic_edge_derivation(),
                recorded_at: "t".into(),
            })
            .unwrap();
        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let service = SpecificationGraphService::new(store, commands.clone());

        let first = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 1,
                page_token: String::new(),
                include_relation_assessments: false,
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
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(second.nodes[0].id, "z");
        assert!(
            second.edges.is_empty(),
            "owner paging must not duplicate the Edge"
        );

        stop_runtime(commands, commands_task, events, events_task).await;
    }

    #[tokio::test]
    async fn graph_page_includes_adjacent_assumption_and_guarantee_nodes() {
        let store = Arc::new(InMemoryNodeStore::new());
        let specification = node("contract-spec");
        store.add_node(&specification).unwrap();
        crate::graph_generation::generate_and_persist(&specification, &*store, "t").unwrap();
        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let service = SpecificationGraphService::new(store, commands.clone());

        let response = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        assert_eq!(response.derived_nodes.len(), 5);
        assert!(response.edges.iter().any(|edge| {
            edge.kind == pb::EdgeKind::HasAssumption as i32
                && edge.target_kind == pb::VertexKind::Assumption as i32
        }));
        assert!(response.edges.iter().any(|edge| {
            edge.kind == pb::EdgeKind::HasGuarantee as i32
                && edge.target_kind == pb::VertexKind::Guarantee as i32
        }));
        assert!(response.edges.iter().any(|edge| {
            edge.kind == pb::EdgeKind::HasBehavior as i32
                && edge.target_kind == pb::VertexKind::Behavior as i32
        }));
        assert!(response.edges.iter().any(|edge| {
            edge.kind == pb::EdgeKind::EngagesEntity as i32
                && edge.target_kind == pb::VertexKind::Entity as i32
        }));

        stop_runtime(commands, commands_task, events, events_task).await;
    }

    #[tokio::test]
    async fn graph_page_returns_relation_assessments_only_when_requested() {
        let store = Arc::new(InMemoryNodeStore::new());
        for id in ["a", "b"] {
            let specification = node(id);
            store.add_node(&specification).unwrap();
            crate::graph_generation::generate_and_persist(&specification, &*store, "t").unwrap();
        }
        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let service = SpecificationGraphService::new(store, commands.clone());

        let ordinary = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        assert!(ordinary.relation_assessments.is_empty());

        let audited = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: true,
            }))
            .await
            .unwrap()
            .into_inner();
        assert!(!audited.relation_assessments.is_empty());

        stop_runtime(commands, commands_task, events, events_task).await;
    }

    #[tokio::test]
    async fn accumulating_evidence_reselects_the_better_supported_coherent_set() {
        let store = Arc::new(InMemoryNodeStore::new());
        store.add_node(&node("candidate-a")).unwrap();
        store.add_node(&node("candidate-z")).unwrap();
        mark_graph_complete(&store, "candidate-a");
        mark_graph_complete(&store, "candidate-z");
        let conflict = Edge::specification_relation(
            EdgeKind::HardContradiction,
            "candidate-a",
            "candidate-z",
            vec![],
            crate::graph_generation::semantic_edge_derivation(),
            "t0",
        )
        .unwrap();
        store.append_edge(&conflict).unwrap();
        ground(&store, "candidate-a", Kind::Unknown, "candidate-a-hint");
        ground(
            &store,
            "candidate-z",
            Kind::Assertoric,
            "candidate-z-policy",
        );
        let edge_count_before = store.count_edges().unwrap();

        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let service = SpecificationGraphService::new(store.clone(), commands.clone());
        let graph = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        let selected: std::collections::BTreeSet<&str> = graph
            .nodes
            .iter()
            .filter(|node| node.selection.as_ref().is_some_and(|view| view.current))
            .map(|node| node.id.as_str())
            .collect();
        assert_eq!(selected, std::collections::BTreeSet::from(["candidate-z"]));

        // A newly accumulated, stronger independent proof changes only the
        // derived view. The losing candidate and every older Edge remain in
        // the Ledger.
        ground(
            &store,
            "candidate-a",
            Kind::Demonstrative,
            "candidate-a-proof",
        );
        let graph = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        let selected: std::collections::BTreeSet<&str> = graph
            .nodes
            .iter()
            .filter(|node| node.selection.as_ref().is_some_and(|view| view.current))
            .map(|node| node.id.as_str())
            .collect();
        assert_eq!(selected, std::collections::BTreeSet::from(["candidate-a"]));
        let winner = graph
            .nodes
            .iter()
            .find(|node| node.id == "candidate-a")
            .unwrap()
            .selection
            .as_ref()
            .unwrap();
        assert_eq!(winner.support_score, 18);
        assert_eq!(
            winner
                .contributions
                .iter()
                .map(|contribution| contribution.points)
                .sum::<i32>(),
            winner.support_score
        );
        let loser = graph
            .nodes
            .iter()
            .find(|node| node.id == "candidate-z")
            .unwrap()
            .selection
            .as_ref()
            .unwrap();
        assert_eq!(loser.exclusions[0].kind, "contradicted");
        assert_eq!(store.count_edges().unwrap(), edge_count_before + 1);

        stop_runtime(commands, commands_task, events, events_task).await;
    }

    #[tokio::test]
    async fn refresh_replaces_fitness_input_while_ledger_keeps_every_capture() {
        let temp = tempfile::tempdir().unwrap();
        let evidence_path = temp.path().join("pump-proof.txt");
        std::fs::write(&evidence_path, "proof-v1").unwrap();
        let locator = evidence_path.to_string_lossy();
        let positive = serde_json::json!({
            "kind": "demonstrative",
            "locator": locator.as_ref(),
        })
        .to_string();
        let counter = serde_json::json!({
            "kind": "counter",
            "locator": locator.as_ref(),
        })
        .to_string();

        let store = Arc::new(InMemoryNodeStore::new());
        let blobs =
            Arc::new(crate::store::FileBlobStore::open(&temp.path().join("blobs")).unwrap());
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let consumers = ConsumerRuntime::start(
            events.clone(),
            commands.clone(),
            store.clone(),
            built_in_consumers()
                .into_iter()
                .filter(|definition| definition.consumer_id == crate::evidence_capture::PLUGIN_NAME)
                .collect(),
        )
        .await
        .unwrap();
        let service = SpecificationGraphService::new(store.clone(), commands.clone());

        let accepted = service
            .add_specification(Request::new(pb::AddSpecificationRequest {
                specification: "The pump shall stop.".into(),
                evidence: vec![positive.clone()],
                client: "test".into(),
                client_version: "test".into(),
            }))
            .await
            .unwrap()
            .into_inner()
            .node
            .unwrap();
        let first =
            wait_for_captured_evidence(&store, &accepted.id, None, Kind::Demonstrative, None).await;
        mark_graph_complete(&store, &accepted.id);
        let first_hash = first.meta.evidence[0].snapshot.content_hash.clone();

        let graph = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        let first_view = graph.nodes[0].selection.as_ref().unwrap();
        assert!(first_view.current);
        assert_eq!(first_view.support_score, 20);
        assert_eq!(first_view.contributions.len(), 1);

        // The descriptor is intentionally unchanged. The persisted request
        // generation, rather than descriptor hash or wall-clock resolution,
        // forces a fresh snapshot after the artifact changes.
        std::fs::write(&evidence_path, "proof-v2").unwrap();
        let refreshed = commands
            .replace_evidence_requests(ReplaceEvidenceRequestsInput {
                node_id: accepted.id.clone(),
                evidence: vec![positive],
                now: chrono::Utc::now().to_rfc3339(),
            })
            .await
            .unwrap();
        let generation = refreshed.meta.evidence_request_generation.clone();
        assert!(!generation.is_empty());
        let second = wait_for_captured_evidence(
            &store,
            &accepted.id,
            Some(&generation),
            Kind::Demonstrative,
            Some(&first_hash),
        )
        .await;
        let second_hash = second.meta.evidence[0].snapshot.content_hash.clone();
        assert_ne!(first_hash, second_hash);

        // Reclassifying the same locator as Counter Evidence makes the old
        // positive GroundedBy edges inert for fitness without deleting them.
        let replaced = commands
            .replace_evidence_requests(ReplaceEvidenceRequestsInput {
                node_id: accepted.id.clone(),
                evidence: vec![counter],
                now: chrono::Utc::now().to_rfc3339(),
            })
            .await
            .unwrap();
        let generation = replaced.meta.evidence_request_generation.clone();
        wait_for_captured_evidence(&store, &accepted.id, Some(&generation), Kind::Counter, None)
            .await;
        let graph = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        let view = graph.nodes[0].selection.as_ref().unwrap();
        assert!(!view.current);
        assert_eq!(view.support_score, -20);
        assert_eq!(view.contributions.len(), 1);
        assert_eq!(view.contributions[0].kind, "counter_evidence");
        assert_eq!(
            graph
                .edges
                .iter()
                .filter(|edge| edge.kind == pb::EdgeKind::GroundedBy as i32)
                .count(),
            1,
            "the current graph exposes only the current Evidence projection"
        );

        let ledger = store.list_ledger_edges(None, 100).unwrap();
        assert_eq!(
            ledger
                .edges
                .iter()
                .filter(|edge| edge.kind == EdgeKind::GroundedBy)
                .count(),
            3,
            "all three immutable captures remain auditable"
        );
        let wire_ledger = service
            .get_ledger(Request::new(pb::GetLedgerRequest {
                page_size: 100,
                page_token: String::new(),
            }))
            .await
            .unwrap()
            .into_inner();
        let grounding: Vec<&pb::Edge> = wire_ledger
            .edges
            .iter()
            .filter(|edge| edge.kind == pb::EdgeKind::GroundedBy as i32)
            .collect();
        assert_eq!(grounding.len(), 3);
        assert_eq!(
            grounding.iter().filter(|edge| edge.current).count(),
            1,
            "Ledger distinguishes the one current capture from two historical projections"
        );

        events.shutdown().await.unwrap();
        events_task.await.unwrap();
        consumers.join().await;
        commands.shutdown().await.unwrap();
        commands_task.await.unwrap();
    }

    async fn wait_for_captured_evidence(
        store: &InMemoryNodeStore,
        node_id: &str,
        generation: Option<&str>,
        kind: Kind,
        different_from_hash: Option<&str>,
    ) -> Node {
        for _ in 0..200 {
            let node = store.get_node(node_id).unwrap().unwrap();
            let generation_matches =
                generation.is_none_or(|expected| node.meta.evidence_request_generation == expected);
            let evidence_matches = node
                .meta
                .evidence
                .as_slice()
                .first()
                .is_some_and(|evidence| {
                    evidence.kind == kind
                        && different_from_hash
                            .is_none_or(|old| evidence.snapshot.content_hash != old)
                });
            if generation_matches && evidence_matches {
                return node;
            }
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
        panic!("timed out waiting for Evidence capture of {node_id}");
    }

    #[tokio::test]
    async fn assumption_command_exposes_explicit_reliance_and_current_paired_contract() {
        let store = Arc::new(InMemoryNodeStore::new());
        let mut source = node("source");
        source.statement = "The sensor shall report the alarm.".into();
        let mut target = node("target");
        target.statement = "The controller shall stop the pump.".into();
        store.add_node(&source).unwrap();
        store.add_node(&target).unwrap();
        crate::graph_generation::generate_and_persist(&target, &*store, "t0").unwrap();
        let blobs = Arc::new(NoBlobs);
        let (commands, commands_task, events, events_task) = start_runtime(store.clone(), blobs);
        let service = SpecificationGraphService::new(store, commands.clone());

        let (_, paired) = commands
            .establish_guarantee_discharge(EstablishContractRelationInput {
                source: source.id.clone(),
                target: target.id.clone(),
                relied: source.id.clone(),
                basis_spec_ids: vec![],
                now: "t1".into(),
            })
            .await
            .unwrap();
        assert_eq!(paired.relied_spec_id.as_deref(), Some(source.id.as_str()));
        assert_eq!(paired.family(), crate::domain::EdgeFamily::Semantic);

        let graph = service
            .get_graph(Request::new(pb::GetGraphRequest {
                page_size: 10,
                page_token: String::new(),
                include_relation_assessments: false,
            }))
            .await
            .unwrap()
            .into_inner();
        let target_wire = graph
            .nodes
            .iter()
            .find(|node| node.id == target.id)
            .unwrap();
        assert_eq!(
            target_wire
                .sentence
                .as_ref()
                .and_then(|sentence| sentence.contract.as_ref())
                .map(|contract| contract.assumption.as_str()),
            Some(source.statement.as_str())
        );
        let assumption_edges: Vec<&pb::Edge> = graph
            .edges
            .iter()
            .filter(|edge| {
                edge.source == target.id && edge.kind == pb::EdgeKind::HasAssumption as i32
            })
            .collect();
        assert_eq!(assumption_edges.len(), 1);
        assert_eq!(
            assumption_edges[0].derivation.as_ref().unwrap().method,
            crate::pairing::PAIRED_PROJECTION_METHOD
        );
        let ledger = service
            .get_ledger(Request::new(pb::GetLedgerRequest {
                page_size: 100,
                page_token: String::new(),
            }))
            .await
            .unwrap()
            .into_inner();
        let historical_assumptions: Vec<&pb::Edge> = ledger
            .edges
            .iter()
            .filter(|edge| {
                edge.source == target.id && edge.kind == pb::EdgeKind::HasAssumption as i32
            })
            .collect();
        assert_eq!(historical_assumptions.len(), 2);
        assert_eq!(
            historical_assumptions
                .iter()
                .filter(|edge| edge.current)
                .count(),
            1
        );
        assert!(historical_assumptions.iter().any(|edge| {
            !edge.current
                && edge.derivation.as_ref().unwrap().method
                    == crate::graph_generation::CONTRACT_PROJECTION_METHOD
        }));

        stop_runtime(commands, commands_task, events, events_task).await;
    }
}
