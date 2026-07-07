//! The tonic service implementing the `spec_oracle.v1.SpecificationGraph`
//! wire contract.
//!
//! The RPC layer is thin: it decodes the request, stamps the daemon-authoritative
//! creation instant (sense ③), and drives the synchronous [`add`] pipeline on a
//! blocking thread (`spawn_blocking`), since capture touches the filesystem, git,
//! the network, and the blocking ArangoDB driver — none of which may run on the
//! async reactor. The resulting nodes (one per sentence) are converted to their
//! protobuf form — deriving each sentence's response-time view — and returned;
//! ingest errors map to gRPC status codes the client turns into exit codes
//! (`INVALID_ARGUMENT` → bad input, `INTERNAL` → runtime failure).

use std::sync::Arc;

use tonic::{Request, Response, Status};
use tracing::Instrument;

use crate::domain::Node;
use so_protocol::pb;
use so_protocol::pb::specification_graph_server::SpecificationGraph;

use crate::add::{self, AddError, AddRequest};
use crate::convert;
use crate::store::{BlobStore, NodeStore};

/// The ingest service, holding the two persistence seams behind `Arc`s so each
/// request can hand them to a blocking task. Both trait objects are `Send + Sync`
/// so they can cross the `spawn_blocking` boundary and be shared across requests.
pub struct SpecificationGraphService {
    nodes: Arc<dyn NodeStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
}

impl SpecificationGraphService {
    pub fn new(
        nodes: Arc<dyn NodeStore + Send + Sync>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
    ) -> SpecificationGraphService {
        SpecificationGraphService { nodes, blobs }
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
            "spec.evidence.count" = tracing::field::Empty,
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
        tracing::Span::current().record("spec.evidence.count", evidence.len() as u64);
        let current = tracing::Span::current();
        so_tracing::record_specification_on_span(&current, policy, &specification);

        let nodes = self.nodes.clone();
        let blobs = self.blobs.clone();

        let ingest_span = tracing::info_span!(
            "spec.daemon.ingest_blocking",
            "spec.specification.length" = specification.len() as u64,
            "spec.evidence.count" = evidence.len() as u64,
        );
        let outcome = tokio::task::spawn_blocking(move || -> Result<Vec<Node>, AddError> {
            let _entered = ingest_span.enter();
            let add_req = AddRequest {
                specification: &specification,
                evidence_values: &evidence,
                now: &now,
                cli: &cli,
                cli_version: &cli_version,
            };
            add::run(&add_req, &*nodes, &*blobs)
        })
        .await
        .map_err(|e| Status::internal(format!("ingest task failed to run: {e}")))?;

        let persisted = match outcome {
            Ok(persisted) => persisted,
            Err(e) => {
                record_add_error(policy, &e);
                return Err(add_error_to_status(e));
            }
        };
        tracing::Span::current().record("spec.sentence.count", persisted.len() as u64);
        tracing::Span::current().record("node.count", persisted.len() as u64);
        if let Some(first) = persisted.first() {
            tracing::Span::current().record("node.id", first.id.as_str());
        }
        tracing::info!(
            "node.count" = persisted.len() as u64,
            "specification ingest completed"
        );
        Ok(Response::new(pb::AddSpecificationResponse {
            nodes: persisted.iter().map(convert::node_to_pb).collect(),
        }))
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

/// Map an ingest failure to a gRPC status. Bad input is `INVALID_ARGUMENT`:
/// syntax errors, malformed evidence values, and the snapshot failures the
/// caller can fix from the request alone (an evidence file that does not
/// exist, a line out of range). Environment/runtime failure (other capture
/// failures, store) is `INTERNAL`; a store failure never leaves a partial
/// specification behind (ingest rolls back already-persisted sentences,
/// best-effort, before the error surfaces). The client maps these statuses
/// back to its exit codes.
fn add_error_to_status(e: AddError) -> Status {
    match &e {
        AddError::Grammar(_) | AddError::Evidence(_) => Status::invalid_argument(e.to_string()),
        AddError::Snapshot(s) if snapshot_is_bad_input(s) => {
            Status::invalid_argument(e.to_string())
        }
        AddError::Snapshot(_) | AddError::Store(_) => Status::internal(e.to_string()),
    }
}

/// Snapshot failures the caller can fix by correcting the request. A missing
/// evidence file is classified as bad input: the common case is a typo'd
/// locator, and treating it as a runtime failure would hide it behind exit 1.
fn snapshot_is_bad_input(e: &crate::snapshot::SnapshotError) -> bool {
    use crate::snapshot::SnapshotError;
    matches!(
        e,
        SnapshotError::NotFound(_) | SnapshotError::LineOutOfRange { .. }
    )
}
