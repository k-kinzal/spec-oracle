//! The tonic service implementing the `spec_oracle.v1.ContractGraph` contract.
//!
//! The RPC layer is thin: it decodes the request, stamps the daemon-authoritative
//! creation instant (sense ③), and drives the synchronous [`add`] pipeline on a
//! blocking thread (`spawn_blocking`), since capture touches the filesystem, git,
//! the network, and the blocking ArangoDB driver — none of which may run on the
//! async reactor. The resulting node is converted to its protobuf form and
//! returned; ingest errors map to gRPC status codes the client turns into exit
//! codes (`INVALID_ARGUMENT` → bad input, `INTERNAL` → runtime failure).

use std::sync::Arc;

use tonic::{Request, Response, Status};
use tracing::Instrument;

use crate::domain::Node;
use so_protocol::pb;
use so_protocol::pb::contract_graph_server::ContractGraph;

use crate::add::{self, AddError, AddRequest};
use crate::store::{BlobStore, NodeStore};

/// The ingest service, holding the two persistence seams behind `Arc`s so each
/// request can hand them to a blocking task. Both trait objects are `Send + Sync`
/// so they can cross the `spawn_blocking` boundary and be shared across requests.
pub struct ContractGraphService {
    nodes: Arc<dyn NodeStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
}

impl ContractGraphService {
    pub fn new(
        nodes: Arc<dyn NodeStore + Send + Sync>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
    ) -> ContractGraphService {
        ContractGraphService { nodes, blobs }
    }
}

#[tonic::async_trait]
impl ContractGraph for ContractGraphService {
    async fn add_contract(
        &self,
        request: Request<pb::AddContractRequest>,
    ) -> Result<Response<pb::AddContractResponse>, Status> {
        let policy = so_tracing::capture_policy();
        let span = tracing::info_span!(
            "spec.daemon.add_contract",
            "spec.telemetry.capture" = policy.as_str(),
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.ContractGraph",
            "rpc.method" = "AddContract",
            "client.name" = tracing::field::Empty,
            "client.version" = tracing::field::Empty,
            "spec.statement.length" = tracing::field::Empty,
            "spec.evidence.count" = tracing::field::Empty,
            "spec.statement.hash" = tracing::field::Empty,
            "spec.statement.text" = tracing::field::Empty,
            "error.category" = tracing::field::Empty,
            "error.stage" = tracing::field::Empty,
            "error.kind" = tracing::field::Empty,
            "error.message" = tracing::field::Empty,
            "node.id" = tracing::field::Empty,
        );
        so_tracing::set_span_parent_from_metadata(&span, request.metadata());
        async move { self.add_contract_inner(request).await }
            .instrument(span)
            .await
    }
}

impl ContractGraphService {
    async fn add_contract_inner(
        &self,
        request: Request<pb::AddContractRequest>,
    ) -> Result<Response<pb::AddContractResponse>, Status> {
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

        let statement = req.statement;
        let evidence = req.evidence;
        tracing::Span::current().record("client.name", cli.as_str());
        tracing::Span::current().record("client.version", cli_version.as_str());
        tracing::Span::current().record("spec.statement.length", statement.len() as u64);
        tracing::Span::current().record("spec.evidence.count", evidence.len() as u64);
        let current = tracing::Span::current();
        so_tracing::record_statement_on_span(&current, policy, &statement);

        let nodes = self.nodes.clone();
        let blobs = self.blobs.clone();

        let ingest_span = tracing::info_span!(
            "spec.daemon.ingest_blocking",
            "spec.statement.length" = statement.len() as u64,
            "spec.evidence.count" = evidence.len() as u64,
        );
        let outcome = tokio::task::spawn_blocking(move || -> Result<Node, AddError> {
            let _entered = ingest_span.enter();
            let add_req = AddRequest {
                statement: &statement,
                evidence_values: &evidence,
                now: &now,
                cli: &cli,
                cli_version: &cli_version,
            };
            add::run(&add_req, &*nodes, &*blobs)
        })
        .await
        .map_err(|e| Status::internal(format!("ingest task failed to run: {e}")))?;

        let node = match outcome {
            Ok(node) => node,
            Err(e) => {
                record_add_error(policy, &e);
                return Err(add_error_to_status(e));
            }
        };
        tracing::Span::current().record("node.id", node.id.as_str());
        tracing::info!("node.id" = %node.id, "contract ingest completed");
        Ok(Response::new(pb::AddContractResponse {
            node: Some(pb::Node::from(&node)),
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
                "contract ingest failed"
            );
        }
        so_tracing::CapturePolicy::Diagnostic => {
            tracing::Span::current().record("error.kind", error.diagnostic_kind());
            tracing::warn!(
                "error.category" = error.category(),
                "error.stage" = error.stage(),
                "error.kind" = error.diagnostic_kind(),
                "spec.telemetry.capture" = policy.as_str(),
                "contract ingest failed"
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
                "contract ingest failed"
            );
        }
    }
}

/// Map an ingest failure to a gRPC status. Bad input (grammar/evidence) is
/// `INVALID_ARGUMENT`; environment/runtime failure (capture/store) is `INTERNAL`.
/// The client maps these back to its exit codes.
fn add_error_to_status(e: AddError) -> Status {
    match e {
        AddError::Grammar(_) | AddError::Evidence(_) => Status::invalid_argument(e.to_string()),
        AddError::Snapshot(_) | AddError::Store(_) => Status::internal(e.to_string()),
    }
}
