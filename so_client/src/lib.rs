//! A thin client for the `spec_oracle.v1.SpecificationGraph` service.
//!
//! The client is deliberately minimal: it resolves the caller's input *channels*
//! (`@file` / `-`(stdin) / inline) into concrete text — the one thing that cannot
//! cross the wire, because it names the client's own streams — and forwards the
//! specification plus resolved Evidence descriptors to the daemon. The Add RPC
//! parses and persists one Node; locator capture happens later in a daemon Job.
//! The returned protobuf Node is handed back unchanged; the daemon owns the
//! domain model.
//!
//! Note the division of labor: **channel** resolution (reading the client's files
//! and stdin) happens here; **locator** capture (snapshotting whatever the
//! evidence points at) happens in a daemon Job. A file evidence value therefore
//! refers to a path on the *daemon's* filesystem, even though an `@file` channel
//! reads the descriptor from the *client's*.

use std::io::Read;

use thiserror::Error;

use so_protocol::pb;
use so_protocol::pb::specification_graph_client::SpecificationGraphClient;

use tonic::transport::Channel;
use tonic::Request;
use tracing::Instrument;

// A graph page contains authored Nodes plus their attached Term/Derived Nodes
// and Edges. At the protocol's 1,000-Node page ceiling that envelope can exceed
// tonic's 4 MiB default, and the unpaged current-set response can be larger
// still. Keep the transport ceiling comfortably above those protocol payloads.
const MAX_DECODING_MESSAGE_SIZE: usize = 64 * 1024 * 1024;

/// Failure resolving an evidence input channel (client-side files/stdin).
#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("failed to read evidence from '{path}': {source}")]
    Read {
        path: String,
        source: std::io::Error,
    },
    #[error("failed to read evidence from stdin: {0}")]
    Stdin(std::io::Error),
}

/// Anything that can go wrong talking to the service.
#[derive(Debug, Error)]
pub enum ClientError {
    #[error(transparent)]
    Channel(#[from] ChannelError),
    #[error("failed to connect to spec-oracle daemon: {0}")]
    Connect(tonic::transport::Error),
    #[error("daemon returned an error: {0}")]
    Status(#[from] tonic::Status),
    #[error("daemon response contained no nodes")]
    EmptyResponse,
    #[error("daemon response contained no selection edge")]
    EmptySelectionResponse,
    #[error("daemon response contained no assumption edge")]
    EmptyAssumptionResponse,
    #[error("daemon response contained no promoted discharge edge")]
    EmptyDischargePromotionResponse,
    #[error("daemon response contained no derived contract")]
    EmptyDerivedContractResponse,
    #[error("daemon returned an invalid graph response: {0}")]
    InvalidGraphResponse(String),
}

impl ClientError {
    /// Whether this is bad input the caller can fix — a client-side channel error
    /// or a daemon `INVALID_ARGUMENT` — as opposed to a connection/runtime
    /// failure. Lets the CLI pick a usage vs. runtime exit code without depending
    /// on tonic itself.
    pub fn is_bad_input(&self) -> bool {
        match self {
            ClientError::Channel(_) => true,
            ClientError::Status(status) => matches!(
                status.code(),
                tonic::Code::InvalidArgument | tonic::Code::NotFound
            ),
            _ => false,
        }
    }
}

/// Resolve the `@path` / `-`(stdin) / inline input channel to raw text. This is
/// the only client-side reading step: the resolved text is what the daemon then
/// interprets and captures.
pub fn resolve_channel(arg: &str) -> Result<String, ChannelError> {
    if arg == "-" {
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .map_err(ChannelError::Stdin)?;
        return Ok(buf);
    }
    if let Some(path) = arg.strip_prefix('@') {
        return std::fs::read_to_string(path).map_err(|source| ChannelError::Read {
            path: path.to_string(),
            source,
        });
    }
    Ok(arg.to_string())
}

/// One bounded page of the specification graph, as returned by [`Client::get_graph`].
/// The nodes and their induced edges are handed back in their protobuf form (the
/// daemon owns the domain model); `next_page_token` is empty on the last page.
pub struct GraphPage {
    pub nodes: Vec<pb::Node>,
    pub term_nodes: Vec<pb::TermNode>,
    pub derived_nodes: Vec<pb::DerivedNode>,
    pub edges: Vec<pb::Edge>,
    pub relation_assessments: Vec<pb::RelationAssessment>,
    pub next_page_token: String,
    pub total_nodes: u64,
}

/// One bounded page of immutable Ledger Edges and their non-Specification
/// endpoint values.
pub struct LedgerPage {
    pub edges: Vec<pb::Edge>,
    pub term_nodes: Vec<pb::TermNode>,
    pub derived_nodes: Vec<pb::DerivedNode>,
    pub next_page_token: String,
    pub total_edges: u64,
}

/// A connected client for the SpecificationGraph service.
pub struct Client {
    inner: SpecificationGraphClient<Channel>,
}

impl Client {
    /// Connect to a daemon endpoint (e.g. `http://127.0.0.1:50051`).
    pub async fn connect(endpoint: String) -> Result<Client, ClientError> {
        let span = tracing::info_span!(
            "spec.client.connect",
            "server.address" = %endpoint
        );
        async move {
            let inner = SpecificationGraphClient::connect(endpoint)
                .await
                .map_err(ClientError::Connect)?
                .max_decoding_message_size(MAX_DECODING_MESSAGE_SIZE);
            Ok(Client { inner })
        }
        .instrument(span)
        .await
    }

    /// Add a specification: resolve each evidence channel to text, send the
    /// request, and return the one accepted Specification Node. Evidence
    /// descriptors remain opaque; capture happens asynchronously in `specd`.
    pub async fn add(
        &mut self,
        specification: &str,
        evidence_args: &[String],
        client: &str,
        client_version: &str,
    ) -> Result<pb::Node, ClientError> {
        let policy = so_tracing::capture_policy();
        let span = tracing::info_span!(
            "spec.client.add_specification",
            "spec.telemetry.capture" = policy.as_str(),
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "AddSpecification",
            "spec.specification.length" = specification.len() as u64,
            "spec.evidence.arg_count" = evidence_args.len() as u64,
            "spec.evidence.resolved_count" = tracing::field::Empty,
            "spec.specification.hash" = tracing::field::Empty,
            "spec.specification.text" = tracing::field::Empty,
            "client.name" = %client,
            "client.version" = %client_version,
        );
        so_tracing::record_specification_on_span(&span, policy, specification);
        async {
            let mut evidence = Vec::with_capacity(evidence_args.len());
            for arg in evidence_args {
                evidence.push(resolve_channel(arg)?);
            }
            tracing::Span::current().record("spec.evidence.resolved_count", evidence.len() as u64);

            let mut request = Request::new(pb::AddSpecificationRequest {
                specification: specification.to_string(),
                evidence,
                client: client.to_string(),
                client_version: client_version.to_string(),
            });
            so_tracing::inject_context(request.metadata_mut());

            let response = self.inner.add_specification(request).await?.into_inner();
            let node = response.node.ok_or(ClientError::EmptyResponse)?;
            tracing::info!(
                "node.id" = %node.id,
                "specification add completed"
            );
            Ok(node)
        }
        .instrument(span)
        .await
    }

    /// Replace the complete Evidence descriptor set for an existing
    /// specification. Input channels are resolved client-side exactly as for
    /// Add; locator capture remains asynchronous in the daemon.
    pub async fn replace_evidence(
        &mut self,
        node_id: &str,
        evidence_args: &[String],
    ) -> Result<pb::Node, ClientError> {
        let span = tracing::info_span!(
            "spec.client.replace_evidence",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "ReplaceEvidence",
            "node.id" = %node_id,
            "spec.evidence.arg_count" = evidence_args.len() as u64,
        );
        async {
            let mut evidence = Vec::with_capacity(evidence_args.len());
            for arg in evidence_args {
                evidence.push(resolve_channel(arg)?);
            }
            let mut request = Request::new(pb::ReplaceEvidenceRequest {
                node_id: node_id.to_string(),
                evidence,
            });
            so_tracing::inject_context(request.metadata_mut());
            self.inner
                .replace_evidence(request)
                .await?
                .into_inner()
                .node
                .ok_or(ClientError::EmptyResponse)
        }
        .instrument(span)
        .await
    }

    /// Append one explicit selection judgment between existing Specification
    /// Nodes. The daemon validates the endpoints and owns the fixed policy
    /// derivation attached to the resulting Edge.
    pub async fn add_selection_relation(
        &mut self,
        source: &str,
        target: &str,
        kind: pb::EdgeKind,
        basis_spec_ids: &[String],
    ) -> Result<pb::Edge, ClientError> {
        let span = tracing::info_span!(
            "spec.client.add_selection_relation",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "AddSelectionRelation",
            "selection.kind" = ?kind,
            "selection.source" = %source,
            "selection.target" = %target,
            "selection.basis_count" = basis_spec_ids.len() as u64,
        );
        async {
            let mut request = Request::new(pb::AddSelectionRelationRequest {
                source: source.to_string(),
                target: target.to_string(),
                kind: kind as i32,
                basis_spec_ids: basis_spec_ids.to_vec(),
            });
            so_tracing::inject_context(request.metadata_mut());
            self.inner
                .add_selection_relation(request)
                .await?
                .into_inner()
                .edge
                .ok_or(ClientError::EmptySelectionResponse)
        }
        .instrument(span)
        .await
    }

    /// Append one proved assume-guarantee pairing between authored
    /// Specification Nodes. `relied` names the assertion the target actually
    /// awaits; the daemon performs all semantic and aggregate validation.
    pub async fn add_assumption_relation(
        &mut self,
        source: &str,
        target: &str,
        relied: &str,
        kind: pb::EdgeKind,
        basis_spec_ids: &[String],
    ) -> Result<pb::Edge, ClientError> {
        let span = tracing::info_span!(
            "spec.client.add_assumption_relation",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "AddAssumptionRelation",
            "pairing.kind" = ?kind,
            "pairing.source" = %source,
            "pairing.target" = %target,
            "pairing.relied" = %relied,
            "pairing.basis_count" = basis_spec_ids.len() as u64,
        );
        async {
            let mut request = Request::new(pb::AddAssumptionRelationRequest {
                source: source.to_string(),
                target: target.to_string(),
                relied: relied.to_string(),
                kind: kind as i32,
                basis_spec_ids: basis_spec_ids.to_vec(),
            });
            so_tracing::inject_context(request.metadata_mut());
            self.inner
                .add_assumption_relation(request)
                .await?
                .into_inner()
                .edge
                .ok_or(ClientError::EmptyAssumptionResponse)
        }
        .instrument(span)
        .await
    }

    /// Explicitly promote a proved discharge Assessment to the ordinary
    /// GuaranteeDischarge topology. The daemon revalidates the pairing.
    pub async fn promote_discharge_candidate(
        &mut self,
        assessment_id: &str,
    ) -> Result<pb::Edge, ClientError> {
        let span = tracing::info_span!(
            "spec.client.promote_discharge_candidate",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "PromoteDischargeCandidate",
            "assessment.id" = %assessment_id,
        );
        async {
            let mut request = Request::new(pb::PromoteDischargeCandidateRequest {
                assessment_id: assessment_id.to_string(),
            });
            so_tracing::inject_context(request.metadata_mut());
            self.inner
                .promote_discharge_candidate(request)
                .await?
                .into_inner()
                .edge
                .ok_or(ClientError::EmptyDischargePromotionResponse)
        }
        .instrument(span)
        .await
    }

    pub async fn derive_contract(
        &mut self,
        left_contract_id: &str,
        right_contract_id: &str,
        operation: pb::ContractOperation,
        basis_spec_ids: &[String],
    ) -> Result<(pb::DerivedNode, Vec<pb::Edge>), ClientError> {
        let span = tracing::info_span!(
            "spec.client.derive_contract",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "DeriveContract",
            "contract.left" = %left_contract_id,
            "contract.right" = %right_contract_id,
            "contract.operation" = ?operation,
        );
        async {
            let mut request = Request::new(pb::DeriveContractRequest {
                left_contract_id: left_contract_id.to_string(),
                right_contract_id: right_contract_id.to_string(),
                operation: operation as i32,
                basis_spec_ids: basis_spec_ids.to_vec(),
            });
            so_tracing::inject_context(request.metadata_mut());
            let response = self.inner.derive_contract(request).await?.into_inner();
            let contract = response
                .contract
                .ok_or(ClientError::EmptyDerivedContractResponse)?;
            Ok((contract, response.derivation_edges))
        }
        .instrument(span)
        .await
    }

    /// Read one bounded page of the specification graph. `page_size` of 0 lets
    /// the daemon choose its default; the daemon clamps it to a hard maximum, so
    /// this never fetches the whole graph. `page_token` is the opaque cursor from
    /// a previous page's `next_page_token` (empty starts from the beginning).
    ///
    /// An empty page is a valid result (the graph may be empty, or the cursor may
    /// have reached the end), so — unlike [`Client::add`] — this returns it rather
    /// than treating it as an error.
    pub async fn get_graph(
        &mut self,
        page_size: u32,
        page_token: &str,
    ) -> Result<GraphPage, ClientError> {
        let span = tracing::info_span!(
            "spec.client.get_graph",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "GetGraph",
            "spec.page.requested_size" = page_size as u64,
            "spec.page.has_cursor" = !page_token.is_empty(),
            "spec.page.node_count" = tracing::field::Empty,
            "spec.page.edge_count" = tracing::field::Empty,
            "spec.page.has_next" = tracing::field::Empty,
            "spec.graph.total_nodes" = tracing::field::Empty,
        );
        async {
            let mut request = Request::new(pb::GetGraphRequest {
                page_size,
                page_token: page_token.to_string(),
            });
            so_tracing::inject_context(request.metadata_mut());

            let response = self.inner.get_graph(request).await?.into_inner();
            tracing::Span::current().record("spec.page.node_count", response.nodes.len() as u64);
            tracing::Span::current().record("spec.page.edge_count", response.edges.len() as u64);
            tracing::Span::current()
                .record("spec.page.has_next", !response.next_page_token.is_empty());
            tracing::Span::current().record("spec.graph.total_nodes", response.total_nodes);
            tracing::info!(
                "spec.page.node_count" = response.nodes.len() as u64,
                "spec.graph.total_nodes" = response.total_nodes,
                "graph page fetched"
            );
            Ok(GraphPage {
                nodes: response.nodes,
                term_nodes: response.term_nodes,
                derived_nodes: response.derived_nodes,
                edges: response.edges,
                relation_assessments: response.relation_assessments,
                next_page_token: response.next_page_token,
                total_nodes: response.total_nodes,
            })
        }
        .instrument(span)
        .await
    }

    pub async fn get_ledger(
        &mut self,
        page_size: u32,
        page_token: &str,
    ) -> Result<LedgerPage, ClientError> {
        let span = tracing::info_span!(
            "spec.client.get_ledger",
            "rpc.system" = "grpc",
            "rpc.service" = "spec_oracle.v1.SpecificationGraph",
            "rpc.method" = "GetLedger",
            "ledger.page.requested_size" = page_size as u64,
            "ledger.page.has_cursor" = !page_token.is_empty(),
        );
        async {
            let mut request = Request::new(pb::GetLedgerRequest {
                page_size,
                page_token: page_token.to_string(),
            });
            so_tracing::inject_context(request.metadata_mut());
            let response = self.inner.get_ledger(request).await?.into_inner();
            Ok(LedgerPage {
                edges: response.edges,
                term_nodes: response.term_nodes,
                derived_nodes: response.derived_nodes,
                next_page_token: response.next_page_token,
                total_edges: response.total_edges,
            })
        }
        .instrument(span)
        .await
    }
}
