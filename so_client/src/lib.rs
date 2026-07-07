//! A thin client for the `spec_oracle.v1.SpecificationGraph` service.
//!
//! The client is deliberately minimal: it resolves the caller's input *channels*
//! (`@file` / `-`(stdin) / inline) into concrete text — the one thing that cannot
//! cross the wire, because it names the client's own streams — and forwards the
//! specification plus the resolved evidence values to the daemon, which performs
//! all parsing, capture, and persistence. The returned protobuf nodes (one per
//! sentence) are handed back unchanged; the daemon owns the domain model.
//!
//! Note the division of labor: **channel** resolution (reading the client's files
//! and stdin) happens here; **locator** capture (snapshotting whatever the
//! evidence points at) happens in the daemon. A file evidence value therefore
//! refers to a path on the *daemon's* filesystem, even though an `@file` channel
//! reads the descriptor from the *client's*.

use std::io::Read;

use thiserror::Error;

use so_protocol::pb;
use so_protocol::pb::specification_graph_client::SpecificationGraphClient;

use tonic::transport::Channel;
use tonic::Request;
use tracing::Instrument;

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
}

impl ClientError {
    /// Whether this is bad input the caller can fix — a client-side channel error
    /// or a daemon `INVALID_ARGUMENT` — as opposed to a connection/runtime
    /// failure. Lets the CLI pick a usage vs. runtime exit code without depending
    /// on tonic itself.
    pub fn is_bad_input(&self) -> bool {
        match self {
            ClientError::Channel(_) => true,
            ClientError::Status(status) => status.code() == tonic::Code::InvalidArgument,
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
                .map_err(ClientError::Connect)?;
            Ok(Client { inner })
        }
        .instrument(span)
        .await
    }

    /// Add a specification: resolve each evidence channel to text, send the
    /// request, and return the persisted nodes (one per sentence, in input
    /// order) in their protobuf form.
    pub async fn add(
        &mut self,
        specification: &str,
        evidence_args: &[String],
        client: &str,
        client_version: &str,
    ) -> Result<Vec<pb::Node>, ClientError> {
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
            if response.nodes.is_empty() {
                return Err(ClientError::EmptyResponse);
            }
            tracing::info!(
                "node.count" = response.nodes.len() as u64,
                "specification add completed"
            );
            Ok(response.nodes)
        }
        .instrument(span)
        .await
    }
}
