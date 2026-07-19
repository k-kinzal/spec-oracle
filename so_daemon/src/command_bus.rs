//! Volatile Commands and their handlers.
//!
//! Commands request work; successful handlers acknowledge the Command and
//! publish fresh facts to the [`EventBus`](crate::event_bus::EventBus). Command
//! identity is process-local and idempotent while the daemon remains alive.
//! Neither Commands nor Events are a substitute for the append-only graph
//! Ledger.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use thiserror::Error;
use tokio::sync::{mpsc, oneshot};

use crate::add::{self, AddError, AddRequest};
use crate::domain::{MetaUpdate, Node};
use crate::event_bus::{EventBus, EventKind, EventRequest};
use crate::identity::{derive_id, new_message_id};
use crate::store::{BlobStore, GraphStore, StoreError};

const COMMAND_MAILBOX_CAPACITY: usize = 256;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "PascalCase")]
pub enum CommandKind {
    AddNode,
    ReplaceEvidenceRequests,
    StartGraphRebuild,
    BeginNodeGraphRebuild,
    CompleteGraphRebuildPage,
    DeriveContract,
    EstablishOccurrenceReliance,
    EstablishGuaranteeDischarge,
    EstablishAdmissibilityEnvelope,
    AcceptDischargeCandidate,
    ProjectNodeTerms,
    ProjectNodeContract,
    CaptureEvidence,
    PinGithubEvidenceToCommit,
    AssessNodeSemanticRelations,
    AssessNodeContractRelations,
    AssessNodeDischargeCandidates,
}

impl CommandKind {
    /// The concrete Event type produced when this Command changes state.
    ///
    /// This is intentionally one-to-one. Abstract Event categories belong to
    /// subscription matching and never replace these concrete facts.
    pub const fn event_kind(self) -> EventKind {
        match self {
            CommandKind::AddNode => EventKind::NodeAdded,
            CommandKind::ReplaceEvidenceRequests => EventKind::EvidenceRequestsReplaced,
            CommandKind::StartGraphRebuild => EventKind::GraphRebuildStarted,
            CommandKind::BeginNodeGraphRebuild => EventKind::NodeGraphRebuildStarted,
            CommandKind::CompleteGraphRebuildPage => EventKind::GraphRebuildPageCompleted,
            CommandKind::DeriveContract => EventKind::ContractDerived,
            CommandKind::EstablishOccurrenceReliance => EventKind::OccurrenceRelianceEstablished,
            CommandKind::EstablishGuaranteeDischarge => EventKind::GuaranteeDischargeEstablished,
            CommandKind::EstablishAdmissibilityEnvelope => {
                EventKind::AdmissibilityEnvelopeEstablished
            }
            CommandKind::AcceptDischargeCandidate => EventKind::DischargeCandidateAccepted,
            CommandKind::ProjectNodeTerms => EventKind::NodeTermsProjected,
            CommandKind::ProjectNodeContract => EventKind::NodeContractProjected,
            CommandKind::CaptureEvidence => EventKind::EvidenceCaptured,
            CommandKind::PinGithubEvidenceToCommit => EventKind::GithubEvidencePinnedToCommit,
            CommandKind::AssessNodeSemanticRelations => {
                EventKind::NodeSemanticRelationAssessmentCompleted
            }
            CommandKind::AssessNodeContractRelations => {
                EventKind::NodeContractRelationAssessmentCompleted
            }
            CommandKind::AssessNodeDischargeCandidates => {
                EventKind::NodeDischargeCandidateAssessmentCompleted
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct CommandEnvelope {
    pub id: String,
    pub kind: CommandKind,
    pub issued_at: String,
    pub correlation_id: String,
    pub causation_id: Option<String>,
    pub payload: Value,
}

impl CommandEnvelope {
    pub fn new(kind: CommandKind, payload: Value) -> CommandEnvelope {
        let id = new_message_id();
        CommandEnvelope {
            correlation_id: id.clone(),
            id,
            kind,
            issued_at: now(),
            causation_id: None,
            payload,
        }
    }

    pub fn caused_by_consumer(
        consumer_id: &str,
        event: &crate::event_bus::EventEnvelope,
        operation: &str,
        kind: CommandKind,
        payload: Value,
    ) -> CommandEnvelope {
        CommandEnvelope {
            id: derive_id("consumer-command", &[consumer_id, &event.id, operation]),
            kind,
            issued_at: now(),
            correlation_id: event.correlation_id.clone(),
            causation_id: Some(event.id.clone()),
            payload,
        }
    }

    pub fn caused_by_consumer_with_key(
        consumer_id: &str,
        event: &crate::event_bus::EventEnvelope,
        operation: &str,
        key: &str,
        kind: CommandKind,
        payload: Value,
    ) -> CommandEnvelope {
        CommandEnvelope {
            id: derive_id(
                "consumer-command",
                &[consumer_id, &event.id, operation, key],
            ),
            kind,
            issued_at: now(),
            correlation_id: event.correlation_id.clone(),
            causation_id: Some(event.id.clone()),
            payload,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandAck {
    pub command_id: String,
    pub acknowledged_at: String,
}

pub struct AddNodeInput {
    pub specification: String,
    pub evidence: Vec<String>,
    pub now: String,
    pub cli: String,
    pub cli_version: String,
}

pub struct ReplaceEvidenceRequestsInput {
    pub node_id: String,
    pub evidence: Vec<String>,
    pub now: String,
}

pub struct StartGraphRebuildInput {
    pub client: String,
    pub client_version: String,
}

pub struct EstablishContractRelationInput {
    pub source: String,
    pub target: String,
    pub relied: String,
    pub basis_spec_ids: Vec<String>,
    pub now: String,
}

pub struct AcceptDischargeCandidateInput {
    pub assessment_id: String,
    pub now: String,
}

pub struct DeriveContractInput {
    pub left_contract_id: String,
    pub right_contract_id: String,
    pub operation: crate::contract_algebra::Operation,
    pub basis_spec_ids: Vec<String>,
    pub now: String,
}

#[derive(Clone)]
pub struct CommandBus {
    sender: mpsc::Sender<Message>,
}

#[derive(Debug, Error)]
pub enum CommandBusError {
    #[error(transparent)]
    Add(#[from] AddError),
    #[error("Command Bus is closed")]
    Closed,
    #[error("Command Bus stopped before replying")]
    ReplyDropped,
    #[error("Command Bus stopped before shutdown completed")]
    ShutdownDropped,
}

#[derive(Debug, Error)]
pub enum ReplaceEvidenceRequestsError {
    #[error(transparent)]
    Store(#[from] StoreError),
    #[error("Command Bus is closed")]
    Closed,
    #[error("Command Bus stopped before replying")]
    ReplyDropped,
}

#[derive(Debug, Error)]
pub enum ExecuteCommandError {
    #[error("Command kind {0:?} is not a Consumer processing Command")]
    Unsupported(CommandKind),
    #[error("Command processing failed: {0}")]
    Processing(String),
    #[error("Event Bus rejected a Command Event: {0}")]
    Event(#[from] crate::event_bus::EventBusError),
    #[error("Command Bus is closed")]
    Closed,
    #[error("Command Bus stopped before replying")]
    ReplyDropped,
}

#[derive(Debug, Error)]
pub enum GraphCommandError {
    #[error("Command Handler task failed: {0}")]
    Worker(String),
    #[error(transparent)]
    Pairing(#[from] crate::pairing::PairingError),
    #[error(transparent)]
    Algebra(#[from] crate::contract_algebra::AlgebraError),
    #[error(transparent)]
    Store(#[from] StoreError),
    #[error(transparent)]
    Event(#[from] crate::event_bus::EventBusError),
    #[error("Command Bus is closed")]
    Closed,
    #[error("Command Bus stopped before replying")]
    ReplyDropped,
}

enum Message {
    AddNode {
        command: CommandEnvelope,
        input: AddNodeInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<(CommandAck, Node), AddError>>,
    },
    ReplaceEvidenceRequests {
        command: CommandEnvelope,
        input: ReplaceEvidenceRequestsInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<(CommandAck, Node), StoreError>>,
    },
    StartGraphRebuild {
        command: CommandEnvelope,
        input: StartGraphRebuildInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<(CommandAck, u64), GraphCommandError>>,
    },
    EstablishContractRelation {
        command: CommandEnvelope,
        kind: crate::domain::EdgeKind,
        input: EstablishContractRelationInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<(CommandAck, crate::domain::Edge), GraphCommandError>>,
    },
    AcceptDischargeCandidate {
        command: CommandEnvelope,
        input: AcceptDischargeCandidateInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<(CommandAck, crate::domain::Edge), GraphCommandError>>,
    },
    DeriveContract {
        command: CommandEnvelope,
        input: DeriveContractInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<
            Result<(CommandAck, crate::contract_algebra::DerivationResult), GraphCommandError>,
        >,
    },
    Process {
        command: CommandEnvelope,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<CommandAck, ExecuteCommandError>>,
    },
    Shutdown {
        reply: oneshot::Sender<()>,
    },
}

#[derive(Clone)]
enum CompletedCommand {
    AddNode(CommandAck, Node),
    ReplaceEvidenceRequests(CommandAck, Node),
    StartGraphRebuild(CommandAck, u64),
    EstablishContractRelation(CommandAck, crate::domain::Edge),
    AcceptDischargeCandidate(CommandAck, crate::domain::Edge),
    DeriveContract(CommandAck, crate::contract_algebra::DerivationResult),
    Processing(CommandAck),
}

impl CommandBus {
    pub fn start(
        graph: Arc<dyn GraphStore + Send + Sync>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
        events: EventBus,
    ) -> (CommandBus, tokio::task::JoinHandle<()>) {
        let (sender, receiver) = mpsc::channel(COMMAND_MAILBOX_CAPACITY);
        let bus = CommandBus { sender };
        let task = tokio::spawn(run(receiver, graph, blobs, events));
        (bus, task)
    }

    pub async fn add(&self, input: AddNodeInput) -> Result<Node, CommandBusError> {
        self.add_command(
            CommandEnvelope::new(
                CommandKind::AddNode,
                json!({
                    "specification": input.specification,
                    "evidence": input.evidence,
                }),
            ),
            input,
        )
        .await
        .map(|(_, node)| node)
    }

    pub async fn add_command(
        &self,
        command: CommandEnvelope,
        input: AddNodeInput,
    ) -> Result<(CommandAck, Node), CommandBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::AddNode {
                command,
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| CommandBusError::Closed)?;
        received
            .await
            .map_err(|_| CommandBusError::ReplyDropped)?
            .map_err(CommandBusError::Add)
    }

    pub async fn replace_evidence_requests(
        &self,
        input: ReplaceEvidenceRequestsInput,
    ) -> Result<Node, ReplaceEvidenceRequestsError> {
        let command = CommandEnvelope::new(
            CommandKind::ReplaceEvidenceRequests,
            json!({
                "node_id": input.node_id,
                "evidence": input.evidence,
            }),
        );
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::ReplaceEvidenceRequests {
                command,
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| ReplaceEvidenceRequestsError::Closed)?;
        received
            .await
            .map_err(|_| ReplaceEvidenceRequestsError::ReplyDropped)?
            .map(|(_, node)| node)
            .map_err(ReplaceEvidenceRequestsError::Store)
    }

    pub async fn start_graph_rebuild(
        &self,
        input: StartGraphRebuildInput,
    ) -> Result<(CommandAck, u64), GraphCommandError> {
        let command = CommandEnvelope::new(
            CommandKind::StartGraphRebuild,
            json!({
                "client": input.client,
                "client_version": input.client_version,
            }),
        );
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::StartGraphRebuild {
                command,
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| GraphCommandError::Closed)?;
        received
            .await
            .map_err(|_| GraphCommandError::ReplyDropped)?
    }

    pub async fn establish_occurrence_reliance(
        &self,
        input: EstablishContractRelationInput,
    ) -> Result<(CommandAck, crate::domain::Edge), GraphCommandError> {
        self.establish_contract_relation(
            CommandKind::EstablishOccurrenceReliance,
            crate::domain::EdgeKind::OccurrenceReliance,
            input,
        )
        .await
    }

    pub async fn establish_guarantee_discharge(
        &self,
        input: EstablishContractRelationInput,
    ) -> Result<(CommandAck, crate::domain::Edge), GraphCommandError> {
        self.establish_contract_relation(
            CommandKind::EstablishGuaranteeDischarge,
            crate::domain::EdgeKind::GuaranteeDischarge,
            input,
        )
        .await
    }

    pub async fn establish_admissibility_envelope(
        &self,
        input: EstablishContractRelationInput,
    ) -> Result<(CommandAck, crate::domain::Edge), GraphCommandError> {
        self.establish_contract_relation(
            CommandKind::EstablishAdmissibilityEnvelope,
            crate::domain::EdgeKind::AdmissibilityEnvelope,
            input,
        )
        .await
    }

    async fn establish_contract_relation(
        &self,
        command_kind: CommandKind,
        relation_kind: crate::domain::EdgeKind,
        input: EstablishContractRelationInput,
    ) -> Result<(CommandAck, crate::domain::Edge), GraphCommandError> {
        let command = CommandEnvelope::new(
            command_kind,
            json!({
                "kind": relation_kind.as_str(),
                "source": input.source,
                "target": input.target,
                "relied": input.relied,
                "basis_spec_ids": input.basis_spec_ids,
            }),
        );
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::EstablishContractRelation {
                command,
                kind: relation_kind,
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| GraphCommandError::Closed)?;
        received
            .await
            .map_err(|_| GraphCommandError::ReplyDropped)?
    }

    pub async fn accept_discharge_candidate(
        &self,
        input: AcceptDischargeCandidateInput,
    ) -> Result<(CommandAck, crate::domain::Edge), GraphCommandError> {
        let command = CommandEnvelope::new(
            CommandKind::AcceptDischargeCandidate,
            json!({"assessment_id": input.assessment_id}),
        );
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::AcceptDischargeCandidate {
                command,
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| GraphCommandError::Closed)?;
        received
            .await
            .map_err(|_| GraphCommandError::ReplyDropped)?
    }

    pub async fn derive_contract(
        &self,
        input: DeriveContractInput,
    ) -> Result<(CommandAck, crate::contract_algebra::DerivationResult), GraphCommandError> {
        let command = CommandEnvelope::new(
            CommandKind::DeriveContract,
            json!({
                "left_contract_id": input.left_contract_id,
                "right_contract_id": input.right_contract_id,
                "operation": input.operation.as_str(),
                "basis_spec_ids": input.basis_spec_ids,
            }),
        );
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::DeriveContract {
                command,
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| GraphCommandError::Closed)?;
        received
            .await
            .map_err(|_| GraphCommandError::ReplyDropped)?
    }

    /// Submit a Command produced by an Event Consumer. Completion is reported
    /// only after the Handler has persisted its Ledger changes and the Event
    /// Bus has accepted every corresponding Event.
    pub async fn process(
        &self,
        command: CommandEnvelope,
    ) -> Result<CommandAck, ExecuteCommandError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Process {
                command,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| ExecuteCommandError::Closed)?;
        received
            .await
            .map_err(|_| ExecuteCommandError::ReplyDropped)?
    }

    pub async fn shutdown(&self) -> Result<(), CommandBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Shutdown { reply })
            .await
            .map_err(|_| CommandBusError::Closed)?;
        received.await.map_err(|_| CommandBusError::ShutdownDropped)
    }
}

async fn run(
    mut receiver: mpsc::Receiver<Message>,
    graph: Arc<dyn GraphStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
    events: EventBus,
) {
    let mut completed: HashMap<String, CompletedCommand> = HashMap::new();
    while let Some(message) = receiver.recv().await {
        match message {
            Message::AddNode {
                command,
                input,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::AddNode(ack, node)) = completed.get(&command.id) {
                    let _ = reply.send(Ok((ack.clone(), node.clone())));
                    continue;
                }
                let command_id = command.id.clone();
                let operation_id = command.id.clone();
                let graph = graph.clone();
                let worker_parent = parent_span.clone();
                let write = tokio::task::spawn_blocking(move || {
                    let span = tracing::info_span!(
                        parent: &worker_parent,
                        "spec.command.add_node",
                        "command.id" = %operation_id,
                    );
                    let _entered = span.enter();
                    let request = AddRequest {
                        message_id: &operation_id,
                        specification: &input.specification,
                        evidence_values: &input.evidence,
                        now: &input.now,
                        cli: &input.cli,
                        cli_version: &input.cli_version,
                    };
                    add::run_with_status(&request, &*graph)
                })
                .await;
                match write {
                    Ok(Ok(status)) => {
                        let ack = CommandAck {
                            command_id: command_id.clone(),
                            acknowledged_at: now(),
                        };
                        completed.insert(
                            command_id.clone(),
                            CompletedCommand::AddNode(ack.clone(), status.node.clone()),
                        );
                        // The Command Ack is observable before the resulting
                        // Event is accepted. A process crash in this narrow gap
                        // is part of the explicitly volatile contract.
                        let _ = reply.send(Ok((ack, status.node.clone())));
                        let request = EventRequest::new(command.kind.event_kind(), &command_id)
                            .with_subject(&status.node.id)
                            .with_payload(
                                serde_json::to_value(&status.node).expect("Node is serializable"),
                            )
                            .with_correlation(command.correlation_id)
                            .with_parent(parent_span);
                        if let Err(error) = events.publish(request).await {
                            tracing::error!(
                                "command.id" = %command_id,
                                "error.message" = %error,
                                "NodeAdded Event could not enter the Event Bus"
                            );
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(error));
                    }
                    Err(error) => {
                        tracing::error!(
                            "command.id" = %command_id,
                            "error.message" = %error,
                            "AddNode Command worker failed"
                        );
                        drop(reply);
                    }
                }
            }
            Message::ReplaceEvidenceRequests {
                command,
                input,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::ReplaceEvidenceRequests(ack, node)) =
                    completed.get(&command.id)
                {
                    let _ = reply.send(Ok((ack.clone(), node.clone())));
                    continue;
                }
                let command_id = command.id.clone();
                let operation_id = command.id.clone();
                let graph = graph.clone();
                let worker_parent = parent_span.clone();
                let write = tokio::task::spawn_blocking(move || {
                    let span = tracing::info_span!(
                        parent: &worker_parent,
                        "spec.command.replace_evidence_requests",
                        "command.id" = %operation_id,
                        "node.id" = %input.node_id,
                        "spec.evidence.request_count" = input.evidence.len() as u64,
                    );
                    let _entered = span.enter();
                    let update = crate::domain::MetaUpdate {
                        source: crate::evidence_capture::REQUEST_UPDATE_SOURCE.to_string(),
                        applied_at: input.now,
                        value: json!({
                            "generation": operation_id.clone(),
                            "evidence_requests": input.evidence,
                        }),
                    };
                    let requests: Vec<String> = update.value["evidence_requests"]
                        .as_array()
                        .expect("request update stores an array")
                        .iter()
                        .filter_map(Value::as_str)
                        .map(str::to_string)
                        .collect();
                    graph.replace_evidence_requests(
                        &input.node_id,
                        &requests,
                        &operation_id,
                        &update,
                    )
                })
                .await;
                match write {
                    Ok(Ok(node)) => {
                        let ack = CommandAck {
                            command_id: command_id.clone(),
                            acknowledged_at: now(),
                        };
                        completed.insert(
                            command_id.clone(),
                            CompletedCommand::ReplaceEvidenceRequests(ack.clone(), node.clone()),
                        );
                        let _ = reply.send(Ok((ack, node.clone())));
                        let request = EventRequest::new(command.kind.event_kind(), &command_id)
                            .with_subject(&node.id)
                            .with_payload(
                                serde_json::to_value(&node).expect("Node is serializable"),
                            )
                            .with_correlation(command.correlation_id)
                            .with_parent(parent_span);
                        if let Err(error) = events.publish(request).await {
                            tracing::error!(
                                "command.id" = %command_id,
                                "error.message" = %error,
                                "EvidenceRequestsReplaced Event could not enter the Event Bus"
                            );
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(error));
                    }
                    Err(error) => {
                        tracing::error!(
                            "command.id" = %command_id,
                            "error.message" = %error,
                            "ReplaceEvidence Command worker failed"
                        );
                        drop(reply);
                    }
                }
            }
            Message::StartGraphRebuild {
                command,
                input,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::StartGraphRebuild(ack, total_nodes)) =
                    completed.get(&command.id)
                {
                    let _ = reply.send(Ok((ack.clone(), *total_nodes)));
                    continue;
                }
                let graph = graph.clone();
                let worker_parent = parent_span.clone();
                let counted = tokio::task::spawn_blocking(move || {
                    let _entered = tracing::info_span!(
                        parent: &worker_parent,
                        "spec.command.start_graph_rebuild",
                    )
                    .entered();
                    graph.count_nodes()
                })
                .await;
                match counted {
                    Ok(Ok(total_nodes)) => {
                        let ack = command_ack(&command);
                        let request = command_event_request(
                            &command,
                            command.kind.event_kind(),
                            vec![command.id.clone()],
                            json!({
                                "rebuild_id": command.id.clone(),
                                "client": input.client,
                                "client_version": input.client_version,
                                "total_nodes": total_nodes,
                                "after": null,
                                "processed_nodes": 0,
                                "derivations": crate::graph_generation::current_derivations(),
                            }),
                            parent_span,
                        );
                        match events.publish(request).await {
                            Ok(_) => {
                                completed.insert(
                                    command.id,
                                    CompletedCommand::StartGraphRebuild(ack.clone(), total_nodes),
                                );
                                let _ = reply.send(Ok((ack, total_nodes)));
                            }
                            Err(error) => {
                                let _ = reply.send(Err(GraphCommandError::Event(error)));
                            }
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(GraphCommandError::Store(error)));
                    }
                    Err(error) => {
                        let _ = reply.send(Err(GraphCommandError::Worker(error.to_string())));
                    }
                }
            }
            Message::EstablishContractRelation {
                command,
                kind,
                input,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::EstablishContractRelation(ack, edge)) =
                    completed.get(&command.id)
                {
                    let _ = reply.send(Ok((ack.clone(), edge.clone())));
                    continue;
                }
                let graph = graph.clone();
                let worker_parent = parent_span.clone();
                let written = tokio::task::spawn_blocking(move || {
                    let _entered = tracing::info_span!(
                        parent: &worker_parent,
                        "spec.command.establish_contract_relation",
                    )
                    .entered();
                    crate::pairing::append_relation(
                        &*graph,
                        kind,
                        &input.source,
                        &input.target,
                        &input.relied,
                        input.basis_spec_ids,
                        &input.now,
                    )
                })
                .await;
                match written {
                    Ok(Ok(edge)) => {
                        let ack = command_ack(&command);
                        let request = command_event_request(
                            &command,
                            command.kind.event_kind(),
                            vec![edge.target.clone(), edge.id.clone()],
                            json!({"edge_id": edge.id}),
                            parent_span,
                        );
                        match events.publish(request).await {
                            Ok(_) => {
                                completed.insert(
                                    command.id,
                                    CompletedCommand::EstablishContractRelation(
                                        ack.clone(),
                                        edge.clone(),
                                    ),
                                );
                                let _ = reply.send(Ok((ack, edge)));
                            }
                            Err(error) => {
                                let _ = reply.send(Err(GraphCommandError::Event(error)));
                            }
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(GraphCommandError::Pairing(error)));
                    }
                    Err(error) => {
                        let _ = reply.send(Err(GraphCommandError::Worker(error.to_string())));
                    }
                }
            }
            Message::AcceptDischargeCandidate {
                command,
                input,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::AcceptDischargeCandidate(ack, edge)) =
                    completed.get(&command.id)
                {
                    let _ = reply.send(Ok((ack.clone(), edge.clone())));
                    continue;
                }
                let assessment_id = input.assessment_id.clone();
                let graph = graph.clone();
                let worker_parent = parent_span.clone();
                let written = tokio::task::spawn_blocking(move || {
                    let _entered = tracing::info_span!(
                        parent: &worker_parent,
                        "spec.command.accept_discharge_candidate",
                    )
                    .entered();
                    crate::pairing::accept_discharge_candidate(
                        &*graph,
                        &input.assessment_id,
                        &input.now,
                    )
                })
                .await;
                match written {
                    Ok(Ok(edge)) => {
                        let ack = command_ack(&command);
                        let request = command_event_request(
                            &command,
                            command.kind.event_kind(),
                            vec![edge.target.clone(), edge.id.clone()],
                            json!({
                                "assessment_id": assessment_id,
                                "edge_id": edge.id,
                            }),
                            parent_span,
                        );
                        match events.publish(request).await {
                            Ok(_) => {
                                completed.insert(
                                    command.id,
                                    CompletedCommand::AcceptDischargeCandidate(
                                        ack.clone(),
                                        edge.clone(),
                                    ),
                                );
                                let _ = reply.send(Ok((ack, edge)));
                            }
                            Err(error) => {
                                let _ = reply.send(Err(GraphCommandError::Event(error)));
                            }
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(GraphCommandError::Pairing(error)));
                    }
                    Err(error) => {
                        let _ = reply.send(Err(GraphCommandError::Worker(error.to_string())));
                    }
                }
            }
            Message::DeriveContract {
                command,
                input,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::DeriveContract(ack, derivation)) =
                    completed.get(&command.id)
                {
                    let _ = reply.send(Ok((ack.clone(), derivation.clone())));
                    continue;
                }
                let graph = graph.clone();
                let worker_parent = parent_span.clone();
                let written = tokio::task::spawn_blocking(move || {
                    let _entered = tracing::info_span!(
                        parent: &worker_parent,
                        "spec.command.derive_contract",
                    )
                    .entered();
                    crate::contract_algebra::derive(
                        &*graph,
                        &input.left_contract_id,
                        &input.right_contract_id,
                        input.operation,
                        input.basis_spec_ids,
                        &input.now,
                    )
                })
                .await;
                match written {
                    Ok(Ok(derivation)) => {
                        let ack = command_ack(&command);
                        let request = command_event_request(
                            &command,
                            EventKind::ContractDerived,
                            vec![derivation.contract.id().to_string()],
                            json!({
                                "contract_id": derivation.contract.id(),
                                "derivation": crate::contract_algebra::DERIVATION_VERSION,
                            }),
                            parent_span,
                        );
                        match events.publish(request).await {
                            Ok(_) => {
                                completed.insert(
                                    command.id,
                                    CompletedCommand::DeriveContract(
                                        ack.clone(),
                                        derivation.clone(),
                                    ),
                                );
                                let _ = reply.send(Ok((ack, derivation)));
                            }
                            Err(error) => {
                                let _ = reply.send(Err(GraphCommandError::Event(error)));
                            }
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(GraphCommandError::Algebra(error)));
                    }
                    Err(error) => {
                        let _ = reply.send(Err(GraphCommandError::Worker(error.to_string())));
                    }
                }
            }
            Message::Process {
                command,
                parent_span,
                reply,
            } => {
                if let Some(CompletedCommand::Processing(ack)) = completed.get(&command.id) {
                    let _ = reply.send(Ok(ack.clone()));
                    continue;
                }
                let result = process_consumer_command(
                    &command,
                    graph.clone(),
                    blobs.clone(),
                    &events,
                    parent_span,
                )
                .await;
                if let Ok(ack) = &result {
                    completed.insert(
                        command.id.clone(),
                        CompletedCommand::Processing(ack.clone()),
                    );
                }
                let _ = reply.send(result);
            }
            Message::Shutdown { reply } => {
                let _ = reply.send(());
                break;
            }
        }
    }
}

async fn process_consumer_command(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    match command.kind {
        CommandKind::BeginNodeGraphRebuild => {
            handle_begin_node_graph_rebuild(command, graph, events, parent_span).await
        }
        CommandKind::CompleteGraphRebuildPage => {
            handle_complete_graph_rebuild_page(command, events, parent_span).await
        }
        CommandKind::ProjectNodeTerms => {
            handle_project_node_terms(command, graph, events, parent_span).await
        }
        CommandKind::ProjectNodeContract => {
            handle_project_node_contract(command, graph, events, parent_span).await
        }
        CommandKind::CaptureEvidence => {
            handle_capture_evidence(command, graph, blobs, events, parent_span).await
        }
        CommandKind::PinGithubEvidenceToCommit => {
            handle_github_evidence(command, graph, blobs, events, parent_span).await
        }
        CommandKind::AssessNodeSemanticRelations => {
            handle_semantic_relations(command, graph, events, parent_span).await
        }
        CommandKind::AssessNodeContractRelations => {
            handle_contract_relations(command, graph, events, parent_span).await
        }
        CommandKind::AssessNodeDischargeCandidates => {
            handle_discharge_candidates(command, graph, events, parent_span).await
        }
        kind => Err(ExecuteCommandError::Unsupported(kind)),
    }
}

async fn handle_begin_node_graph_rebuild(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let rebuild_id = processing_payload_string(command, "rebuild_id")?;
    let command_id = command.id.clone();
    let recorded = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        let recorded_at = now();
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "graph-rebuild".to_string(),
                applied_at: recorded_at,
                value: json!({
                    "rebuild_id": rebuild_id.clone(),
                    "state": "started",
                }),
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, rebuild_id)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, rebuild_id)) = recorded {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id.clone()],
            json!({
                "rebuild_id": rebuild_id,
                "node_id": node_id,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_complete_graph_rebuild_page(
    command: &CommandEnvelope,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let rebuild_id = processing_payload_string(command, "rebuild_id")?;
    publish_command_event(
        events,
        command,
        command.kind.event_kind(),
        vec![rebuild_id],
        command.payload.clone(),
        parent_span,
    )
    .await?;
    Ok(command_ack(command))
}

async fn handle_project_node_terms(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        if node.lang_version != so_lang::LANG_VERSION {
            return Ok(None);
        }
        let recorded_at = now();
        let report =
            crate::graph_generation::persist_term_projection_only(&node, &*graph, &recorded_at)?;
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "term-projection".to_string(),
                applied_at: recorded_at,
                value: json!({
                    "method": crate::graph_generation::TERM_DERIVATION_METHOD,
                    "version": crate::graph_generation::GENERATION_VERSION,
                    "terms_seen": report.terms_seen,
                    "terms_inserted": report.terms_inserted,
                    "mention_edges_inserted": report.mention_edges_inserted,
                }),
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, report)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, report)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "version": crate::graph_generation::GENERATION_VERSION,
                "terms_seen": report.terms_seen,
                "terms_inserted": report.terms_inserted,
                "mention_edges_inserted": report.mention_edges_inserted,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_project_node_contract(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        if node.lang_version != so_lang::LANG_VERSION {
            return Ok(None);
        }
        let recorded_at = now();
        let (report, contract_id) = crate::graph_generation::persist_contract_projection_only(
            &node,
            &*graph,
            &recorded_at,
        )?;
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "contract-projection".to_string(),
                applied_at: recorded_at,
                value: json!({
                    "method": crate::graph_generation::CONTRACT_PROJECTION_METHOD,
                    "version": crate::graph_generation::CONTRACT_PROJECTION_VERSION,
                    "nodes_inserted": report.contract_nodes_inserted,
                    "edges_inserted": report.contract_edges_inserted,
                    "contract_id": contract_id,
                }),
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, contract_id, report)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, contract_id, report)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "contract_id": contract_id,
                "version": crate::graph_generation::CONTRACT_PROJECTION_VERSION,
                "contract_nodes_inserted": report.contract_nodes_inserted,
                "contract_edges_inserted": report.contract_edges_inserted,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_semantic_relations(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        let recorded_at = now();
        let report =
            crate::graph_generation::persist_semantic_relations_only(&node, &*graph, &recorded_at)?;
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "semantic-relation".to_string(),
                applied_at: recorded_at,
                value: json!({
                    "candidate_method": crate::graph_generation::CANDIDATE_METHOD,
                    "candidate_version": crate::graph_generation::CANDIDATE_VERSION,
                    "assessment_method": crate::graph_generation::SEMANTIC_DERIVATION_METHOD,
                    "assessment_version": crate::graph_generation::SEMANTIC_DERIVATION_VERSION,
                    "edge_method": crate::graph_generation::SEMANTIC_EDGE_METHOD,
                    "edge_version": crate::graph_generation::semantic_edge_derivation().version,
                    "candidates_discovered": report.candidates_discovered,
                    "candidates_examined": report.candidates_examined,
                    "candidates_unassessable": report.candidates_unassessable,
                    "assessments_inserted": report.assessments_inserted,
                    "edges_inserted": report.semantic_edges_inserted,
                    "verdicts": report.verdicts,
                }),
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, report)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, report)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "candidates_discovered": report.candidates_discovered,
                "candidates_examined": report.candidates_examined,
                "candidates_unassessable": report.candidates_unassessable,
                "assessments_inserted": report.assessments_inserted,
                "semantic_edges_inserted": report.semantic_edges_inserted,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_contract_relations(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        let recorded_at = now();
        let report = crate::graph_generation::reconcile_contract_relations_only(
            &node,
            &*graph,
            &recorded_at,
        )?;
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "contract-relation".to_string(),
                applied_at: recorded_at,
                value: json!({
                    "method": crate::graph_generation::CONTRACT_RELATION_METHOD,
                    "version": crate::graph_generation::contract_relation_derivation().version,
                    "subject_has_contract": report.subject_has_contract,
                    "subject_unassessable": report.subject_unassessable,
                    "candidates_unassessable": report.candidates_unassessable,
                    "assessments_inserted": report.assessments_inserted,
                    "edges_inserted": report.semantic_edges_inserted,
                }),
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, report)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, report)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "subject_has_contract": report.subject_has_contract,
                "subject_unassessable": report.subject_unassessable,
                "candidates_unassessable": report.candidates_unassessable,
                "assessments_inserted": report.assessments_inserted,
                "semantic_edges_inserted": report.semantic_edges_inserted,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_discharge_candidates(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        let recorded_at = now();
        let report = crate::graph_generation::reconcile_discharge_candidates_only(
            &node,
            &*graph,
            &recorded_at,
        )?;
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "discharge-candidate".to_string(),
                applied_at: recorded_at,
                value: json!({
                    "method": crate::graph_generation::DISCHARGE_CANDIDATE_METHOD,
                    "version": crate::graph_generation::DISCHARGE_CANDIDATE_VERSION,
                    "subject_has_contract": report.subject_has_contract,
                    "subject_unassessable": report.subject_unassessable,
                    "candidates_unassessable": report.candidates_unassessable,
                    "assessments_inserted": report.assessments_inserted,
                }),
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, report)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, report)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "subject_has_contract": report.subject_has_contract,
                "subject_unassessable": report.subject_unassessable,
                "candidates_unassessable": report.candidates_unassessable,
                "assessments_inserted": report.assessments_inserted,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_capture_evidence(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        if !crate::evidence_capture::needs_capture(&node) {
            return Ok(None);
        }
        let recorded_at = now();
        let capture = crate::evidence_capture::capture(&node, &*graph, &*blobs, &recorded_at)
            .map_err(StoreError::Backend)?;
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: crate::evidence_capture::PLUGIN_NAME.to_string(),
                applied_at: recorded_at,
                value: capture.metadata.clone(),
            },
            capture.captured.then_some(capture.evidence.as_slice()),
        )?;
        Ok::<_, StoreError>(Some((node.id, capture.captured)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, true)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "capture_version": crate::evidence_capture::CAPTURE_VERSION,
                "provider": "evidence-capture",
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

async fn handle_github_evidence(
    command: &CommandEnvelope,
    graph: Arc<dyn GraphStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
    events: &EventBus,
    parent_span: tracing::Span,
) -> Result<CommandAck, ExecuteCommandError> {
    let node_id = processing_node_id(command)?;
    let command_id = command.id.clone();
    let written = tokio::task::spawn_blocking(move || {
        let Some(node) = graph.get_node(&node_id)? else {
            return Ok(None);
        };
        if !crate::github::needs_resolution(&node) {
            return Ok(None);
        }
        let recorded_at = now();
        let metadata = crate::github::resolve_node(&node, &*blobs, &recorded_at)
            .map_err(StoreError::Backend)?;
        let pinned_count = metadata
            .get("evidence")
            .and_then(Value::as_array)
            .map_or(0, Vec::len);
        graph.apply_command_update(
            &node.id,
            &command_id,
            &MetaUpdate {
                source: "github-evidence".to_string(),
                applied_at: recorded_at,
                value: metadata,
            },
            None,
        )?;
        Ok::<_, StoreError>(Some((node.id, pinned_count)))
    })
    .await
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?
    .map_err(|error| ExecuteCommandError::Processing(error.to_string()))?;

    let ack = command_ack(command);
    if let Some((node_id, pinned_count)) = written {
        publish_command_event(
            events,
            command,
            command.kind.event_kind(),
            vec![node_id],
            json!({
                "provider": "github-evidence",
                "pinned_count": pinned_count,
            }),
            parent_span,
        )
        .await?;
    }
    Ok(ack)
}

fn processing_node_id(command: &CommandEnvelope) -> Result<String, ExecuteCommandError> {
    processing_payload_string(command, "node_id")
}

fn processing_payload_string(
    command: &CommandEnvelope,
    field: &str,
) -> Result<String, ExecuteCommandError> {
    command
        .payload
        .get(field)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .map(str::to_string)
        .ok_or_else(|| {
            ExecuteCommandError::Processing(format!(
                "{:?} Command requires payload.{field}",
                command.kind,
            ))
        })
}

fn command_ack(command: &CommandEnvelope) -> CommandAck {
    CommandAck {
        command_id: command.id.clone(),
        acknowledged_at: now(),
    }
}

async fn publish_command_event(
    events: &EventBus,
    command: &CommandEnvelope,
    kind: EventKind,
    subject_ids: Vec<String>,
    payload: Value,
    parent_span: tracing::Span,
) -> Result<(), ExecuteCommandError> {
    events
        .publish(command_event_request(
            command,
            kind,
            subject_ids,
            payload,
            parent_span,
        ))
        .await?;
    Ok(())
}

fn command_event_request(
    command: &CommandEnvelope,
    kind: EventKind,
    subject_ids: Vec<String>,
    payload: Value,
    parent_span: tracing::Span,
) -> EventRequest {
    assert_eq!(
        kind,
        command.kind.event_kind(),
        "a Command Handler must publish its paired concrete Event kind"
    );
    let mut request = EventRequest::new(kind, &command.id)
        .with_payload(payload)
        .with_correlation(&command.correlation_id)
        .with_causation(&command.id)
        .with_parent(parent_span);
    request.subject_ids = subject_ids;
    request
}

fn now() -> String {
    chrono::Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Millis, true)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::event_bus::Subscription;
    use crate::event_sink::EventTap;
    use crate::store::{BlobStore, InMemoryNodeStore, NodeStore};

    #[test]
    fn every_command_kind_has_one_distinct_concrete_event_kind() {
        let commands = [
            CommandKind::AddNode,
            CommandKind::ReplaceEvidenceRequests,
            CommandKind::StartGraphRebuild,
            CommandKind::BeginNodeGraphRebuild,
            CommandKind::CompleteGraphRebuildPage,
            CommandKind::DeriveContract,
            CommandKind::EstablishOccurrenceReliance,
            CommandKind::EstablishGuaranteeDischarge,
            CommandKind::EstablishAdmissibilityEnvelope,
            CommandKind::AcceptDischargeCandidate,
            CommandKind::ProjectNodeTerms,
            CommandKind::ProjectNodeContract,
            CommandKind::CaptureEvidence,
            CommandKind::PinGithubEvidenceToCommit,
            CommandKind::AssessNodeSemanticRelations,
            CommandKind::AssessNodeContractRelations,
            CommandKind::AssessNodeDischargeCandidates,
        ];
        let events: std::collections::HashSet<_> = commands
            .iter()
            .copied()
            .map(CommandKind::event_kind)
            .collect();

        assert_eq!(commands.len(), 17);
        assert_eq!(events.len(), commands.len());
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

    fn input() -> AddNodeInput {
        AddNodeInput {
            specification: "The pump shall stop.".to_string(),
            evidence: vec![],
            now: "2026-07-18T00:00:00Z".to_string(),
            cli: "test".to_string(),
            cli_version: "test".to_string(),
        }
    }

    #[tokio::test]
    async fn command_ack_precedes_its_corresponding_event() {
        let store = Arc::new(InMemoryNodeStore::new());
        let (events, events_task) = EventBus::start(EventTap::default());
        events
            .register(Subscription::new("recorder", [EventKind::NodeAdded], 1))
            .await
            .unwrap();
        let (commands, commands_task) = CommandBus::start(store, Arc::new(NoBlobs), events.clone());
        let command = CommandEnvelope::new(CommandKind::AddNode, json!({}));
        let (ack, node) = commands
            .add_command(command.clone(), input())
            .await
            .unwrap();
        let delivery = events.receive("recorder").await.unwrap();
        events.ack(&delivery).await.unwrap();
        events.shutdown().await.unwrap();
        events_task.await.unwrap();
        commands.shutdown().await.unwrap();
        commands_task.await.unwrap();

        assert_eq!(delivery.event.command_id, ack.command_id);
        assert_eq!(delivery.event.subject_ids, [node.id]);
        let ack_time = chrono::DateTime::parse_from_rfc3339(&ack.acknowledged_at).unwrap();
        let event_time = chrono::DateTime::parse_from_rfc3339(&delivery.event.emitted_at).unwrap();
        assert!(event_time >= ack_time);
    }

    #[tokio::test]
    async fn processing_command_is_idempotent_by_command_id() {
        let store = Arc::new(InMemoryNodeStore::new());
        store
            .add_node(&Node {
                id: "n1".to_string(),
                statement: "The pump shall stop.".to_string(),
                lang_version: so_lang::LANG_VERSION.to_string(),
                meta: crate::domain::Meta {
                    evidence_requests: vec![],
                    evidence_request_generation: String::new(),
                    evidence: vec![],
                    created_at: "t".to_string(),
                    cli: "test".to_string(),
                    cli_version: "test".to_string(),
                    updates: Default::default(),
                },
            })
            .unwrap();
        let (events, events_task) = EventBus::start(EventTap::default());
        events
            .register(Subscription::new(
                "recorder",
                [EventKind::NodeTermsProjected],
                1,
            ))
            .await
            .unwrap();
        let (commands, commands_task) = CommandBus::start(store, Arc::new(NoBlobs), events.clone());
        let command = CommandEnvelope::new(CommandKind::ProjectNodeTerms, json!({"node_id": "n1"}));
        let first = commands.process(command.clone()).await.unwrap();
        let duplicate = commands.process(command).await.unwrap();
        assert_eq!(first, duplicate);
        let delivery = events.receive("recorder").await.unwrap();
        assert_eq!(delivery.event.command_id, first.command_id);
        events.ack(&delivery).await.unwrap();
        events.shutdown().await.unwrap();
        events_task.await.unwrap();
        commands.shutdown().await.unwrap();
        commands_task.await.unwrap();
    }
}
