//! Independently running Event Consumers.
//!
//! A Consumer polls the volatile Event Bus, submits a deterministic Command,
//! waits until that Command has completed, and explicitly acknowledges or
//! rejects the Delivery. The Event Bus does not construct or invoke anything
//! in this module. Built-in graph and Evidence processors use
//! [`ConsumerDefinition`]; a Plugin may use the same adapter or run its own
//! receive loop directly against the Event Bus.

use serde_json::json;
use std::sync::Arc;

use crate::command_bus::{CommandBus, CommandEnvelope, CommandKind};
use crate::event_bus::{EventBus, EventBusError, EventKind, Subscription};
use crate::store::GraphStore;

const GRAPH_REBUILD_CONSUMER: &str = "graph-rebuild";
const GRAPH_REBUILD_PAGE_SIZE: usize = 100;

#[derive(Clone)]
pub struct ConsumerDefinition {
    pub consumer_id: &'static str,
    pub event_kinds: &'static [EventKind],
    pub workers: usize,
    pub command_kind: CommandKind,
    pub operation: &'static str,
}

impl ConsumerDefinition {
    pub const fn new(
        consumer_id: &'static str,
        event_kinds: &'static [EventKind],
        workers: usize,
        command_kind: CommandKind,
        operation: &'static str,
    ) -> ConsumerDefinition {
        ConsumerDefinition {
            consumer_id,
            event_kinds,
            workers,
            command_kind,
            operation,
        }
    }
}

const NODE_EVENTS: &[EventKind] = &[EventKind::NodeAdded, EventKind::NodeGraphRebuildStarted];
const EVIDENCE_EVENTS: &[EventKind] = &[EventKind::NodeAdded, EventKind::EvidenceRequestsReplaced];
const TERM_EVENTS: &[EventKind] = &[EventKind::NodeTermsProjected];
const CONTRACT_EVENTS: &[EventKind] = &[
    EventKind::NodeContractProjected,
    EventKind::OccurrenceRelianceEstablished,
    EventKind::GuaranteeDischargeEstablished,
    EventKind::AdmissibilityEnvelopeEstablished,
    EventKind::DischargeCandidateAccepted,
];
const DISCHARGE_EVENTS: &[EventKind] = &[
    EventKind::NodeContractProjected,
    EventKind::OccurrenceRelianceEstablished,
    EventKind::GuaranteeDischargeEstablished,
    EventKind::AdmissibilityEnvelopeEstablished,
    EventKind::DischargeCandidateAccepted,
    EventKind::NodeSemanticRelationAssessmentCompleted,
    EventKind::NodeContractRelationAssessmentCompleted,
];

pub fn built_in_consumers() -> Vec<ConsumerDefinition> {
    vec![
        ConsumerDefinition::new(
            "term-projection",
            NODE_EVENTS,
            1,
            CommandKind::ProjectNodeTerms,
            "project-node-terms",
        ),
        ConsumerDefinition::new(
            "contract-projection",
            NODE_EVENTS,
            1,
            CommandKind::ProjectNodeContract,
            "project-node-contract",
        ),
        ConsumerDefinition::new(
            crate::evidence_capture::PLUGIN_NAME,
            EVIDENCE_EVENTS,
            4,
            CommandKind::CaptureEvidence,
            "capture-evidence",
        ),
        ConsumerDefinition::new(
            "github-evidence",
            EVIDENCE_EVENTS,
            4,
            CommandKind::PinGithubEvidenceToCommit,
            "pin-github-evidence-to-commit",
        ),
        ConsumerDefinition::new(
            "semantic-relation",
            TERM_EVENTS,
            1,
            CommandKind::AssessNodeSemanticRelations,
            "assess-node-semantic-relations",
        ),
        ConsumerDefinition::new(
            "contract-relation",
            CONTRACT_EVENTS,
            1,
            CommandKind::AssessNodeContractRelations,
            "assess-node-contract-relations",
        ),
        ConsumerDefinition::new(
            "discharge-candidate",
            DISCHARGE_EVENTS,
            1,
            CommandKind::AssessNodeDischargeCandidates,
            "assess-node-discharge-candidates",
        ),
    ]
}

pub struct ConsumerRuntime {
    tasks: Vec<tokio::task::JoinHandle<()>>,
}

impl ConsumerRuntime {
    pub async fn start(
        events: EventBus,
        commands: CommandBus,
        graph: Arc<dyn GraphStore + Send + Sync>,
        definitions: Vec<ConsumerDefinition>,
    ) -> Result<ConsumerRuntime, EventBusError> {
        let mut tasks = Vec::new();
        events
            .register(Subscription::new(
                GRAPH_REBUILD_CONSUMER,
                [
                    EventKind::GraphRebuildStarted,
                    EventKind::GraphRebuildPageCompleted,
                ],
                1,
            ))
            .await?;
        {
            let events = events.clone();
            let commands = commands.clone();
            tasks.push(tokio::spawn(async move {
                run_graph_rebuild_consumer(events, commands, graph).await;
            }));
        }
        for definition in definitions {
            let workers = definition.workers.max(1);
            events
                .register(Subscription::new(
                    definition.consumer_id,
                    definition.event_kinds.iter().copied(),
                    workers,
                ))
                .await?;
            for _ in 0..workers {
                let events = events.clone();
                let commands = commands.clone();
                let definition = definition.clone();
                tasks.push(tokio::spawn(async move {
                    run_consumer(definition, events, commands).await;
                }));
            }
        }
        Ok(ConsumerRuntime { tasks })
    }

    pub async fn join(self) {
        for task in self.tasks {
            if let Err(error) = task.await {
                tracing::error!(
                    "error.message" = %error,
                    "Consumer task terminated unexpectedly"
                );
            }
        }
    }
}

async fn run_graph_rebuild_consumer(
    events: EventBus,
    commands: CommandBus,
    graph: Arc<dyn GraphStore + Send + Sync>,
) {
    loop {
        let delivery = match events.receive(GRAPH_REBUILD_CONSUMER).await {
            Ok(delivery) => delivery,
            Err(EventBusError::Closed | EventBusError::ReplyDropped) => break,
            Err(error) => {
                tracing::error!(
                    "consumer.id" = GRAPH_REBUILD_CONSUMER,
                    "error.message" = %error,
                    "Graph rebuild Consumer could not receive a Delivery"
                );
                break;
            }
        };

        match process_graph_rebuild_page(&delivery.event, &commands, graph.clone()).await {
            Ok(()) => {
                if let Err(error) = events.ack(&delivery).await {
                    tracing::warn!(
                        "consumer.id" = GRAPH_REBUILD_CONSUMER,
                        "delivery.id" = %delivery.id,
                        "error.message" = %error,
                        "Graph rebuild Consumer could not acknowledge a completed Delivery"
                    );
                }
            }
            Err(message) => {
                if let Err(error) = events.nack(&delivery, &message).await {
                    tracing::warn!(
                        "consumer.id" = GRAPH_REBUILD_CONSUMER,
                        "delivery.id" = %delivery.id,
                        "error.message" = %error,
                        "Graph rebuild Consumer could not reject a failed Delivery"
                    );
                }
            }
        }
    }
}

async fn process_graph_rebuild_page(
    event: &crate::event_bus::EventEnvelope,
    commands: &CommandBus,
    graph: Arc<dyn GraphStore + Send + Sync>,
) -> Result<(), String> {
    let rebuild_id = event
        .payload
        .get("rebuild_id")
        .and_then(serde_json::Value::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| format!("{:?} Event requires payload.rebuild_id", event.kind))?
        .to_string();
    let total_nodes = event
        .payload
        .get("total_nodes")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let processed_nodes = event
        .payload
        .get("processed_nodes")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let after = match event.kind {
        EventKind::GraphRebuildStarted => None,
        EventKind::GraphRebuildPageCompleted => {
            let Some(next) = event.payload.get("next_after") else {
                return Err("GraphRebuildPageCompleted Event requires payload.next_after".into());
            };
            if next.is_null() {
                return Ok(());
            }
            Some(
                next.as_str()
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| {
                        "GraphRebuildPageCompleted payload.next_after must be a cursor or null"
                            .to_string()
                    })?
                    .to_string(),
            )
        }
        kind => return Err(format!("Graph rebuild Consumer cannot process {kind:?}")),
    };

    let page = tokio::task::spawn_blocking(move || {
        graph.list_nodes(after.as_deref(), GRAPH_REBUILD_PAGE_SIZE)
    })
    .await
    .map_err(|error| format!("graph rebuild page task failed: {error}"))?
    .map_err(|error| error.to_string())?;
    let page_nodes = page.nodes.len() as u64;

    for node in page.nodes {
        let command = CommandEnvelope::caused_by_consumer_with_key(
            GRAPH_REBUILD_CONSUMER,
            event,
            "begin-node-graph-rebuild",
            &node.id,
            CommandKind::BeginNodeGraphRebuild,
            json!({
                "rebuild_id": rebuild_id.clone(),
                "node_id": node.id,
            }),
        );
        commands
            .process(command)
            .await
            .map_err(|error| error.to_string())?;
    }

    let completed = CommandEnvelope::caused_by_consumer(
        GRAPH_REBUILD_CONSUMER,
        event,
        "complete-graph-rebuild-page",
        CommandKind::CompleteGraphRebuildPage,
        json!({
            "rebuild_id": rebuild_id,
            "page_nodes": page_nodes,
            "processed_nodes": processed_nodes.saturating_add(page_nodes),
            "total_nodes": total_nodes,
            "next_after": page.next_cursor,
        }),
    );
    commands
        .process(completed)
        .await
        .map_err(|error| error.to_string())?;
    Ok(())
}

async fn run_consumer(definition: ConsumerDefinition, events: EventBus, commands: CommandBus) {
    loop {
        let delivery = match events.receive(definition.consumer_id).await {
            Ok(delivery) => delivery,
            Err(EventBusError::Closed | EventBusError::ReplyDropped) => break,
            Err(error) => {
                tracing::error!(
                    "consumer.id" = definition.consumer_id,
                    "error.message" = %error,
                    "Consumer could not receive a Delivery"
                );
                break;
            }
        };
        let Some(node_id) = delivery.event.subject_ids.first().cloned() else {
            let _ = events.ack(&delivery).await;
            continue;
        };
        let command = CommandEnvelope::caused_by_consumer(
            definition.consumer_id,
            &delivery.event,
            definition.operation,
            definition.command_kind,
            json!({
                "node_id": node_id,
                "source_event_id": delivery.event.id,
            }),
        );
        match commands.process(command).await {
            Ok(_) => {
                if let Err(error) = events.ack(&delivery).await {
                    tracing::warn!(
                        "consumer.id" = definition.consumer_id,
                        "delivery.id" = %delivery.id,
                        "error.message" = %error,
                        "Consumer could not acknowledge a completed Delivery"
                    );
                }
            }
            Err(error) => {
                let message = error.to_string();
                if let Err(nack_error) = events.nack(&delivery, &message).await {
                    tracing::warn!(
                        "consumer.id" = definition.consumer_id,
                        "delivery.id" = %delivery.id,
                        "error.message" = %nack_error,
                        "Consumer could not reject a failed Delivery"
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::time::Duration;

    use super::*;
    use crate::domain::{Meta, Node};
    use crate::event_bus::{EventRequest, Subscription};
    use crate::event_sink::EventTap;
    use crate::store::{BlobStore, GraphStore, InMemoryNodeStore, NodeStore, StoreError};

    struct NoBlobs;

    impl BlobStore for NoBlobs {
        fn put_blob(&self, _hash: &str, _bytes: &[u8]) -> Result<(), StoreError> {
            Ok(())
        }

        fn get_blob(&self, _hash: &str) -> Result<Option<Vec<u8>>, StoreError> {
            Ok(None)
        }
    }

    #[test]
    fn built_in_processors_are_plain_consumer_definitions() {
        let definitions = built_in_consumers();
        assert_eq!(definitions.len(), 7);
        assert!(definitions
            .iter()
            .any(|definition| definition.consumer_id == "evidence-capture"));
        assert!(definitions
            .iter()
            .any(|definition| definition.consumer_id == "term-projection"));
    }

    #[tokio::test]
    async fn consumer_submits_a_command_then_acknowledges_its_delivery() {
        const INPUT_EVENTS: &[EventKind] = &[EventKind::NodeAdded];

        let store = Arc::new(InMemoryNodeStore::new());
        store
            .add_node(&Node {
                id: "n1".to_string(),
                statement: "The pump shall stop.".to_string(),
                lang_version: so_lang::LANG_VERSION.to_string(),
                meta: Meta {
                    evidence_requests: vec![],
                    evidence_request_generation: String::new(),
                    evidence: vec![],
                    created_at: "2026-07-18T00:00:00Z".to_string(),
                    cli: "test".to_string(),
                    cli_version: "test".to_string(),
                    updates: Default::default(),
                },
            })
            .unwrap();

        let (events, event_task) = EventBus::start(EventTap::default());
        let graph: Arc<dyn GraphStore + Send + Sync> = store.clone();
        let blobs: Arc<dyn BlobStore + Send + Sync> = Arc::new(NoBlobs);
        let (commands, command_task) = CommandBus::start(graph.clone(), blobs, events.clone());
        let consumers = ConsumerRuntime::start(
            events.clone(),
            commands.clone(),
            graph,
            vec![ConsumerDefinition::new(
                "term-projection-test",
                INPUT_EVENTS,
                1,
                CommandKind::ProjectNodeTerms,
                "project-node-terms",
            )],
        )
        .await
        .unwrap();
        events
            .register(Subscription::new(
                "projection-recorder",
                [EventKind::NodeTermsProjected],
                1,
            ))
            .await
            .unwrap();

        let source = events
            .publish(EventRequest::new(EventKind::NodeAdded, "add-node-command").with_subject("n1"))
            .await
            .unwrap();
        let projected = tokio::time::timeout(
            Duration::from_secs(2),
            events.receive("projection-recorder"),
        )
        .await
        .expect("projection Consumer completed its Command")
        .unwrap();

        assert_eq!(projected.event.kind, EventKind::NodeTermsProjected);
        assert_eq!(projected.event.correlation_id, source.correlation_id);
        assert_eq!(
            projected.event.causation_id.as_deref(),
            Some(projected.event.command_id.as_str())
        );
        let expected_command_id = crate::identity::derive_id(
            "consumer-command",
            &["term-projection-test", &source.id, "project-node-terms"],
        );
        assert_eq!(projected.event.command_id, expected_command_id);

        tokio::time::timeout(Duration::from_secs(2), async {
            loop {
                if events.snapshot().await.unwrap().pending_deliveries == 1 {
                    break;
                }
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("source Delivery was explicitly acknowledged");
        assert_eq!(
            store
                .get_node("n1")
                .unwrap()
                .unwrap()
                .meta
                .updates
                .get(&expected_command_id)
                .map(|update| update.source.as_str()),
            Some("term-projection")
        );

        events.ack(&projected).await.unwrap();
        tokio::time::timeout(Duration::from_secs(5), events.shutdown())
            .await
            .expect("Event Bus drained after the rebuild")
            .unwrap();
        tokio::time::timeout(Duration::from_secs(5), event_task)
            .await
            .expect("Event Bus task stopped")
            .unwrap();
        tokio::time::timeout(Duration::from_secs(5), consumers.join())
            .await
            .expect("rebuild Consumers stopped");
        tokio::time::timeout(Duration::from_secs(5), commands.shutdown())
            .await
            .expect("Command Bus accepted shutdown")
            .unwrap();
        tokio::time::timeout(Duration::from_secs(5), command_task)
            .await
            .expect("Command Bus task stopped")
            .unwrap();
    }

    #[tokio::test]
    async fn graph_rebuild_reenters_existing_nodes_through_graph_consumers() {
        let store = Arc::new(InMemoryNodeStore::new());
        store
            .add_node(&Node {
                id: "existing".to_string(),
                statement: "The pump shall stop.".to_string(),
                lang_version: so_lang::LANG_VERSION.to_string(),
                meta: Meta {
                    evidence_requests: vec![],
                    evidence_request_generation: String::new(),
                    evidence: vec![],
                    created_at: "2026-07-18T00:00:00Z".to_string(),
                    cli: "test".to_string(),
                    cli_version: "test".to_string(),
                    updates: Default::default(),
                },
            })
            .unwrap();

        let (events, event_task) = EventBus::start(EventTap::default());
        let graph: Arc<dyn GraphStore + Send + Sync> = store.clone();
        let blobs: Arc<dyn BlobStore + Send + Sync> = Arc::new(NoBlobs);
        let (commands, command_task) = CommandBus::start(graph.clone(), blobs, events.clone());
        let consumers = ConsumerRuntime::start(
            events.clone(),
            commands.clone(),
            graph,
            built_in_consumers(),
        )
        .await
        .unwrap();

        let (_, total_nodes) = commands
            .start_graph_rebuild(crate::command_bus::StartGraphRebuildInput {
                client: "test".to_string(),
                client_version: "test".to_string(),
            })
            .await
            .unwrap();
        assert_eq!(total_nodes, 1);

        tokio::time::timeout(Duration::from_secs(5), async {
            loop {
                let edges = store
                    .list_edges(
                        &["existing".to_string()],
                        &crate::graph_generation::current_derivations(),
                    )
                    .unwrap();
                let current = store.get_node("existing").unwrap().unwrap();
                if !edges.is_empty()
                    && current
                        .meta
                        .updates
                        .values()
                        .any(|update| update.source == "graph-rebuild")
                {
                    break;
                }
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("existing Node entered the rebuild and acquired derived Edges");

        events.shutdown().await.unwrap();
        event_task.await.unwrap();
        consumers.join().await;
        commands.shutdown().await.unwrap();
        command_task.await.unwrap();
    }
}
