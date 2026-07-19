//! Volatile in-process Event delivery.
//!
//! This module is a broker, not a task runner. It stores accepted Events for
//! the lifetime of the daemon, leases Deliveries to independently running
//! Consumers, accepts explicit Ack/Nack messages, and redelivers unacknowledged
//! Deliveries. It never starts a Consumer, calls Plugin code, reads or writes
//! the Ledger, submits Commands, or interprets processing results.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use thiserror::Error;
use tokio::sync::{mpsc, oneshot, OwnedSemaphorePermit, Semaphore};

use crate::event_sink::EventTap;
use crate::identity::{derive_id, new_message_id};

const BUS_MAILBOX_CAPACITY: usize = 1024;
const EVENT_RETENTION_CAPACITY: usize = 4096;
const RETRY_MAX_SECONDS: u64 = 60;
const DEFAULT_LEASE: Duration = Duration::from_secs(300);

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "PascalCase")]
pub enum EventKind {
    NodeAdded,
    EvidenceRequestsReplaced,
    GraphRebuildStarted,
    NodeGraphRebuildStarted,
    GraphRebuildPageCompleted,
    ContractDerived,
    OccurrenceRelianceEstablished,
    GuaranteeDischargeEstablished,
    AdmissibilityEnvelopeEstablished,
    DischargeCandidateAccepted,
    NodeTermsProjected,
    NodeContractProjected,
    EvidenceCaptured,
    GithubEvidencePinnedToCommit,
    NodeSemanticRelationAssessmentCompleted,
    NodeContractRelationAssessmentCompleted,
    NodeDischargeCandidateAssessmentCompleted,
}

/// Abstract Event categories used only for subscription matching.
///
/// An emitted fact always retains exactly one concrete [`EventKind`]. A
/// category match therefore never replaces, wraps, or republishes the concrete
/// Event. Kinds may belong to more than one category.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "PascalCase")]
pub enum EventClass {
    DomainEvent,
    GraphEvent,
    NodeEvent,
    EvidenceEvent,
    ContractEvent,
    RelationEvent,
    ProjectionEvent,
    AssessmentEvent,
}

impl EventKind {
    pub fn is_a(self, class: EventClass) -> bool {
        match class {
            EventClass::DomainEvent => true,
            EventClass::GraphEvent => matches!(
                self,
                EventKind::GraphRebuildStarted
                    | EventKind::NodeGraphRebuildStarted
                    | EventKind::GraphRebuildPageCompleted
            ),
            EventClass::NodeEvent => matches!(
                self,
                EventKind::NodeAdded
                    | EventKind::EvidenceRequestsReplaced
                    | EventKind::NodeGraphRebuildStarted
                    | EventKind::NodeTermsProjected
                    | EventKind::NodeContractProjected
                    | EventKind::EvidenceCaptured
                    | EventKind::GithubEvidencePinnedToCommit
                    | EventKind::NodeSemanticRelationAssessmentCompleted
                    | EventKind::NodeContractRelationAssessmentCompleted
                    | EventKind::NodeDischargeCandidateAssessmentCompleted
            ),
            EventClass::EvidenceEvent => matches!(
                self,
                EventKind::EvidenceRequestsReplaced
                    | EventKind::EvidenceCaptured
                    | EventKind::GithubEvidencePinnedToCommit
            ),
            EventClass::ContractEvent => matches!(
                self,
                EventKind::ContractDerived
                    | EventKind::OccurrenceRelianceEstablished
                    | EventKind::GuaranteeDischargeEstablished
                    | EventKind::AdmissibilityEnvelopeEstablished
                    | EventKind::DischargeCandidateAccepted
                    | EventKind::NodeContractProjected
                    | EventKind::NodeContractRelationAssessmentCompleted
                    | EventKind::NodeDischargeCandidateAssessmentCompleted
            ),
            EventClass::RelationEvent => matches!(
                self,
                EventKind::OccurrenceRelianceEstablished
                    | EventKind::GuaranteeDischargeEstablished
                    | EventKind::AdmissibilityEnvelopeEstablished
                    | EventKind::DischargeCandidateAccepted
                    | EventKind::NodeSemanticRelationAssessmentCompleted
                    | EventKind::NodeContractRelationAssessmentCompleted
                    | EventKind::NodeDischargeCandidateAssessmentCompleted
            ),
            EventClass::ProjectionEvent => matches!(
                self,
                EventKind::NodeTermsProjected | EventKind::NodeContractProjected
            ),
            EventClass::AssessmentEvent => matches!(
                self,
                EventKind::NodeSemanticRelationAssessmentCompleted
                    | EventKind::NodeContractRelationAssessmentCompleted
                    | EventKind::NodeDischargeCandidateAssessmentCompleted
            ),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct EventEnvelope {
    pub id: String,
    pub stream_instance_id: String,
    pub sequence: u64,
    pub kind: EventKind,
    pub schema_version: u32,
    pub emitted_at: String,
    pub command_id: String,
    pub correlation_id: String,
    pub causation_id: Option<String>,
    pub subject_ids: Vec<String>,
    pub payload: Value,
    #[serde(skip)]
    pub parent_span: Option<tracing::Span>,
}

#[derive(Clone, Debug)]
pub struct EventRequest {
    pub kind: EventKind,
    pub schema_version: u32,
    pub command_id: String,
    pub correlation_id: String,
    pub causation_id: Option<String>,
    pub subject_ids: Vec<String>,
    pub payload: Value,
    pub parent_span: Option<tracing::Span>,
}

impl EventRequest {
    pub fn new(kind: EventKind, command_id: impl Into<String>) -> EventRequest {
        let command_id = command_id.into();
        EventRequest {
            kind,
            schema_version: 1,
            correlation_id: command_id.clone(),
            command_id,
            causation_id: None,
            subject_ids: Vec::new(),
            payload: Value::Null,
            parent_span: Some(tracing::Span::current()),
        }
    }

    pub fn with_subject(mut self, subject_id: impl Into<String>) -> EventRequest {
        self.subject_ids.push(subject_id.into());
        self
    }

    pub fn with_payload(mut self, payload: Value) -> EventRequest {
        self.payload = payload;
        self
    }

    pub fn with_correlation(mut self, correlation_id: impl Into<String>) -> EventRequest {
        self.correlation_id = correlation_id.into();
        self
    }

    pub fn with_causation(mut self, causation_id: impl Into<String>) -> EventRequest {
        self.causation_id = Some(causation_id.into());
        self
    }

    pub fn with_parent(mut self, parent_span: tracing::Span) -> EventRequest {
        self.parent_span = Some(parent_span);
        self
    }
}

/// The Event kinds and lease policy for one logical Consumer.
///
/// Worker construction belongs to the daemon runtime. The Event Bus knows only
/// this delivery contract.
#[derive(Clone, Debug)]
pub struct Subscription {
    pub consumer_id: String,
    pub event_kinds: HashSet<EventKind>,
    pub event_classes: HashSet<EventClass>,
    pub max_in_flight: usize,
    pub lease_duration: Duration,
}

impl Subscription {
    pub fn new(
        consumer_id: impl Into<String>,
        event_kinds: impl IntoIterator<Item = EventKind>,
        max_in_flight: usize,
    ) -> Subscription {
        Subscription {
            consumer_id: consumer_id.into(),
            event_kinds: event_kinds.into_iter().collect(),
            event_classes: HashSet::new(),
            max_in_flight: max_in_flight.max(1),
            lease_duration: DEFAULT_LEASE,
        }
    }

    pub fn for_classes(
        consumer_id: impl Into<String>,
        event_classes: impl IntoIterator<Item = EventClass>,
        max_in_flight: usize,
    ) -> Subscription {
        Subscription {
            consumer_id: consumer_id.into(),
            event_kinds: HashSet::new(),
            event_classes: event_classes.into_iter().collect(),
            max_in_flight: max_in_flight.max(1),
            lease_duration: DEFAULT_LEASE,
        }
    }

    pub fn with_event_class(mut self, event_class: EventClass) -> Subscription {
        self.event_classes.insert(event_class);
        self
    }

    pub fn with_lease(mut self, lease_duration: Duration) -> Subscription {
        assert!(!lease_duration.is_zero(), "Delivery lease must be positive");
        self.lease_duration = lease_duration;
        self
    }

    fn matches(&self, kind: EventKind) -> bool {
        self.event_kinds.contains(&kind)
            || self
                .event_classes
                .iter()
                .any(|event_class| kind.is_a(*event_class))
    }
}

#[derive(Clone, Debug)]
pub struct EventDelivery {
    pub id: String,
    pub event: EventEnvelope,
    pub consumer_id: String,
    pub attempt: u32,
    pub lease_deadline: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EventBusSnapshot {
    pub stream_instance_id: String,
    pub last_sequence: u64,
    pub retained_events: usize,
    pub pending_deliveries: usize,
    pub consumer_count: usize,
}

#[derive(Clone)]
pub struct EventBus {
    sender: mpsc::Sender<Message>,
    retention: Arc<Semaphore>,
}

#[derive(Debug, Error)]
pub enum EventBusError {
    #[error("Event Bus is closed")]
    Closed,
    #[error("Event Bus stopped before replying")]
    ReplyDropped,
    #[error("Event Bus stopped before shutdown completed")]
    ShutdownDropped,
    #[error("Consumer `{0}` is already registered")]
    DuplicateConsumer(String),
    #[error("Consumer `{0}` is not registered")]
    UnknownConsumer(String),
}

enum Message {
    Publish {
        request: EventRequest,
        permit: OwnedSemaphorePermit,
        reply: oneshot::Sender<Result<EventEnvelope, EventBusError>>,
    },
    Register {
        subscription: Subscription,
        reply: oneshot::Sender<Result<(), EventBusError>>,
    },
    Receive {
        consumer_id: String,
        reply: oneshot::Sender<Result<EventDelivery, EventBusError>>,
    },
    Ack {
        consumer_id: String,
        delivery_id: String,
        attempt: u32,
        reply: oneshot::Sender<Result<(), EventBusError>>,
    },
    Nack {
        consumer_id: String,
        delivery_id: String,
        attempt: u32,
        reason: String,
        reply: oneshot::Sender<Result<(), EventBusError>>,
    },
    LeaseExpired {
        delivery_id: String,
        attempt: u32,
    },
    RedeliveryReady {
        delivery_id: String,
    },
    Snapshot {
        reply: oneshot::Sender<EventBusSnapshot>,
    },
    Shutdown {
        reply: oneshot::Sender<()>,
    },
}

struct RetainedEvent {
    envelope: EventEnvelope,
    awaiting: HashSet<String>,
    _permit: OwnedSemaphorePermit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeliveryState {
    Pending,
    InFlight,
    WaitingToRetry,
}

struct DeliveryRecord {
    id: String,
    event_id: String,
    consumer_id: String,
    attempt: u32,
    state: DeliveryState,
}

struct ConsumerState {
    subscription: Subscription,
    pending: VecDeque<String>,
    receivers: VecDeque<oneshot::Sender<Result<EventDelivery, EventBusError>>>,
    in_flight: usize,
    retry_blocks_order: bool,
}

impl EventBus {
    pub fn start(tap: EventTap) -> (EventBus, tokio::task::JoinHandle<()>) {
        let (sender, receiver) = mpsc::channel(BUS_MAILBOX_CAPACITY);
        let retention = Arc::new(Semaphore::new(EVENT_RETENTION_CAPACITY));
        let bus = EventBus {
            sender: sender.clone(),
            retention,
        };
        let task = tokio::spawn(run(receiver, sender, tap, new_message_id()));
        (bus, task)
    }

    /// Accept a fresh Event. Waiting for a retention permit is producer
    /// backpressure; accepted unacked Events are never force-expired.
    pub async fn publish(&self, request: EventRequest) -> Result<EventEnvelope, EventBusError> {
        let permit = self
            .retention
            .clone()
            .acquire_owned()
            .await
            .map_err(|_| EventBusError::Closed)?;
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Publish {
                request,
                permit,
                reply,
            })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ReplyDropped)?
    }

    /// Register delivery state for future Events only.
    pub async fn register(&self, subscription: Subscription) -> Result<(), EventBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Register {
                subscription,
                reply,
            })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ReplyDropped)?
    }

    /// Wait until the next Delivery for this Consumer can be leased.
    pub async fn receive(&self, consumer_id: &str) -> Result<EventDelivery, EventBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Receive {
                consumer_id: consumer_id.to_string(),
                reply,
            })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ReplyDropped)?
    }

    /// Explicitly acknowledge one leased Delivery attempt.
    pub async fn ack(&self, delivery: &EventDelivery) -> Result<(), EventBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Ack {
                consumer_id: delivery.consumer_id.clone(),
                delivery_id: delivery.id.clone(),
                attempt: delivery.attempt,
                reply,
            })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ReplyDropped)?
    }

    /// Explicitly reject one leased attempt. The same Delivery ID becomes
    /// available again after retry backoff.
    pub async fn nack(
        &self,
        delivery: &EventDelivery,
        reason: impl Into<String>,
    ) -> Result<(), EventBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Nack {
                consumer_id: delivery.consumer_id.clone(),
                delivery_id: delivery.id.clone(),
                attempt: delivery.attempt,
                reason: reason.into(),
                reply,
            })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ReplyDropped)?
    }

    pub async fn snapshot(&self) -> Result<EventBusSnapshot, EventBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Snapshot { reply })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ReplyDropped)
    }

    /// Stop accepting new Events and finish once all retained Deliveries have
    /// been acknowledged.
    pub async fn shutdown(&self) -> Result<(), EventBusError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Shutdown { reply })
            .await
            .map_err(|_| EventBusError::Closed)?;
        received.await.map_err(|_| EventBusError::ShutdownDropped)
    }
}

async fn run(
    mut receiver: mpsc::Receiver<Message>,
    sender: mpsc::Sender<Message>,
    tap: EventTap,
    stream_instance_id: String,
) {
    let mut consumers: HashMap<String, ConsumerState> = HashMap::new();
    let mut events: HashMap<String, RetainedEvent> = HashMap::new();
    let mut deliveries: HashMap<String, DeliveryRecord> = HashMap::new();
    let mut sequence = 0_u64;
    let mut shutdown_reply: Option<oneshot::Sender<()>> = None;

    while let Some(message) = receiver.recv().await {
        match message {
            Message::Publish {
                request,
                permit,
                reply,
            } => {
                sequence = sequence.saturating_add(1);
                let event = envelope(&stream_instance_id, sequence, request);
                tap.record(&event);
                let subscribed: Vec<String> = consumers
                    .iter()
                    .filter(|(_, state)| state.subscription.matches(event.kind))
                    .map(|(consumer_id, _)| consumer_id.clone())
                    .collect();
                if !subscribed.is_empty() {
                    let event_id = event.id.clone();
                    events.insert(
                        event_id.clone(),
                        RetainedEvent {
                            envelope: event.clone(),
                            awaiting: subscribed.iter().cloned().collect(),
                            _permit: permit,
                        },
                    );
                    for consumer_id in &subscribed {
                        let delivery_id = derive_id("event-delivery", &[&event_id, consumer_id]);
                        deliveries.insert(
                            delivery_id.clone(),
                            DeliveryRecord {
                                id: delivery_id.clone(),
                                event_id: event_id.clone(),
                                consumer_id: consumer_id.clone(),
                                attempt: 0,
                                state: DeliveryState::Pending,
                            },
                        );
                        if let Some(state) = consumers.get_mut(consumer_id) {
                            state.pending.push_back(delivery_id);
                        }
                    }
                    for consumer_id in subscribed {
                        lease_available(
                            &consumer_id,
                            &mut consumers,
                            &events,
                            &mut deliveries,
                            &sender,
                        );
                    }
                }
                let _ = reply.send(Ok(event));
            }
            Message::Register {
                subscription,
                reply,
            } => {
                if consumers.contains_key(&subscription.consumer_id) {
                    let _ = reply.send(Err(EventBusError::DuplicateConsumer(
                        subscription.consumer_id,
                    )));
                } else if shutdown_reply.is_some() {
                    let _ = reply.send(Err(EventBusError::Closed));
                } else {
                    consumers.insert(
                        subscription.consumer_id.clone(),
                        ConsumerState {
                            subscription,
                            pending: VecDeque::new(),
                            receivers: VecDeque::new(),
                            in_flight: 0,
                            retry_blocks_order: false,
                        },
                    );
                    let _ = reply.send(Ok(()));
                }
            }
            Message::Receive { consumer_id, reply } => {
                let Some(state) = consumers.get_mut(&consumer_id) else {
                    let _ = reply.send(Err(EventBusError::UnknownConsumer(consumer_id)));
                    continue;
                };
                if shutdown_reply.is_some() && !has_delivery_for(&consumer_id, &deliveries) {
                    let _ = reply.send(Err(EventBusError::Closed));
                    continue;
                }
                state.receivers.push_back(reply);
                lease_available(
                    &consumer_id,
                    &mut consumers,
                    &events,
                    &mut deliveries,
                    &sender,
                );
            }
            Message::Ack {
                consumer_id,
                delivery_id,
                attempt,
                reply,
            } => {
                acknowledge(
                    &consumer_id,
                    &delivery_id,
                    attempt,
                    &mut consumers,
                    &mut events,
                    &mut deliveries,
                    &sender,
                );
                let _ = reply.send(Ok(()));
            }
            Message::Nack {
                consumer_id,
                delivery_id,
                attempt,
                reason,
                reply,
            } => {
                reject(
                    &consumer_id,
                    &delivery_id,
                    attempt,
                    &reason,
                    &mut consumers,
                    &mut deliveries,
                    &sender,
                );
                let _ = reply.send(Ok(()));
            }
            Message::LeaseExpired {
                delivery_id,
                attempt,
            } => {
                let Some(record) = deliveries.get(&delivery_id) else {
                    continue;
                };
                let consumer_id = record.consumer_id.clone();
                reject(
                    &consumer_id,
                    &delivery_id,
                    attempt,
                    "Delivery lease expired",
                    &mut consumers,
                    &mut deliveries,
                    &sender,
                );
            }
            Message::RedeliveryReady { delivery_id } => {
                let Some(record) = deliveries.get_mut(&delivery_id) else {
                    continue;
                };
                if record.state != DeliveryState::WaitingToRetry {
                    continue;
                }
                record.state = DeliveryState::Pending;
                let consumer_id = record.consumer_id.clone();
                if let Some(state) = consumers.get_mut(&consumer_id) {
                    state.retry_blocks_order = false;
                    state.pending.push_front(delivery_id);
                }
                lease_available(
                    &consumer_id,
                    &mut consumers,
                    &events,
                    &mut deliveries,
                    &sender,
                );
            }
            Message::Snapshot { reply } => {
                let _ = reply.send(EventBusSnapshot {
                    stream_instance_id: stream_instance_id.clone(),
                    last_sequence: sequence,
                    retained_events: events.len(),
                    pending_deliveries: deliveries.len(),
                    consumer_count: consumers.len(),
                });
            }
            Message::Shutdown { reply } => {
                shutdown_reply = Some(reply);
            }
        }

        if shutdown_reply.is_some() && deliveries.is_empty() {
            for state in consumers.values_mut() {
                while let Some(reply) = state.receivers.pop_front() {
                    let _ = reply.send(Err(EventBusError::Closed));
                }
            }
            if let Some(reply) = shutdown_reply.take() {
                let _ = reply.send(());
            }
            break;
        }
    }
}

fn envelope(stream_instance_id: &str, sequence: u64, request: EventRequest) -> EventEnvelope {
    let sequence_string = sequence.to_string();
    let id = derive_id(
        "event",
        &[
            stream_instance_id,
            &sequence_string,
            &format!("{:?}", request.kind),
            &request.command_id,
        ],
    );
    EventEnvelope {
        id,
        stream_instance_id: stream_instance_id.to_string(),
        sequence,
        kind: request.kind,
        schema_version: request.schema_version,
        emitted_at: now(),
        command_id: request.command_id,
        correlation_id: request.correlation_id,
        causation_id: request.causation_id,
        subject_ids: request.subject_ids,
        payload: request.payload,
        parent_span: request.parent_span,
    }
}

fn has_delivery_for(consumer_id: &str, deliveries: &HashMap<String, DeliveryRecord>) -> bool {
    deliveries
        .values()
        .any(|record| record.consumer_id == consumer_id)
}

fn lease_available(
    consumer_id: &str,
    consumers: &mut HashMap<String, ConsumerState>,
    events: &HashMap<String, RetainedEvent>,
    deliveries: &mut HashMap<String, DeliveryRecord>,
    sender: &mpsc::Sender<Message>,
) {
    loop {
        let next = {
            let Some(state) = consumers.get_mut(consumer_id) else {
                return;
            };
            if state.retry_blocks_order
                || state.in_flight >= state.subscription.max_in_flight
                || state.pending.is_empty()
                || state.receivers.is_empty()
            {
                return;
            }
            let delivery_id = state.pending.pop_front().expect("checked above");
            let receiver = state.receivers.pop_front().expect("checked above");
            state.in_flight += 1;
            (delivery_id, receiver, state.subscription.lease_duration)
        };
        let (delivery_id, receiver, lease_duration) = next;
        let Some(record) = deliveries.get_mut(&delivery_id) else {
            if let Some(state) = consumers.get_mut(consumer_id) {
                state.in_flight = state.in_flight.saturating_sub(1);
            }
            continue;
        };
        let Some(retained) = events.get(&record.event_id) else {
            if let Some(state) = consumers.get_mut(consumer_id) {
                state.in_flight = state.in_flight.saturating_sub(1);
            }
            deliveries.remove(&delivery_id);
            continue;
        };
        record.attempt = record.attempt.saturating_add(1);
        record.state = DeliveryState::InFlight;
        let attempt = record.attempt;
        let lease_deadline = chrono::Utc::now()
            + chrono::TimeDelta::from_std(lease_duration)
                .expect("Delivery lease fits chrono duration");
        let delivery = EventDelivery {
            id: record.id.clone(),
            event: retained.envelope.clone(),
            consumer_id: consumer_id.to_string(),
            attempt,
            lease_deadline: lease_deadline.to_rfc3339_opts(chrono::SecondsFormat::Millis, true),
        };
        if receiver.send(Ok(delivery)).is_err() {
            record.state = DeliveryState::Pending;
            if let Some(state) = consumers.get_mut(consumer_id) {
                state.in_flight = state.in_flight.saturating_sub(1);
                state.pending.push_front(delivery_id);
            }
            continue;
        }
        let sender = sender.clone();
        let lease_delivery_id = delivery_id;
        tokio::spawn(async move {
            tokio::time::sleep(lease_duration).await;
            let _ = sender
                .send(Message::LeaseExpired {
                    delivery_id: lease_delivery_id,
                    attempt,
                })
                .await;
        });
    }
}

fn acknowledge(
    consumer_id: &str,
    delivery_id: &str,
    attempt: u32,
    consumers: &mut HashMap<String, ConsumerState>,
    events: &mut HashMap<String, RetainedEvent>,
    deliveries: &mut HashMap<String, DeliveryRecord>,
    sender: &mpsc::Sender<Message>,
) {
    let Some(record) = deliveries.get(delivery_id) else {
        return;
    };
    if record.consumer_id != consumer_id
        || record.attempt != attempt
        || record.state != DeliveryState::InFlight
    {
        return;
    }
    let event_id = record.event_id.clone();
    deliveries.remove(delivery_id);
    if let Some(state) = consumers.get_mut(consumer_id) {
        state.in_flight = state.in_flight.saturating_sub(1);
    }
    if let Some(event) = events.get_mut(&event_id) {
        event.awaiting.remove(consumer_id);
        if event.awaiting.is_empty() {
            events.remove(&event_id);
        }
    }
    tracing::info!(
        "delivery.id" = %delivery_id,
        "event.id" = %event_id,
        "delivery.consumer_id" = %consumer_id,
        "delivery.attempt" = attempt as u64,
        "Event Delivery acknowledged"
    );
    lease_available(consumer_id, consumers, events, deliveries, sender);
}

fn reject(
    consumer_id: &str,
    delivery_id: &str,
    attempt: u32,
    reason: &str,
    consumers: &mut HashMap<String, ConsumerState>,
    deliveries: &mut HashMap<String, DeliveryRecord>,
    sender: &mpsc::Sender<Message>,
) {
    let Some(record) = deliveries.get_mut(delivery_id) else {
        return;
    };
    if record.consumer_id != consumer_id
        || record.attempt != attempt
        || record.state != DeliveryState::InFlight
    {
        return;
    }
    record.state = DeliveryState::WaitingToRetry;
    if let Some(state) = consumers.get_mut(consumer_id) {
        state.in_flight = state.in_flight.saturating_sub(1);
        if state.subscription.max_in_flight == 1 {
            state.retry_blocks_order = true;
        }
    }
    let delay = retry_delay(attempt);
    tracing::warn!(
        "delivery.id" = %delivery_id,
        "delivery.consumer_id" = %consumer_id,
        "delivery.attempt" = attempt as u64,
        "retry.delay_ms" = delay.as_millis() as u64,
        "error.message" = %reason,
        "Event Delivery not acknowledged; scheduling redelivery"
    );
    let sender = sender.clone();
    let delivery_id = delivery_id.to_string();
    tokio::spawn(async move {
        tokio::time::sleep(delay).await;
        let _ = sender.send(Message::RedeliveryReady { delivery_id }).await;
    });
}

fn retry_delay(attempt: u32) -> Duration {
    let exponent = attempt.saturating_sub(1).min(6);
    Duration::from_secs((1_u64 << exponent).min(RETRY_MAX_SECONDS))
}

fn now() -> String {
    chrono::Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Millis, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn concrete_events_keep_overlapping_domain_classifications() {
        assert!(EventKind::GraphRebuildStarted.is_a(EventClass::GraphEvent));
        assert!(EventKind::NodeGraphRebuildStarted.is_a(EventClass::GraphEvent));
        assert!(EventKind::NodeGraphRebuildStarted.is_a(EventClass::NodeEvent));

        assert!(EventKind::NodeContractProjected.is_a(EventClass::NodeEvent));
        assert!(EventKind::NodeContractProjected.is_a(EventClass::ContractEvent));
        assert!(EventKind::NodeContractProjected.is_a(EventClass::ProjectionEvent));

        assert!(EventKind::OccurrenceRelianceEstablished.is_a(EventClass::ContractEvent));
        assert!(EventKind::OccurrenceRelianceEstablished.is_a(EventClass::RelationEvent));

        assert!(EventKind::NodeSemanticRelationAssessmentCompleted.is_a(EventClass::NodeEvent));
        assert!(
            EventKind::NodeSemanticRelationAssessmentCompleted.is_a(EventClass::AssessmentEvent)
        );
    }

    fn request(command_id: &str, subject_id: &str) -> EventRequest {
        EventRequest::new(EventKind::NodeAdded, command_id)
            .with_subject(subject_id)
            .with_payload(json!({"node_id": subject_id}))
    }

    #[tokio::test]
    async fn nack_redelivers_the_same_event_and_delivery() {
        let (bus, task) = EventBus::start(EventTap::default());
        bus.register(
            Subscription::new("consumer", [EventKind::NodeAdded], 1)
                .with_lease(Duration::from_secs(30)),
        )
        .await
        .unwrap();
        let first_event = bus.publish(request("c1", "n1")).await.unwrap();
        let first = bus.receive("consumer").await.unwrap();
        bus.nack(&first, "retry").await.unwrap();
        tokio::time::sleep(Duration::from_millis(1_100)).await;
        let second = bus.receive("consumer").await.unwrap();
        assert_eq!(second.event.id, first_event.id);
        assert_eq!(second.id, first.id);
        assert_eq!(second.attempt, 2);
        bus.ack(&second).await.unwrap();
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }

    #[tokio::test]
    async fn acknowledged_delivery_is_not_redelivered() {
        let (bus, task) = EventBus::start(EventTap::default());
        bus.register(Subscription::new("consumer", [EventKind::NodeAdded], 1))
            .await
            .unwrap();
        bus.publish(request("c1", "n1")).await.unwrap();
        let delivery = bus.receive("consumer").await.unwrap();
        bus.ack(&delivery).await.unwrap();
        assert_eq!(bus.snapshot().await.unwrap().pending_deliveries, 0);
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }

    #[tokio::test]
    async fn abstract_subscription_delivers_the_concrete_event_once() {
        let (bus, task) = EventBus::start(EventTap::default());
        bus.register(
            Subscription::new("node-consumer", [EventKind::NodeAdded], 1)
                .with_event_class(EventClass::NodeEvent),
        )
        .await
        .unwrap();

        let emitted = bus.publish(request("c1", "n1")).await.unwrap();
        let delivery = bus.receive("node-consumer").await.unwrap();

        assert_eq!(delivery.event.id, emitted.id);
        assert_eq!(delivery.event.kind, EventKind::NodeAdded);
        assert!(delivery.event.kind.is_a(EventClass::DomainEvent));
        assert!(delivery.event.kind.is_a(EventClass::NodeEvent));
        assert!(!delivery.event.kind.is_a(EventClass::EvidenceEvent));

        bus.ack(&delivery).await.unwrap();
        assert_eq!(bus.snapshot().await.unwrap().pending_deliveries, 0);
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }

    #[tokio::test]
    async fn consumer_acknowledgements_are_independent() {
        let (bus, task) = EventBus::start(EventTap::default());
        bus.register(Subscription::new("a", [EventKind::NodeAdded], 1))
            .await
            .unwrap();
        bus.register(Subscription::new("b", [EventKind::NodeAdded], 1))
            .await
            .unwrap();
        bus.publish(request("c1", "n1")).await.unwrap();
        let a = bus.receive("a").await.unwrap();
        let b = bus.receive("b").await.unwrap();
        bus.ack(&a).await.unwrap();
        assert_eq!(bus.snapshot().await.unwrap().pending_deliveries, 1);
        bus.ack(&b).await.unwrap();
        assert_eq!(bus.snapshot().await.unwrap().pending_deliveries, 0);
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }

    #[tokio::test]
    async fn max_in_flight_one_preserves_sequence_order() {
        let (bus, task) = EventBus::start(EventTap::default());
        bus.register(Subscription::new("serial", [EventKind::NodeAdded], 1))
            .await
            .unwrap();
        bus.publish(request("c1", "n1")).await.unwrap();
        bus.publish(request("c2", "n2")).await.unwrap();
        let first = bus.receive("serial").await.unwrap();
        assert_eq!(first.event.sequence, 1);
        bus.ack(&first).await.unwrap();
        let second = bus.receive("serial").await.unwrap();
        assert_eq!(second.event.sequence, 2);
        bus.ack(&second).await.unwrap();
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }

    #[tokio::test]
    async fn a_new_consumer_does_not_receive_an_existing_event() {
        let (bus, task) = EventBus::start(EventTap::default());
        let event = bus.publish(request("c1", "n1")).await.unwrap();
        bus.register(Subscription::new("late", [EventKind::NodeAdded], 1))
            .await
            .unwrap();
        let second = bus.publish(request("c2", "n2")).await.unwrap();
        let delivery = bus.receive("late").await.unwrap();
        assert_eq!(delivery.event.id, second.id);
        assert_ne!(delivery.event.id, event.id);
        bus.ack(&delivery).await.unwrap();
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }

    #[tokio::test]
    async fn a_new_bus_starts_empty_with_a_distinct_stream() {
        let (first, first_task) = EventBus::start(EventTap::default());
        let first_stream = first.snapshot().await.unwrap().stream_instance_id;
        first.shutdown().await.unwrap();
        first_task.await.unwrap();

        let (second, second_task) = EventBus::start(EventTap::default());
        let snapshot = second.snapshot().await.unwrap();
        assert_ne!(snapshot.stream_instance_id, first_stream);
        assert_eq!(snapshot.last_sequence, 0);
        assert_eq!(snapshot.retained_events, 0);
        second.shutdown().await.unwrap();
        second_task.await.unwrap();
    }

    #[tokio::test]
    async fn an_expired_lease_redelivers_and_ignores_a_stale_ack() {
        let (bus, task) = EventBus::start(EventTap::default());
        bus.register(
            Subscription::new("consumer", [EventKind::NodeAdded], 1)
                .with_lease(Duration::from_millis(20)),
        )
        .await
        .unwrap();
        bus.publish(request("c1", "n1")).await.unwrap();
        let expired = bus.receive("consumer").await.unwrap();
        tokio::time::sleep(Duration::from_millis(1_100)).await;
        let current = bus.receive("consumer").await.unwrap();
        bus.ack(&expired).await.unwrap();
        assert_eq!(bus.snapshot().await.unwrap().pending_deliveries, 1);
        bus.ack(&current).await.unwrap();
        bus.shutdown().await.unwrap();
        task.await.unwrap();
    }
}
