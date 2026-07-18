//! Best-effort archival taps for the volatile [`EventBus`](crate::event_bus::EventBus).
//!
//! A sink is deliberately outside the delivery protocol. The Event Bus only
//! performs a non-blocking copy into each sink's bounded mailbox; a full
//! mailbox or a failing backend may lose archive records, but can never delay
//! Event acceptance or Consumer acknowledgement.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use tokio::sync::{mpsc, oneshot};

use crate::event_bus::EventEnvelope;

/// A pluggable external archive for observing accepted Events.
///
/// Implementations must make duplicate Event IDs idempotent. This interface is
/// not an Event broker, a replay source, or part of Consumer acknowledgement.
pub trait EventSink: Send + Sync {
    fn name(&self) -> &str;
    fn persist(&self, events: &[EventEnvelope]) -> Result<(), String>;
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EventTapMetrics {
    pub accepted: u64,
    pub dropped: u64,
    pub persist_success: u64,
    pub persist_failure: u64,
    pub retry: u64,
    pub batches: u64,
    pub last_batch_size: u64,
    pub last_sequence: u64,
    pub lag_events: u64,
    pub sequence_gaps: u64,
}

#[derive(Default)]
struct Metrics {
    accepted: AtomicU64,
    dropped: AtomicU64,
    persist_success: AtomicU64,
    persist_failure: AtomicU64,
    retry: AtomicU64,
    batches: AtomicU64,
    last_batch_size: AtomicU64,
    last_sequence: AtomicU64,
    high_watermark: AtomicU64,
    sequence_gaps: AtomicU64,
}

impl Metrics {
    fn snapshot(&self) -> EventTapMetrics {
        let last_sequence = self.last_sequence.load(Ordering::Relaxed);
        EventTapMetrics {
            accepted: self.accepted.load(Ordering::Relaxed),
            dropped: self.dropped.load(Ordering::Relaxed),
            persist_success: self.persist_success.load(Ordering::Relaxed),
            persist_failure: self.persist_failure.load(Ordering::Relaxed),
            retry: self.retry.load(Ordering::Relaxed),
            batches: self.batches.load(Ordering::Relaxed),
            last_batch_size: self.last_batch_size.load(Ordering::Relaxed),
            last_sequence,
            lag_events: self
                .high_watermark
                .load(Ordering::Relaxed)
                .saturating_sub(last_sequence),
            sequence_gaps: self.sequence_gaps.load(Ordering::Relaxed),
        }
    }
}

enum SinkMessage {
    Event(EventEnvelope),
    Shutdown(oneshot::Sender<()>),
}

#[derive(Clone)]
struct SinkMailbox {
    name: String,
    sender: mpsc::Sender<SinkMessage>,
}

/// Non-blocking fan-out from the Event Bus into dedicated sink workers.
#[derive(Clone, Default)]
pub struct EventTap {
    sinks: Arc<Vec<SinkMailbox>>,
    metrics: Arc<Metrics>,
}

impl EventTap {
    pub fn new(
        sinks: Vec<Arc<dyn EventSink>>,
        mailbox_capacity: usize,
        batch_size: usize,
    ) -> EventTap {
        assert!(
            mailbox_capacity > 0,
            "sink mailbox capacity must be positive"
        );
        assert!(batch_size > 0, "sink batch size must be positive");
        let metrics = Arc::new(Metrics::default());
        let mut mailboxes = Vec::with_capacity(sinks.len());
        for sink in sinks {
            let (sender, receiver) = mpsc::channel(mailbox_capacity);
            let name = sink.name().to_string();
            tokio::spawn(run_sink(receiver, sink, batch_size, metrics.clone()));
            mailboxes.push(SinkMailbox { name, sender });
        }
        EventTap {
            sinks: Arc::new(mailboxes),
            metrics,
        }
    }

    /// Copy an accepted Event without awaiting external storage.
    pub fn record(&self, event: &EventEnvelope) {
        self.metrics
            .high_watermark
            .fetch_max(event.sequence, Ordering::Relaxed);
        for sink in self.sinks.iter() {
            match sink.sender.try_send(SinkMessage::Event(event.clone())) {
                Ok(()) => {
                    self.metrics.accepted.fetch_add(1, Ordering::Relaxed);
                }
                Err(error) => {
                    self.metrics.dropped.fetch_add(1, Ordering::Relaxed);
                    tracing::warn!(
                        "event.sink" = %sink.name,
                        "event.id" = %event.id,
                        "event.sequence" = event.sequence,
                        "error.message" = %error,
                        "Event archive copy dropped"
                    );
                }
            }
        }
    }

    pub fn metrics(&self) -> EventTapMetrics {
        self.metrics.snapshot()
    }

    /// Best-effort drain of every sink mailbox. This does not change Event Bus
    /// delivery state and is only used during an orderly daemon shutdown.
    pub async fn shutdown(&self) {
        for sink in self.sinks.iter() {
            let (reply, received) = oneshot::channel();
            if sink.sender.send(SinkMessage::Shutdown(reply)).await.is_ok() {
                let _ = received.await;
            }
        }
    }
}

async fn run_sink(
    mut receiver: mpsc::Receiver<SinkMessage>,
    sink: Arc<dyn EventSink>,
    batch_size: usize,
    metrics: Arc<Metrics>,
) {
    let mut batch = Vec::with_capacity(batch_size);
    while let Some(message) = receiver.recv().await {
        let mut shutdown = None;
        match message {
            SinkMessage::Event(event) => batch.push(event),
            SinkMessage::Shutdown(reply) => shutdown = Some(reply),
        }

        while batch.len() < batch_size {
            match receiver.try_recv() {
                Ok(SinkMessage::Event(event)) => batch.push(event),
                Ok(SinkMessage::Shutdown(reply)) => {
                    shutdown = Some(reply);
                    break;
                }
                Err(_) => break,
            }
        }

        if !batch.is_empty() {
            persist_batch(&sink, &batch, &metrics).await;
            batch.clear();
        }
        if let Some(reply) = shutdown {
            let _ = reply.send(());
            break;
        }
    }
}

async fn persist_batch(sink: &Arc<dyn EventSink>, batch: &[EventEnvelope], metrics: &Arc<Metrics>) {
    const MAX_ATTEMPTS: usize = 3;
    let owned = batch.to_vec();
    let mut attempt = 0;
    loop {
        attempt += 1;
        let worker_sink = sink.clone();
        let worker_batch = owned.clone();
        let result = tokio::task::spawn_blocking(move || worker_sink.persist(&worker_batch)).await;
        match result {
            Ok(Ok(())) => {
                metrics
                    .persist_success
                    .fetch_add(owned.len() as u64, Ordering::Relaxed);
                metrics.batches.fetch_add(1, Ordering::Relaxed);
                metrics
                    .last_batch_size
                    .store(owned.len() as u64, Ordering::Relaxed);
                observe_sequences(&owned, metrics);
                return;
            }
            Ok(Err(error)) => {
                metrics.persist_failure.fetch_add(1, Ordering::Relaxed);
                tracing::warn!(
                    "event.sink" = sink.name(),
                    "event.sink.attempt" = attempt as u64,
                    "error.message" = %error,
                    "Event archive batch failed"
                );
            }
            Err(error) => {
                metrics.persist_failure.fetch_add(1, Ordering::Relaxed);
                tracing::warn!(
                    "event.sink" = sink.name(),
                    "event.sink.attempt" = attempt as u64,
                    "error.message" = %error,
                    "Event archive worker failed"
                );
            }
        }
        if attempt == MAX_ATTEMPTS {
            return;
        }
        metrics.retry.fetch_add(1, Ordering::Relaxed);
        tokio::time::sleep(Duration::from_millis(10 * attempt as u64)).await;
    }
}

fn observe_sequences(events: &[EventEnvelope], metrics: &Metrics) {
    for event in events {
        let prior = metrics
            .last_sequence
            .swap(event.sequence, Ordering::Relaxed);
        if prior != 0 && event.sequence > prior.saturating_add(1) {
            metrics
                .sequence_gaps
                .fetch_add(event.sequence - prior - 1, Ordering::Relaxed);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event_bus::EventKind;

    struct SlowSink;
    impl EventSink for SlowSink {
        fn name(&self) -> &str {
            "slow"
        }

        fn persist(&self, _events: &[EventEnvelope]) -> Result<(), String> {
            std::thread::sleep(Duration::from_millis(50));
            Ok(())
        }
    }

    fn event(sequence: u64) -> EventEnvelope {
        EventEnvelope {
            id: format!("event-{sequence}"),
            stream_instance_id: "stream".to_string(),
            sequence,
            kind: EventKind::NodeAdded,
            schema_version: 1,
            emitted_at: "2026-07-18T00:00:00Z".to_string(),
            command_id: format!("command-{sequence}"),
            correlation_id: "correlation".to_string(),
            causation_id: None,
            subject_ids: vec!["n1".to_string()],
            payload: serde_json::Value::Null,
            parent_span: None,
        }
    }

    #[tokio::test]
    async fn full_sink_mailbox_drops_are_measured() {
        let tap = EventTap::new(vec![Arc::new(SlowSink)], 1, 1);
        for sequence in 1..=100 {
            tap.record(&event(sequence));
        }
        tap.shutdown().await;
        let metrics = tap.metrics();
        assert!(metrics.accepted > 0);
        assert!(metrics.dropped > 0);
        assert_eq!(metrics.accepted + metrics.dropped, 100);
    }
}
