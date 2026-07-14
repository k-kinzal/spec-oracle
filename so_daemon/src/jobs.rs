//! NodeAdded hooks and the in-memory Job Mailbox.
//!
//! The manager owns every Job until its Plugin result has been written to the
//! Node. Workers receive cloned execution data; an error or worker panic returns
//! the owned Job to `pending` with bounded exponential backoff.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use serde_json::Value;
use thiserror::Error;
use tokio::sync::{mpsc, oneshot};

use crate::domain::{Evidence, MetaUpdate, Node};
use crate::mailbox::{derive_id, NodeAdded};
use crate::store::{BlobStore, GraphStore};

const MAILBOX_CAPACITY: usize = 1024;
const RETRY_MAX_SECONDS: u64 = 60;

/// Resources available to a Plugin execution.
pub struct PluginContext<'a> {
    pub blobs: &'a dyn BlobStore,
    pub graph: &'a (dyn GraphStore + Send + Sync),
    pub now: &'a str,
}

/// The durable effects of one successful Job execution. Most Jobs only append
/// their namespaced JSON value. Evidence capture additionally replaces the
/// Node's captured-evidence view in the same store operation.
pub struct JobOutput {
    pub value: Value,
    pub evidence: Option<Vec<Evidence>>,
}

impl JobOutput {
    pub fn metadata(value: Value) -> JobOutput {
        JobOutput {
            value,
            evidence: None,
        }
    }

    pub fn captured_evidence(value: Value, evidence: Vec<Evidence>) -> JobOutput {
        JobOutput {
            value,
            evidence: Some(evidence),
        }
    }
}

/// A NodeAdded hook that computes one namespaced durable Job result.
///
/// Implementations may run more than once and must keep external side effects
/// idempotent. The daemon makes the Node update itself idempotent by deriving a
/// stable Job ID from the Event and Plugin name.
pub trait NodeMetaPlugin: Send + Sync {
    fn handles(&self, node: &Node) -> bool;
    fn run(&self, node: &Node, context: &PluginContext<'_>) -> Result<JobOutput, String>;
}

/// Link-time Plugin registration.
pub struct PluginRegistration {
    pub name: &'static str,
    pub factory: fn() -> Box<dyn NodeMetaPlugin>,
}

impl PluginRegistration {
    pub const fn new(
        name: &'static str,
        factory: fn() -> Box<dyn NodeMetaPlugin>,
    ) -> PluginRegistration {
        PluginRegistration { name, factory }
    }
}

inventory::collect!(PluginRegistration);

#[derive(Clone)]
struct RegisteredPlugin {
    name: &'static str,
    plugin: Arc<dyn NodeMetaPlugin>,
}

fn registered_plugins() -> Vec<RegisteredPlugin> {
    let mut registrations: Vec<&'static PluginRegistration> =
        inventory::iter::<PluginRegistration>.into_iter().collect();
    registrations.sort_by_key(|registration| registration.name);
    registrations
        .into_iter()
        .map(|registration| RegisteredPlugin {
            name: registration.name,
            plugin: Arc::from((registration.factory)()),
        })
        .collect()
}

/// Sending side used by the Add Mailbox and shutdown coordinator.
#[derive(Clone)]
pub struct JobMailbox {
    sender: mpsc::Sender<Message>,
}

#[derive(Debug, Error)]
pub enum JobMailboxError {
    #[error("Job Mailbox is closed")]
    Closed,
    #[error("Job Mailbox stopped before shutdown completed")]
    ShutdownDropped,
}

enum Message {
    NodeAdded(Box<NodeAdded>),
    AttemptFinished {
        job_id: String,
        result: Result<(), String>,
    },
    RetryReady {
        job_id: String,
    },
    Shutdown {
        reply: oneshot::Sender<()>,
    },
}

struct Job {
    id: String,
    node: Node,
    source: &'static str,
    plugin: Arc<dyn NodeMetaPlugin>,
    parent_span: tracing::Span,
    attempts: u32,
    in_flight: bool,
}

impl JobMailbox {
    pub fn start(
        nodes: Arc<dyn GraphStore + Send + Sync>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
    ) -> (JobMailbox, tokio::task::JoinHandle<()>) {
        Self::start_with_plugins(nodes, blobs, registered_plugins())
    }

    fn start_with_plugins(
        nodes: Arc<dyn GraphStore + Send + Sync>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
        plugins: Vec<RegisteredPlugin>,
    ) -> (JobMailbox, tokio::task::JoinHandle<()>) {
        let (sender, receiver) = mpsc::channel(MAILBOX_CAPACITY);
        let mailbox = JobMailbox {
            sender: sender.clone(),
        };
        let task = tokio::spawn(run(receiver, sender, nodes, blobs, plugins));
        (mailbox, task)
    }

    pub async fn node_added(&self, event: NodeAdded) -> Result<(), JobMailboxError> {
        self.sender
            .send(Message::NodeAdded(Box::new(event)))
            .await
            .map_err(|_| JobMailboxError::Closed)
    }

    /// Stop accepting upstream events after the Add Mailbox has drained, then
    /// wait until every accepted Job has successfully updated its Node.
    pub async fn shutdown(&self) -> Result<(), JobMailboxError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Shutdown { reply })
            .await
            .map_err(|_| JobMailboxError::Closed)?;
        received.await.map_err(|_| JobMailboxError::ShutdownDropped)
    }
}

async fn run(
    mut receiver: mpsc::Receiver<Message>,
    sender: mpsc::Sender<Message>,
    nodes: Arc<dyn GraphStore + Send + Sync>,
    blobs: Arc<dyn BlobStore + Send + Sync>,
    plugins: Vec<RegisteredPlugin>,
) {
    let mut jobs: HashMap<String, Job> = HashMap::new();
    let mut shutdown_reply: Option<oneshot::Sender<()>> = None;

    while let Some(message) = receiver.recv().await {
        match message {
            Message::NodeAdded(event) => {
                enqueue_plugins(*event, &plugins, &mut jobs, &sender, &nodes, &blobs);
            }
            Message::AttemptFinished { job_id, result } => match result {
                Ok(()) => {
                    jobs.remove(&job_id);
                    tracing::info!("job.id" = %job_id, "Node Meta Job completed");
                }
                Err(error) => {
                    if let Some(job) = jobs.get_mut(&job_id) {
                        job.in_flight = false;
                        let delay = retry_delay(job.attempts);
                        tracing::warn!(
                            "job.id" = %job_id,
                            "job.source" = job.source,
                            "job.attempt" = job.attempts as u64,
                            "retry.delay_ms" = delay.as_millis() as u64,
                            "error.message" = %error,
                            "Node Meta Job failed; scheduling retry"
                        );
                        schedule_retry(job_id, delay, sender.clone());
                    }
                }
            },
            Message::RetryReady { job_id } => {
                dispatch(&job_id, &mut jobs, &sender, &nodes, &blobs);
            }
            Message::Shutdown { reply } => {
                shutdown_reply = Some(reply);
            }
        }

        if jobs.is_empty() {
            if let Some(reply) = shutdown_reply.take() {
                let _ = reply.send(());
                break;
            }
        }
    }
}

fn enqueue_plugins(
    event: NodeAdded,
    plugins: &[RegisteredPlugin],
    jobs: &mut HashMap<String, Job>,
    sender: &mpsc::Sender<Message>,
    nodes: &Arc<dyn GraphStore + Send + Sync>,
    blobs: &Arc<dyn BlobStore + Send + Sync>,
) {
    for registration in plugins {
        let job_id = derive_id("job", &[&event.id, registration.name]);
        if jobs.contains_key(&job_id) {
            continue;
        }
        jobs.insert(
            job_id.clone(),
            Job {
                id: job_id.clone(),
                node: event.node.clone(),
                source: registration.name,
                plugin: registration.plugin.clone(),
                parent_span: event.parent_span.clone(),
                attempts: 0,
                in_flight: false,
            },
        );
        dispatch(&job_id, jobs, sender, nodes, blobs);
    }
}

fn dispatch(
    job_id: &str,
    jobs: &mut HashMap<String, Job>,
    sender: &mpsc::Sender<Message>,
    nodes: &Arc<dyn GraphStore + Send + Sync>,
    blobs: &Arc<dyn BlobStore + Send + Sync>,
) {
    let Some(job) = jobs.get_mut(job_id) else {
        return;
    };
    if job.in_flight {
        return;
    }
    job.in_flight = true;
    job.attempts = job.attempts.saturating_add(1);

    let id = job.id.clone();
    let node = job.node.clone();
    let source = job.source;
    let plugin = job.plugin.clone();
    let parent_span = job.parent_span.clone();
    let nodes = nodes.clone();
    let blobs = blobs.clone();
    let sender = sender.clone();
    tokio::spawn(async move {
        let attempt_id = id.clone();
        let result = tokio::task::spawn_blocking(move || {
            let span = tracing::info_span!(
                parent: &parent_span,
                "spec.job.execute",
                "job.id" = %attempt_id,
                "job.source" = source,
                "node.id" = %node.id,
            );
            let _entered = span.enter();
            let now = now();
            let context = PluginContext {
                blobs: &*blobs,
                graph: &*nodes,
                now: &now,
            };
            if !plugin.handles(&node) {
                return Ok(());
            }
            let output = plugin.run(&node, &context)?;
            let update = MetaUpdate {
                source: source.to_string(),
                applied_at: now,
                value: output.value,
            };
            nodes
                .apply_job_result(&node.id, &attempt_id, &update, output.evidence.as_deref())
                .map_err(|error| error.to_string())
        })
        .await
        .map_err(|error| format!("Job worker failed: {error}"))
        .and_then(|result| result);
        let _ = sender
            .send(Message::AttemptFinished { job_id: id, result })
            .await;
    });
}

fn schedule_retry(job_id: String, delay: Duration, sender: mpsc::Sender<Message>) {
    tokio::spawn(async move {
        tokio::time::sleep(delay).await;
        let _ = sender.send(Message::RetryReady { job_id }).await;
    });
}

fn retry_delay(attempts: u32) -> Duration {
    let exponent = attempts.saturating_sub(1).min(6);
    Duration::from_secs((1_u64 << exponent).min(RETRY_MAX_SECONDS))
}

fn now() -> String {
    chrono::Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Secs, true)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;
    use crate::domain::{Meta, Node};
    use crate::store::{InMemoryNodeStore, NodeStore, StoreError};

    struct NoBlobs;
    impl BlobStore for NoBlobs {
        fn put_blob(&self, _hash: &str, _bytes: &[u8]) -> Result<(), StoreError> {
            Ok(())
        }

        fn get_blob(&self, _hash: &str) -> Result<Option<Vec<u8>>, StoreError> {
            Ok(None)
        }
    }

    struct FailsOnce {
        attempts: Arc<AtomicUsize>,
    }

    impl NodeMetaPlugin for FailsOnce {
        fn handles(&self, _node: &Node) -> bool {
            true
        }

        fn run(&self, _node: &Node, _context: &PluginContext<'_>) -> Result<JobOutput, String> {
            if self.attempts.fetch_add(1, Ordering::SeqCst) == 0 {
                Err("first attempt fails".to_string())
            } else {
                Ok(JobOutput::metadata(serde_json::json!({"commit": "abc123"})))
            }
        }
    }

    fn node() -> Node {
        Node {
            id: "n1".to_string(),
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

    #[tokio::test]
    async fn failed_job_is_retried_and_shutdown_drains() {
        let store = Arc::new(InMemoryNodeStore::new());
        let n = node();
        store.add_node(&n).unwrap();
        let attempts = Arc::new(AtomicUsize::new(0));
        let plugin = RegisteredPlugin {
            name: "fails-once",
            plugin: Arc::new(FailsOnce {
                attempts: attempts.clone(),
            }),
        };
        let (mailbox, task) =
            JobMailbox::start_with_plugins(store.clone(), Arc::new(NoBlobs), vec![plugin]);

        mailbox.node_added(NodeAdded::new("m1", n)).await.unwrap();
        mailbox.shutdown().await.unwrap();
        task.await.unwrap();

        assert_eq!(attempts.load(Ordering::SeqCst), 2);
        let stored = store.get_node("n1").unwrap().unwrap();
        assert_eq!(stored.meta.updates.len(), 1);
        assert_eq!(
            stored.meta.updates.values().next().unwrap().value,
            serde_json::json!({"commit": "abc123"})
        );
    }

    #[test]
    fn built_in_github_plugin_is_registered() {
        let plugins = registered_plugins();
        assert!(plugins
            .iter()
            .any(|plugin| plugin.name == "github-evidence"));
        assert!(plugins
            .iter()
            .any(|plugin| plugin.name == "graph-generation"));
        assert!(plugins
            .iter()
            .any(|plugin| plugin.name == "evidence-capture"));
    }
}
