//! The in-memory Add Mailbox.
//!
//! Each command receives one identity on entry. The Mailbox serializes Node
//! additions, replies with the store result, and emits NodeAdded events from the
//! same completion handler. Event delivery is intentionally independent of the
//! Add RPC result.

use std::sync::Arc;

use thiserror::Error;
use tokio::sync::{mpsc, oneshot};

use crate::add::{self, AddError, AddRequest};
use crate::domain::Node;
use crate::jobs::JobMailbox;
use crate::mailbox::{new_message_id, NodeAdded};
use crate::store::GraphStore;

const MAILBOX_CAPACITY: usize = 256;

pub struct AddInput {
    pub specification: String,
    pub evidence: Vec<String>,
    pub now: String,
    pub cli: String,
    pub cli_version: String,
}

#[derive(Clone)]
pub struct AddMailbox {
    sender: mpsc::Sender<Message>,
}

#[derive(Debug, Error)]
pub enum AddMailboxError {
    #[error(transparent)]
    Add(#[from] AddError),
    #[error("Add Mailbox is closed")]
    Closed,
    #[error("Add Mailbox stopped before replying")]
    ReplyDropped,
    #[error("Add Mailbox stopped before shutdown completed")]
    ShutdownDropped,
}

enum Message {
    Add {
        message_id: String,
        input: AddInput,
        parent_span: tracing::Span,
        reply: oneshot::Sender<Result<Node, AddError>>,
    },
    Shutdown {
        reply: oneshot::Sender<()>,
    },
}

impl AddMailbox {
    pub fn start(
        nodes: Arc<dyn GraphStore + Send + Sync>,
        jobs: JobMailbox,
    ) -> (AddMailbox, tokio::task::JoinHandle<()>) {
        let (sender, receiver) = mpsc::channel(MAILBOX_CAPACITY);
        let mailbox = AddMailbox { sender };
        let task = tokio::spawn(run(receiver, nodes, jobs));
        (mailbox, task)
    }

    pub async fn add(&self, input: AddInput) -> Result<Node, AddMailboxError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Add {
                message_id: new_message_id(),
                input,
                parent_span: tracing::Span::current(),
                reply,
            })
            .await
            .map_err(|_| AddMailboxError::Closed)?;
        received
            .await
            .map_err(|_| AddMailboxError::ReplyDropped)?
            .map_err(AddMailboxError::Add)
    }

    pub async fn shutdown(&self) -> Result<(), AddMailboxError> {
        let (reply, received) = oneshot::channel();
        self.sender
            .send(Message::Shutdown { reply })
            .await
            .map_err(|_| AddMailboxError::Closed)?;
        received.await.map_err(|_| AddMailboxError::ShutdownDropped)
    }
}

async fn run(
    mut receiver: mpsc::Receiver<Message>,
    nodes: Arc<dyn GraphStore + Send + Sync>,
    jobs: JobMailbox,
) {
    while let Some(message) = receiver.recv().await {
        match message {
            Message::Add {
                message_id,
                input,
                parent_span,
                reply,
            } => {
                let nodes = nodes.clone();
                let operation_id = message_id.clone();
                let event_parent = parent_span.clone();
                let outcome = tokio::task::spawn_blocking(move || {
                    let span = tracing::info_span!(
                        parent: &parent_span,
                        "spec.add.mailbox.handle",
                        "message.id" = %operation_id,
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
                    add::run_with_status(&request, &*nodes)
                })
                .await;

                match outcome {
                    Ok(Ok(outcome)) => {
                        // Reused Nodes still emit the same Node-addressed event:
                        // this reconciles unfinished Jobs after a daemon restart,
                        // while the Job Mailbox coalesces concurrent duplicates.
                        let event =
                            NodeAdded::with_parent(&message_id, outcome.node.clone(), event_parent);
                        let _ = reply.send(Ok(outcome.node));
                        if let Err(error) = jobs.node_added(event).await {
                            tracing::error!(
                                "message.id" = %message_id,
                                "error.message" = %error,
                                "NodeAdded event could not enter the Job Mailbox"
                            );
                        }
                    }
                    Ok(Err(error)) => {
                        let _ = reply.send(Err(error));
                    }
                    Err(error) => {
                        tracing::error!(
                            "message.id" = %message_id,
                            "error.message" = %error,
                            "Add Mailbox worker failed"
                        );
                        drop(reply);
                    }
                }
            }
            Message::Shutdown { reply } => {
                let _ = reply.send(());
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::{InMemoryNodeStore, NodeStore};

    #[tokio::test]
    async fn add_reply_is_returned_and_shutdown_drains() {
        let store = Arc::new(InMemoryNodeStore::new());
        let temp = tempfile::tempdir().unwrap();
        let evidence_path = temp.path().join("evidence.txt");
        std::fs::write(&evidence_path, "evidence bytes").unwrap();
        let blobs =
            Arc::new(crate::store::FileBlobStore::open(&temp.path().join("blobs")).unwrap());
        let (jobs, jobs_task) = JobMailbox::start(store.clone(), blobs);
        let (adds, adds_task) = AddMailbox::start(store.clone(), jobs.clone());

        let node = adds
            .add(AddInput {
                specification: "The pump shall stop.".to_string(),
                evidence: vec![evidence_path.to_string_lossy().into_owned()],
                now: "2026-07-11T00:00:00Z".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
            })
            .await
            .unwrap();
        assert_eq!(node.statement, "The pump shall stop.");
        assert!(node.meta.evidence.is_empty(), "Add reply precedes capture");

        adds.shutdown().await.unwrap();
        adds_task.await.unwrap();
        jobs.shutdown().await.unwrap();
        jobs_task.await.unwrap();

        let captured = store.get_node(&node.id).unwrap().unwrap();
        assert_eq!(captured.meta.evidence.len(), 1);
        assert!(captured
            .meta
            .updates
            .values()
            .any(|update| update.source == "evidence-capture"));
        let capture_update = captured
            .meta
            .updates
            .values()
            .find(|update| update.source == "evidence-capture")
            .unwrap();
        assert_eq!(capture_update.value["status"], "captured");
        assert_eq!(capture_update.value["evidence"][0]["snapshot"]["bytes"], 14);
    }
}
