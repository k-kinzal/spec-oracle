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
use crate::store::{BlobStore, GraphStore};

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
        reply: oneshot::Sender<Result<Vec<Node>, AddError>>,
    },
    Shutdown {
        reply: oneshot::Sender<()>,
    },
}

impl AddMailbox {
    pub fn start(
        nodes: Arc<dyn GraphStore + Send + Sync>,
        blobs: Arc<dyn BlobStore + Send + Sync>,
        jobs: JobMailbox,
    ) -> (AddMailbox, tokio::task::JoinHandle<()>) {
        let (sender, receiver) = mpsc::channel(MAILBOX_CAPACITY);
        let mailbox = AddMailbox { sender };
        let task = tokio::spawn(run(receiver, nodes, blobs, jobs));
        (mailbox, task)
    }

    pub async fn add(&self, input: AddInput) -> Result<Vec<Node>, AddMailboxError> {
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
    blobs: Arc<dyn BlobStore + Send + Sync>,
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
                let blobs = blobs.clone();
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
                    add::run(&request, &*nodes, &*blobs)
                })
                .await;

                match outcome {
                    Ok(Ok(persisted)) => {
                        let events: Vec<NodeAdded> = persisted
                            .iter()
                            .cloned()
                            .map(|node| {
                                NodeAdded::with_parent(&message_id, node, event_parent.clone())
                            })
                            .collect();
                        let _ = reply.send(Ok(persisted));
                        for event in events {
                            if let Err(error) = jobs.node_added(event).await {
                                tracing::error!(
                                    "message.id" = %message_id,
                                    "error.message" = %error,
                                    "NodeAdded event could not enter the Job Mailbox"
                                );
                            }
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
    use crate::store::{InMemoryNodeStore, StoreError};

    struct NoBlobs;
    impl BlobStore for NoBlobs {
        fn put_blob(&self, _hash: &str, _bytes: &[u8]) -> Result<(), StoreError> {
            Ok(())
        }

        fn get_blob(&self, _hash: &str) -> Result<Option<Vec<u8>>, StoreError> {
            Ok(None)
        }
    }

    #[tokio::test]
    async fn add_reply_is_returned_and_shutdown_drains() {
        let store = Arc::new(InMemoryNodeStore::new());
        let blobs = Arc::new(NoBlobs);
        let (jobs, jobs_task) = JobMailbox::start(store.clone(), blobs.clone());
        let (adds, adds_task) = AddMailbox::start(store, blobs, jobs.clone());

        let nodes = adds
            .add(AddInput {
                specification: "The pump shall stop.".to_string(),
                evidence: vec![],
                now: "2026-07-11T00:00:00Z".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
            })
            .await
            .unwrap();
        assert_eq!(nodes.len(), 1);

        adds.shutdown().await.unwrap();
        adds_task.await.unwrap();
        jobs.shutdown().await.unwrap();
        jobs_task.await.unwrap();
    }
}
