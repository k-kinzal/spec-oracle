//! In-process message identity shared by the Add and Job mailboxes.
//!
//! A new `message_id` identifies one Mailbox submission. NodeAdded identity is
//! instead derived from the content-addressed Node so concurrent submissions
//! of identical content coalesce into the same downstream Jobs.

use sha2::{Digest, Sha256};

use crate::domain::Node;

/// A successful Node addition event emitted by the Add Mailbox.
#[derive(Clone)]
pub struct NodeAdded {
    pub id: String,
    pub message_id: String,
    pub node: Node,
    pub parent_span: tracing::Span,
}

pub fn new_message_id() -> String {
    uuid::Uuid::new_v4().to_string()
}

/// Derive a stable SHA-256 ID within one Mailbox message.
///
/// Length-prefixing each part avoids ambiguous concatenations. `namespace`
/// keeps Node, Event, and Job identities distinct even if their parts match.
pub fn derive_id(namespace: &str, parts: &[&str]) -> String {
    let mut hasher = Sha256::new();
    hash_part(&mut hasher, namespace.as_bytes());
    for part in parts {
        hash_part(&mut hasher, part.as_bytes());
    }
    format!("{:x}", hasher.finalize())
}

fn hash_part(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

impl NodeAdded {
    pub fn new(message_id: &str, node: Node) -> NodeAdded {
        Self::with_parent(message_id, node, tracing::Span::current())
    }

    pub fn with_parent(message_id: &str, node: Node, parent_span: tracing::Span) -> NodeAdded {
        let mut evidence_requests = node.meta.evidence_requests.clone();
        evidence_requests.sort();
        evidence_requests.dedup();
        let mut parts = Vec::with_capacity(evidence_requests.len() + 1);
        parts.push(node.id.as_str());
        parts.extend(evidence_requests.iter().map(String::as_str));
        let id = derive_id("node-added", &parts);
        NodeAdded {
            id,
            message_id: message_id.to_string(),
            node,
            parent_span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, Node};

    #[test]
    fn derived_ids_are_stable_and_namespaced() {
        let first = derive_id("node", &["message", "0"]);
        assert_eq!(first, derive_id("node", &["message", "0"]));
        assert_ne!(first, derive_id("event", &["message", "0"]));
        assert_ne!(first, derive_id("node", &["message", "1"]));
    }

    #[test]
    fn node_added_identity_comes_from_the_reused_node() {
        let node = Node {
            id: "n1".to_string(),
            statement: "The pump shall stop.".to_string(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence_requests: vec![],
                evidence: vec![],
                created_at: "t".to_string(),
                cli: "spec".to_string(),
                cli_version: "test".to_string(),
                updates: Default::default(),
            },
        };
        let event = NodeAdded::new("m1", node);
        assert_eq!(event.id, derive_id("node-added", &["n1"]));
        let duplicate = NodeAdded::new("another-message", event.node.clone());
        assert_eq!(event.id, duplicate.id);

        let mut enriched = event.node.clone();
        enriched.meta.evidence_requests.push("new.rs:1".into());
        assert_ne!(event.id, NodeAdded::new("m1", enriched).id);
        assert_eq!(event.message_id, "m1");
    }
}
