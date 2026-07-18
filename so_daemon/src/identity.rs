//! Content-derived and random identity helpers for Commands, Events, and Deliveries.
//!
//! Random Command and stream IDs distinguish fresh requests. Stable hashes are
//! used only where a content-addressed identity or Delivery identity is
//! required.

use sha2::{Digest, Sha256};

pub fn new_message_id() -> String {
    uuid::Uuid::new_v4().to_string()
}

/// Derive a stable SHA-256 ID within one Mailbox message.
///
/// Length-prefixing each part avoids ambiguous concatenations. `namespace`
/// keeps Node, Event, and Delivery identities distinct even if their parts match.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derived_ids_are_stable_and_namespaced() {
        let first = derive_id("node", &["message", "0"]);
        assert_eq!(first, derive_id("node", &["message", "0"]));
        assert_ne!(first, derive_id("event", &["message", "0"]));
        assert_ne!(first, derive_id("node", &["message", "1"]));
    }
}
