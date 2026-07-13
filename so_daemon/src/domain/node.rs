//! The persisted node: one constrained-NL specification sentence.
//!
//! A node carries two orthogonal layers:
//!   * the **logical** layer — the sentence itself: the raw `statement` text in
//!     the constrained specification language, plus the `lang_version` that
//!     accepted it. The words are the source of truth; everything derivable
//!     from them — the parse tree, the speech act, the assume-guarantee
//!     contract reading — is a computed *view*, produced at response time and
//!     never stored;
//!   * the **epistemic** layer — raw evidence requests recorded at acceptance,
//!     followed by captured `meta.evidence` appended by an asynchronous Job.
//!
//! `meta` holds captured facts: each piece of evidence with its snapshot (sense
//! ②) and origin (sense ①), the node's own creation facts (sense ③), and
//! successful asynchronous updates produced by NodeAdded hooks.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::domain::locator::{Kind, Locator};
use crate::domain::origin::Origin;
use crate::domain::snapshot::Snapshot;

/// One grounded piece of evidence for a node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Evidence {
    /// Epistemic kind, recorded at ingest (`unknown` if unclassified).
    pub kind: Kind,
    /// Where the grounding lives.
    pub locator: Locator,
    /// Our observation of it (sense ②).
    pub snapshot: Snapshot,
    /// The source artifact's own provenance (sense ①).
    #[serde(skip_serializing_if = "Origin::is_empty")]
    #[serde(default)]
    pub origin: Origin,
}

/// One successful asynchronous Meta update, keyed by its Mailbox-derived Job
/// ID in [`Meta::updates`]. Re-executing a Job replaces the same entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetaUpdate {
    pub source: String,
    pub applied_at: String,
    pub value: serde_json::Value,
}

/// Node metadata. Captured facts only — no deterministically computed views.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Meta {
    /// Caller-supplied evidence descriptors. They are persisted verbatim so an
    /// Evidence Job can be retried after daemon restart without repeating the
    /// Add RPC. Interpretation and I/O never happen on the Add path.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub evidence_requests: Vec<String>,
    /// Successfully captured evidence. Empty while capture is pending, when no
    /// evidence was requested, or when a durable rejected Job result explains
    /// why the request could not be interpreted.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<Evidence>,
    /// Node creation facts (sense ③), self-observed. No adder identity is
    /// recorded — it is unavailable and out of scope.
    pub created_at: String,
    pub cli: String,
    pub cli_version: String,
    /// Successful results produced by NodeAdded hooks. This contains results,
    /// not Job scheduling or retry state; all execution state remains in memory.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub updates: BTreeMap<String, MetaUpdate>,
}

/// A specification node: exactly one accepted sentence. Grounding may arrive
/// asynchronously after the node itself becomes visible.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Node {
    pub id: String,
    /// The raw sentence text — the source of truth.
    pub statement: String,
    /// The version of the language that accepted the sentence. Every row the
    /// store writes records it; the empty default is defensive robustness for
    /// rows created out of band. (Pre-0.2 data lives in the abandoned
    /// `contracts` collection and is never read — see `crate::arango`.)
    #[serde(default)]
    pub lang_version: String,
    pub meta: Meta,
}

impl Node {
    /// A one-line human summary. Deliberately does not surface any derived
    /// reading as a parse result to be confirmed — it is a convenience view.
    pub fn summary(&self) -> String {
        format!("{}  ({} evidence)", self.id, self.meta.evidence.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::snapshot::Anchor;

    fn sample_node() -> Node {
        Node {
            id: "test-id".to_string(),
            statement: "The pump shall stop.".to_string(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence_requests: vec![
                    r#"{"kind":"constitutive","locator":"src/pump.rs:10"}"#.into()
                ],
                evidence: vec![Evidence {
                    kind: Kind::Constitutive,
                    locator: Locator::File {
                        path: "src/pump.rs".to_string(),
                        line: Some(10),
                        col: None,
                    },
                    snapshot: Snapshot {
                        content: "fn stop() {}".to_string(),
                        content_hash: "deadbeef".to_string(),
                        bytes: 12,
                        captured_at: "2026-07-05T00:00:00Z".to_string(),
                        anchor: Anchor::Worktree,
                    },
                    origin: Origin::default(),
                }],
                created_at: "2026-07-05T00:00:00Z".to_string(),
                cli: "spec".to_string(),
                cli_version: "0.1.0".to_string(),
                updates: Default::default(),
            },
        }
    }

    #[test]
    fn round_trips_through_json_without_snapshot_bytes() {
        let node = sample_node();
        let json = serde_json::to_string_pretty(&node).unwrap();
        // The captured bytes are not persisted in the node — only the hash
        // pointer into the blob store.
        assert!(!json.contains("fn stop()"));
        assert!(json.contains("deadbeef"));

        let back: Node = serde_json::from_str(&json).unwrap();
        // Everything round-trips except the (blob-resident) snapshot content.
        assert_eq!(back.meta.evidence[0].snapshot.content, "");
        let mut expected = node.clone();
        expected.meta.evidence[0].snapshot.content = String::new();
        assert_eq!(expected, back);
    }

    #[test]
    fn empty_origin_is_omitted_from_json() {
        let node = sample_node();
        let json = serde_json::to_string(&node).unwrap();
        assert!(!json.contains("\"origin\""));
    }

    #[test]
    fn summary_counts_evidence() {
        assert!(sample_node().summary().contains("1 evidence"));
    }

    #[test]
    fn rows_without_lang_version_still_deserialize() {
        // Defensive: a row created out of band without `lang_version` (the
        // store itself always writes it) still deserializes, defaulting to empty.
        let mut json = serde_json::to_value(sample_node()).unwrap();
        json.as_object_mut().unwrap().remove("lang_version");
        let back: Node = serde_json::from_value(json).unwrap();
        assert_eq!(back.lang_version, "");
    }
}
