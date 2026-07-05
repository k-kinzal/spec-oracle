//! The persisted node: an assume-guarantee contract that is also a grounded claim.
//!
//! A node carries two orthogonal layers:
//!   * the **logical** layer — the contract `(assumption ⇒ guarantee)` projected
//!     from the constrained-NL `statement` by the language crate, which remains
//!     the source of truth;
//!   * the **epistemic** layer — the `meta.evidence` grounding the claim.
//!
//! `meta` holds only facts that are irreducible at ingest: each piece of
//! evidence with its snapshot (sense ②) and origin (sense ①), plus the node's
//! own creation facts (sense ③). Everything derivable — the subject, the
//! strength, the conformance state — is a computed *view*, never stored here.

use serde::{Deserialize, Serialize};

use so_lang::grammar::{Assumption, Guarantee};

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

/// Node metadata. Irreducible-at-ingest facts only — no computed views.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Meta {
    pub evidence: Vec<Evidence>,
    /// Node creation facts (sense ③), self-observed. No adder identity is
    /// recorded — it is unavailable and out of scope.
    pub created_at: String,
    pub cli: String,
    pub cli_version: String,
}

/// A specification node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Node {
    pub id: String,
    /// The constrained-NL statement — the source of truth.
    pub statement: String,
    /// Projected from `statement` by the grammar (`⊤` when ubiquitous).
    pub assumption: Assumption,
    /// Projected from `statement` by the grammar.
    pub guarantee: Guarantee,
    pub meta: Meta,
}

impl Node {
    /// A one-line human summary. Deliberately does not surface the A/G split as a
    /// parse result to be confirmed — it is a convenience view only.
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
            assumption: Assumption::Top,
            guarantee: Guarantee {
                subject: "pump".to_string(),
                response: "stop".to_string(),
            },
            meta: Meta {
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
}
