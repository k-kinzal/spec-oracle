//! Content-addressed graph nodes derived from an authored specification.
//!
//! Unlike [`crate::domain::Node`], these vertices are not authored sentences.
//! They make grounding and the two sides of the ingest assume-guarantee view
//! explicit topology. Their identities are derived from their content so two
//! specifications that refer to the same value share one vertex.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::domain::{Anchor, Evidence, VertexKind};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DerivedNode {
    Evidence {
        id: String,
        evidence: Evidence,
    },
    Assumption {
        id: String,
        expression: String,
        /// Canonical symbolic formula. Empty on legacy/trivial ingest
        /// projections whose human expression is already complete (`Top`).
        #[serde(default, skip_serializing_if = "String::is_empty")]
        formula_json: String,
        derivation_version: String,
    },
    Guarantee {
        id: String,
        expression: String,
        force: String,
        derivation_version: String,
    },
}

impl DerivedNode {
    /// Build a captured-evidence vertex. Per-capture timestamps remain in the
    /// specification's `meta.evidence`; the shared graph vertex is the stable
    /// grounding value (kind, locator, bytes/hash, anchor, and provenance).
    pub fn evidence(mut evidence: Evidence) -> Self {
        evidence.snapshot.captured_at.clear();
        if let Anchor::Web { retrieved_at, .. } = &mut evidence.snapshot.anchor {
            retrieved_at.clear();
        }
        let id = content_id(
            "evidence",
            &serde_json::to_vec(&evidence).expect("evidence identity serializes"),
        );
        Self::Evidence { id, evidence }
    }

    pub fn assumption(expression: &str, derivation_version: &str) -> Self {
        let id = content_id(
            "assumption",
            &serde_json::to_vec(&(expression, derivation_version))
                .expect("assumption identity serializes"),
        );
        Self::Assumption {
            id,
            expression: expression.to_string(),
            formula_json: String::new(),
            derivation_version: derivation_version.to_string(),
        }
    }

    pub fn assumption_formula(
        expression: &str,
        formula_json: &str,
        derivation_version: &str,
    ) -> Self {
        let id = content_id(
            "assumption",
            &serde_json::to_vec(&(expression, formula_json, derivation_version))
                .expect("assumption identity serializes"),
        );
        Self::Assumption {
            id,
            expression: expression.to_string(),
            formula_json: formula_json.to_string(),
            derivation_version: derivation_version.to_string(),
        }
    }

    pub fn guarantee(expression: &str, force: &str, derivation_version: &str) -> Self {
        let id = content_id(
            "guarantee",
            &serde_json::to_vec(&(expression, force, derivation_version))
                .expect("guarantee identity serializes"),
        );
        Self::Guarantee {
            id,
            expression: expression.to_string(),
            force: force.to_string(),
            derivation_version: derivation_version.to_string(),
        }
    }

    pub fn id(&self) -> &str {
        match self {
            Self::Evidence { id, .. }
            | Self::Assumption { id, .. }
            | Self::Guarantee { id, .. } => id,
        }
    }

    pub fn vertex_kind(&self) -> VertexKind {
        match self {
            Self::Evidence { .. } => VertexKind::Evidence,
            Self::Assumption { .. } => VertexKind::Assumption,
            Self::Guarantee { .. } => VertexKind::Guarantee,
        }
    }
}

fn content_id(namespace: &str, content: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(namespace.as_bytes());
    hasher.update([0]);
    hasher.update(content);
    format!("{namespace}-{:x}", hasher.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Anchor, Kind, Locator, Origin, Snapshot};

    fn evidence(captured_at: &str) -> Evidence {
        Evidence {
            kind: Kind::Assertoric,
            locator: Locator::File {
                path: "src/lib.rs".into(),
                line: Some(1),
                col: None,
            },
            snapshot: Snapshot {
                content: String::new(),
                content_hash: "abc".into(),
                bytes: 3,
                captured_at: captured_at.into(),
                anchor: Anchor::Worktree,
            },
            origin: Origin::default(),
        }
    }

    #[test]
    fn equal_derived_content_reuses_one_identity() {
        assert_eq!(
            DerivedNode::assumption("⊤", "v1").id(),
            DerivedNode::assumption("⊤", "v1").id()
        );
        assert_eq!(
            DerivedNode::guarantee("The pump shall stop.", "binding", "v1").id(),
            DerivedNode::guarantee("The pump shall stop.", "binding", "v1").id()
        );
        assert_eq!(
            DerivedNode::evidence(evidence("t1")),
            DerivedNode::evidence(evidence("t2")),
            "recapturing the same bytes at the same locator reuses the evidence vertex"
        );
    }

    #[test]
    fn node_kinds_have_disjoint_identity_namespaces() {
        assert_ne!(
            DerivedNode::assumption("⊤", "v1").id(),
            DerivedNode::guarantee("⊤", "", "v1").id()
        );
    }
}
