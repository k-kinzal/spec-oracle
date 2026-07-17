//! Content-addressed graph nodes derived from an authored specification.
//!
//! Unlike [`crate::domain::Node`], these vertices are not authored sentences.
//! They make grounding, contract sides, and semantic contracts explicit
//! topology. Their identities are derived from their content so two
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
        #[serde(default, skip_serializing_if = "String::is_empty")]
        formula_json: String,
        derivation_version: String,
    },
    Contract {
        id: String,
        assumption_json: String,
        guarantee_json: String,
        interface_json: String,
        /// `formed`, `composition`, `quotient`, or `merge`.
        operation: String,
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
        Self::guarantee_formula(expression, force, "", derivation_version)
    }

    pub fn guarantee_formula(
        expression: &str,
        force: &str,
        formula_json: &str,
        derivation_version: &str,
    ) -> Self {
        let id = content_id(
            "guarantee",
            &serde_json::to_vec(&(expression, force, formula_json, derivation_version))
                .expect("guarantee identity serializes"),
        );
        Self::Guarantee {
            id,
            expression: expression.to_string(),
            force: force.to_string(),
            formula_json: formula_json.to_string(),
            derivation_version: derivation_version.to_string(),
        }
    }

    pub fn contract(
        contract: &so_reason::contract::Contract,
        operation: &str,
        derivation_version: &str,
    ) -> Self {
        let assumption_json =
            serde_json::to_string(&contract.assumption).expect("contract assumption serializes");
        let guarantee_json =
            serde_json::to_string(&contract.guarantee).expect("contract guarantee serializes");
        let interface_json =
            serde_json::to_string(&contract.interface()).expect("contract interface serializes");
        let id = content_id(
            "contract",
            &serde_json::to_vec(&(
                &assumption_json,
                &guarantee_json,
                &interface_json,
                operation,
                derivation_version,
            ))
            .expect("contract identity serializes"),
        );
        Self::Contract {
            id,
            assumption_json,
            guarantee_json,
            interface_json,
            operation: operation.to_string(),
            derivation_version: derivation_version.to_string(),
        }
    }

    pub fn semantic_contract(&self) -> Option<so_reason::contract::Contract> {
        let Self::Contract {
            assumption_json,
            guarantee_json,
            ..
        } = self
        else {
            return None;
        };
        Some(so_reason::contract::Contract::new(
            serde_json::from_str(assumption_json).ok()?,
            serde_json::from_str(guarantee_json).ok()?,
        ))
    }

    pub fn id(&self) -> &str {
        match self {
            Self::Evidence { id, .. }
            | Self::Assumption { id, .. }
            | Self::Guarantee { id, .. }
            | Self::Contract { id, .. } => id,
        }
    }

    pub fn vertex_kind(&self) -> VertexKind {
        match self {
            Self::Evidence { .. } => VertexKind::Evidence,
            Self::Assumption { .. } => VertexKind::Assumption,
            Self::Guarantee { .. } => VertexKind::Guarantee,
            Self::Contract { .. } => VertexKind::Contract,
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
