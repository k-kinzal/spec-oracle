//! A checked binary connection in the one specification graph.
//!
//! An Edge says exactly one bounded thing. `MentionsTerm` records lexical
//! incidence. Future semantic kinds require their own graph-side establishment
//! rules. A candidate, `Unknown`, or an unsearched pair is not topology.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VertexKind {
    Specification,
    Term,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    /// A specification contains one occurrence of a normalized term form.
    MentionsTerm,
}

/// A stable pointer into the constrained sentence structure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextAnchor {
    /// JSON-pointer-like path in the serialized sentence AST.
    pub selector: String,
    /// Canonical text at that path. Raw specification words remain authority.
    pub text: String,
    /// Grammatical role such as `subject`, `object`, or `definition_term`.
    pub role: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Derivation {
    pub method: String,
    pub version: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edge {
    pub id: String,
    pub source: String,
    pub source_kind: VertexKind,
    pub target: String,
    pub target_kind: VertexKind,
    pub kind: EdgeKind,
    pub source_anchor: Option<TextAnchor>,
    pub target_anchor: Option<TextAnchor>,
    /// Specifications, beyond the endpoints, that make this connection
    /// checkable. Empty when the endpoints and anchored term incidence are the
    /// complete basis.
    pub basis_spec_ids: Vec<String>,
    pub derivation: Derivation,
    pub recorded_at: String,
}
