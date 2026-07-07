//! A derived relationship between two specification nodes.
//!
//! Edges are not yet produced — the model is all vertices today. This type
//! exists so the graph *read* is graph-shaped ahead of edge derivation: the
//! store's edge seam and the `GetGraph` response already carry `Edge`s (an
//! empty list for now), so refinement/composition/contradiction edges drop in
//! behind the seam without a wire change or a shape change on the client.
//!
//! An edge is a computed view over the words of its endpoints, not an
//! irreducible ingest fact: it is derived by relating two nodes (see the
//! `so_lang::relate` engine), never written by `spec add`.

use serde::{Deserialize, Serialize};

/// The kind of relationship an edge asserts, grounded in the graph vocabulary:
/// one statement refining another, two composing, two in contradiction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    /// The source is a stronger statement that entails the target.
    Refines,
    /// The two statements combine into a joint contract.
    Composes,
    /// The two statements cannot both hold.
    Contradicts,
}

/// A directed edge between two specification nodes, addressed by their ids.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edge {
    pub id: String,
    /// The id of the source node.
    pub source: String,
    /// The id of the target node.
    pub target: String,
    pub kind: EdgeKind,
}
