/// Edge data structures for specification graph
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EdgeKind {
    Refines,
    DependsOn,
    Contradicts,
    DerivesFrom,
    Synonym,
    Composes,
    Formalizes,  // Target is a more formal version of source
    Transform,   // Function f: maps spec from source universe to target universe
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecEdgeData {
    pub id: String,
    pub kind: EdgeKind,
    pub metadata: HashMap<String, String>,
    #[serde(default)]
    pub created_at: i64,
}

/// Edge with source/target node IDs (for serialization)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Edge {
    pub source: String,
    pub target: String,
    #[serde(flatten)]
    pub data: SpecEdgeData,
}
