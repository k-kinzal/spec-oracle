/// Node data structures for specification graph
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NodeKind {
    Assertion,
    Constraint,
    Scenario,
    Definition,
    Domain,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SpecNodeData {
    pub id: String,
    pub content: String,
    pub kind: NodeKind,
    pub metadata: HashMap<String, String>,
    #[serde(default)]
    pub created_at: i64,
    #[serde(default)]
    pub modified_at: i64,
    #[serde(default)]
    pub formality_layer: u8,  // 0=natural, 1=structured, 2=formal, 3=executable
}
