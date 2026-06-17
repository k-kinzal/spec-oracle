/// Query and analysis data structures
use super::{SpecNodeData, EdgeKind};

#[derive(Debug, Clone)]
pub struct ComplianceScore {
    pub score: f32,              // Overall compliance score 0.0-1.0
    pub keyword_overlap: f32,    // Semantic keyword similarity
    pub structural_match: f32,   // Structural pattern matching
    pub explanation: String,     // Human-readable explanation
}

#[derive(Debug, Clone)]
pub struct TestCoverage {
    pub total_testable: usize,
    pub with_tests: usize,
    pub coverage_ratio: f32,
    pub nodes_with_tests: Vec<SpecNodeData>,
    pub nodes_without_tests: Vec<SpecNodeData>,
}

#[derive(Debug, Clone)]
pub struct Contradiction {
    pub node_a: SpecNodeData,
    pub node_b: SpecNodeData,
    pub explanation: String,
}

#[derive(Debug, Clone)]
pub struct Omission {
    pub description: String,
    pub related_nodes: Vec<SpecNodeData>,
}

#[derive(Debug, Clone)]
pub struct LayerInconsistency {
    pub source: SpecNodeData,
    pub target: SpecNodeData,
    pub explanation: String,
}

#[derive(Debug, Clone)]
pub struct InterUniverseInconsistency {
    pub universe_a: String,
    pub universe_b: String,
    pub spec_a: SpecNodeData,
    pub spec_b: SpecNodeData,
    pub transform_path: Vec<String>,
    pub explanation: String,
}

