/// Query and analysis data structures
use super::SpecNodeData;

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
