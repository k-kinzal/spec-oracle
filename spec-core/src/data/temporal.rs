/// Temporal data structures for specification history and versioning
use super::{SpecNodeData, SpecEdgeData};

#[derive(Debug, Clone)]
pub struct TemporalSnapshot {
    pub timestamp: i64,
    pub nodes: Vec<SpecNodeData>,
    pub edges: Vec<SpecEdgeData>,
    pub node_count: usize,
    pub edge_count: usize,
}

#[derive(Debug, Clone)]
pub struct TemporalDiff {
    pub from_timestamp: i64,
    pub to_timestamp: i64,
    pub added_nodes: Vec<SpecNodeData>,
    pub removed_nodes: Vec<SpecNodeData>,
    pub modified_nodes: Vec<(SpecNodeData, SpecNodeData)>,  // (from, to)
    pub added_edges: Vec<SpecEdgeData>,
    pub removed_edges: Vec<SpecEdgeData>,
}

#[derive(Debug, Clone)]
pub struct HistoryEvent {
    pub timestamp: i64,
    pub event_type: String,  // "created", "modified", "edge_added"
    pub description: String,
}

#[derive(Debug, Clone)]
pub struct NodeHistory {
    pub node: SpecNodeData,
    pub events: Vec<HistoryEvent>,
}

#[derive(Debug, Clone)]
pub struct ComplianceDataPoint {
    pub timestamp: i64,
    pub score: f32,
}

#[derive(Debug, Clone)]
pub struct ComplianceTrend {
    pub node: SpecNodeData,
    pub data_points: Vec<ComplianceDataPoint>,
    pub trend_direction: String,  // "improving", "degrading", "stable", "unknown"
}
