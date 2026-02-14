pub mod graph;
pub mod store;
pub mod extract;
pub mod ai_semantic;

pub use graph::{NodeKind, EdgeKind, SpecGraph, SpecNodeData, SpecEdgeData};
pub use graph::{Contradiction, Omission, LayerInconsistency, InterUniverseInconsistency, TestCoverage, ComplianceScore};
pub use graph::{TemporalSnapshot, TemporalDiff, NodeHistory, HistoryEvent, ComplianceTrend, ComplianceDataPoint};
pub use store::FileStore;
pub use extract::{RustExtractor, InferredSpecification, IngestionReport, EdgeSuggestion};
pub use ai_semantic::AISemantic;
