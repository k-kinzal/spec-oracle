/// Data layer: Pure data persistence for UAD/f model
///
/// This module provides data structures and operations for persisting
/// the specification graph WITHOUT formal verification logic.
///
/// Architectural principle: This layer is PURELY for data operations.
/// - CRUD operations on nodes and edges
/// - Graph queries (search, trace, relationships)
/// - Temporal operations (versioning, history, diff)
/// - Serialization/deserialization
///
/// NO formal verification logic belongs here. Formal verification is
/// the responsibility of the formal:: module (UDAFModel, Prover, etc.).
pub mod node;
pub mod edge;
pub mod temporal;
pub mod query;
pub mod repository;

// Re-export key types for convenience
pub use node::{SpecNodeData, NodeKind};
pub use edge::{SpecEdgeData, EdgeKind, Edge};
pub use temporal::{
    TemporalSnapshot,
    TemporalDiff,
    NodeHistory,
    HistoryEvent,
    ComplianceDataPoint,
    ComplianceTrend,
};
pub use query::{
    ComplianceScore, TestCoverage, Contradiction, Omission,
    LayerInconsistency, InterUniverseInconsistency
};
pub use repository::SpecRepository;

/// Graph errors
#[derive(Debug, thiserror::Error)]
pub enum GraphError {
    #[error("Node not found: {0}")]
    NodeNotFound(String),
}
