pub mod graph;
pub mod store;
pub mod extract;
pub mod ai_semantic;
pub mod udaf;
pub mod prover;

pub use graph::{NodeKind, EdgeKind, SpecGraph, SpecNodeData, SpecEdgeData};
pub use graph::{Contradiction, Omission, LayerInconsistency, InterUniverseInconsistency, TestCoverage, ComplianceScore};
pub use graph::{TemporalSnapshot, TemporalDiff, NodeHistory, HistoryEvent, ComplianceTrend, ComplianceDataPoint};
pub use store::{FileStore, DirectoryStore};
pub use extract::{RustExtractor, ProtoExtractor, DocExtractor, ArchitectureExtractor, PHPTestExtractor, InferredSpecification, IngestionReport, EdgeSuggestion};
pub use ai_semantic::AISemantic;
pub use udaf::{UDAFModel, Universe, Domain, AdmissibleSet, TransformFunction, TransformStrategy, Constraint, ConstraintKind, TransformKind};
pub use prover::{Prover, Proof, Property, ProofMethod, ProofStatus, ProofStep};
