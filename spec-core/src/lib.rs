pub mod graph;
pub mod store;
pub mod extract;
pub mod ai_semantic;
pub mod formal;

pub use graph::{NodeKind, EdgeKind, SpecGraph, SpecNodeData, SpecEdgeData};
pub use graph::{Contradiction, Omission, LayerInconsistency, InterUniverseInconsistency, TestCoverage, ComplianceScore};
pub use graph::{TemporalSnapshot, TemporalDiff, NodeHistory, HistoryEvent, ComplianceTrend, ComplianceDataPoint};
pub use store::{FileStore, DirectoryStore, Store};
pub use extract::{RustExtractor, ProtoExtractor, DocExtractor, ArchitectureExtractor, PHPTestExtractor, InferredSpecification, IngestionReport, EdgeSuggestion};
pub use ai_semantic::AISemantic;
// Re-export from formal module
pub use formal::{UDAFModel, Universe, Domain, AdmissibleSet, TransformFunction, TransformStrategy, Constraint, ConstraintKind, TransformKind};
pub use formal::{UniverseId, DomainId, SpecId, TransformId, IdError};
pub use formal::{MetadataKey, Metadata, UniverseMetadata, DomainMetadata, ConstraintMetadata, TransformMetadata};
pub use formal::{SpecSet, DomainSet};
pub use formal::{Proof, Property, ProofMethod, ProofStatus, ProofStep};
#[cfg(feature = "z3-solver")]
pub use formal::{Prover, UnderspecificationReport};
