pub mod store;
pub mod extract;
pub mod ai_semantic;
pub mod formal;
pub mod data;

// Storage layer
pub use store::{FileStore, DirectoryStore, Store};

// Extraction layer
pub use extract::{RustExtractor, ProtoExtractor, DocExtractor, ArchitectureExtractor, PHPTestExtractor, InferredSpecification, IngestionReport, EdgeSuggestion};

// AI semantic analysis
pub use ai_semantic::AISemantic;

// Data layer (pure data operations)
pub use data::{SpecRepository, GraphError};
pub use data::{NodeKind, EdgeKind, SpecNodeData, SpecEdgeData};
pub use data::{TestCoverage, ComplianceScore};
pub use data::{TemporalSnapshot, TemporalDiff, NodeHistory, HistoryEvent, ComplianceTrend, ComplianceDataPoint};

// Formal verification layer (UDA/f model)
pub use formal::{UDAFModel, Universe, Domain, AdmissibleSet, TransformFunction, TransformStrategy, Constraint, ConstraintKind, TransformKind};
pub use formal::{UniverseId, DomainId, SpecId, TransformId, IdError};
pub use formal::{MetadataKey, Metadata, UniverseMetadata, DomainMetadata, ConstraintMetadata, TransformMetadata};
pub use formal::{SpecSet, DomainSet};
pub use formal::{Proof, Property, ProofMethod, ProofStatus, ProofStep};
pub use formal::{ModelSync};

#[cfg(feature = "z3-solver")]
pub use formal::{Prover, UnderspecificationReport, Contradiction, Omission, LayerInconsistency, InterUniverseInconsistency};
