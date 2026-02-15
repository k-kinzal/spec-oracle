/// Transform Function: Mappings between universes
///
/// f: Ui → Uj represents a transformation from one universe to another.
/// The most critical transforms are inverse mappings: f₀ᵢ⁻¹: Ui → U0
///
/// These are NOT just edge markers - they contain actual transformation logic.
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use super::{TransformId, TransformMetadata};
use crate::formal::universe::UniverseId;
use crate::formal::projection::{Observer, ArtifactBundleObserver, TraceObserver, FileSystemObserver, ArtifactKind};

/// Describes which kind of observer to instantiate for a projection strategy.
///
/// This is a serializable descriptor -- call `instantiate()` to create the
/// concrete `Box<dyn Observer>` at runtime.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ObserverKind {
    /// Observe from a static artifact bundle
    ArtifactBundle,

    /// Observe from a behavioral trace
    Trace {
        layer_name: String,
    },

    /// Observe directly from the file system
    FileSystem {
        base_path: String,
    },
}

impl ObserverKind {
    /// Create a concrete observer from this descriptor.
    ///
    /// The `artifact_kind` parameter specifies what kind of artifact the
    /// returned observer will produce.
    pub fn instantiate(&self, artifact_kind: ArtifactKind) -> Box<dyn Observer> {
        match self {
            ObserverKind::ArtifactBundle => {
                Box::new(ArtifactBundleObserver::new(artifact_kind))
            }
            ObserverKind::Trace { .. } => {
                Box::new(TraceObserver::new(artifact_kind))
            }
            ObserverKind::FileSystem { .. } => {
                Box::new(FileSystemObserver::new(artifact_kind))
            }
        }
    }
}

#[allow(deprecated)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransformFunction {
    /// Unique identifier for this transform
    pub id: TransformId,

    /// Source universe
    pub source_universe: UniverseId,

    /// Target universe
    pub target_universe: UniverseId,

    /// Human-readable description of this transformation
    pub description: String,

    /// The type of transformation
    pub kind: TransformKind,

    /// The actual transformation logic (strategy pattern)
    /// This is where we'll plug in different transformation implementations
    pub strategy: TransformStrategy,

    /// Metadata for extensibility
    pub metadata: TransformMetadata,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransformKind {
    /// Forward mapping: Ui → Uj (i < j, more concrete)
    Forward,

    /// Inverse mapping: Ui → U0 (critical for constructing root universe)
    Inverse,

    /// Parallel mapping: Ui → Uj (i, j > 0, different aspects)
    Parallel,
}

/// Projection-aware strategy for performing transformations.
///
/// Each variant carries an `ObserverKind` that describes how to observe the
/// root space before extraction. This replaces `TransformStrategy` by making
/// the observer explicit in every strategy.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProjectionStrategy {
    /// AST-based extraction (code -> spec)
    ASTExtraction {
        language: String,
        observer: ObserverKind,
        extractor_config: HashMap<String, String>,
    },

    /// NLP-based extraction (docs -> spec)
    NLPExtraction {
        model: String,
        observer: ObserverKind,
        prompt_template: String,
    },

    /// Formal verification extraction (TLA+/Alloy -> spec)
    FormalVerification {
        tool: String,
        observer: ObserverKind,
        verification_config: HashMap<String, String>,
    },

    /// Type system extraction (type definitions -> spec)
    TypeExtraction {
        type_system: String,
        observer: ObserverKind,
    },

    /// Manual mapping (user-defined, no observer needed)
    Manual {
        description: String,
    },
}

/// Strategy for performing transformations
///
/// Different transformation strategies based on the nature of the universes.
/// This is where the actual "how to transform" logic lives.
#[deprecated(note = "Use ProjectionStrategy instead, which includes observer configuration")]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TransformStrategy {
    /// Abstract syntax tree analysis (for code → spec)
    ASTAnalysis {
        language: String,
        extractor_config: HashMap<String, String>,
    },

    /// Natural language inference (for docs → spec)
    NLPInference {
        model: String,
        prompt_template: String,
    },

    /// Formal verification (for TLA+/Alloy → spec)
    FormalVerification {
        tool: String,
        verification_config: HashMap<String, String>,
    },

    /// Type system analysis (for type definitions → spec)
    TypeAnalysis {
        type_system: String,
    },

    /// Manual mapping (user-defined transformation)
    Manual {
        description: String,
    },

    /// Composed transformation (chain multiple strategies)
    Composed {
        strategies: Vec<Box<TransformStrategy>>,
    },
}

#[allow(deprecated)]
impl TransformFunction {
    /// Create an inverse mapping: Ui → U0
    pub fn inverse(
        source_universe: UniverseId,
        description: String,
        strategy: TransformStrategy,
    ) -> Self {
        let id = TransformId::inverse(&source_universe);
        Self {
            id,
            source_universe,
            target_universe: UniverseId::root(),
            description,
            kind: TransformKind::Inverse,
            strategy,
            metadata: TransformMetadata::new(),
        }
    }

    /// Create a transform from a ProjectionStrategy.
    ///
    /// Converts the projection strategy into the legacy TransformStrategy
    /// so that the rest of the system can operate unchanged during migration.
    #[allow(deprecated)]
    pub fn new_with_projection(
        source_universe: UniverseId,
        target_universe: UniverseId,
        description: String,
        kind: TransformKind,
        projection: ProjectionStrategy,
    ) -> Self {
        let strategy = match &projection {
            ProjectionStrategy::ASTExtraction { language, extractor_config, .. } => {
                TransformStrategy::ASTAnalysis {
                    language: language.clone(),
                    extractor_config: extractor_config.clone(),
                }
            }
            ProjectionStrategy::NLPExtraction { model, prompt_template, .. } => {
                TransformStrategy::NLPInference {
                    model: model.clone(),
                    prompt_template: prompt_template.clone(),
                }
            }
            ProjectionStrategy::FormalVerification { tool, verification_config, .. } => {
                TransformStrategy::FormalVerification {
                    tool: tool.clone(),
                    verification_config: verification_config.clone(),
                }
            }
            ProjectionStrategy::TypeExtraction { type_system, .. } => {
                TransformStrategy::TypeAnalysis {
                    type_system: type_system.clone(),
                }
            }
            ProjectionStrategy::Manual { description } => {
                TransformStrategy::Manual {
                    description: description.clone(),
                }
            }
        };

        let id = match kind {
            TransformKind::Inverse => TransformId::inverse(&source_universe),
            TransformKind::Forward | TransformKind::Parallel => {
                TransformId::forward(&source_universe, &target_universe)
            }
        };

        Self {
            id,
            source_universe,
            target_universe,
            description,
            kind,
            strategy,
            metadata: TransformMetadata::new(),
        }
    }

    /// Create a forward mapping: Ui → Uj
    pub fn forward(
        source_universe: UniverseId,
        target_universe: UniverseId,
        description: String,
        strategy: TransformStrategy,
    ) -> Self {
        let id = TransformId::forward(&source_universe, &target_universe);
        Self {
            id,
            source_universe,
            target_universe,
            description,
            kind: TransformKind::Forward,
            strategy,
            metadata: TransformMetadata::new(),
        }
    }
}
