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

/// Strategy for performing transformations
///
/// Different transformation strategies based on the nature of the universes.
/// This is where the actual "how to transform" logic lives.
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
