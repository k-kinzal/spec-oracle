/// Universe: The space in which specifications are defined
///
/// A universe represents a complete space of possible specifications at a
/// particular level of formality or abstraction.
///
/// - U0: Root specification (constructed from inverse mappings, not written directly)
/// - U1-UN: Projection universes (written by users, e.g., natural language, TLA+, code)
use serde::{Deserialize, Serialize};
use super::UniverseId;
use super::UniverseMetadata;
use crate::formal::{SpecSet, IdError};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Universe {
    /// Unique identifier for this universe (e.g., "U0", "U1", "U2")
    pub id: UniverseId,

    /// Human-readable name (e.g., "Natural Language Requirements", "TLA+ Formal Spec", "Rust Implementation")
    pub name: String,

    /// Description of what this universe represents
    pub description: String,

    /// Specifications that belong to this universe
    pub specifications: SpecSet,

    /// Metadata for extensibility
    pub metadata: UniverseMetadata,
}

impl Universe {
    /// Create U0 (root universe) - constructed from inverse mappings
    pub fn root() -> Self {
        Self {
            id: UniverseId::root(),
            name: "Root Specification".to_string(),
            description: "The foundational universe constructed from inverse mappings of all projection universes. This represents the 'rough projection of the undefinable root specification'.".to_string(),
            specifications: SpecSet::new(),
            metadata: UniverseMetadata::new(),
        }
    }

    /// Create a projection universe (U1-UN)
    ///
    /// Returns Err if layer is 0 (use root() instead)
    pub fn projection(layer: u8, name: String, description: String) -> Result<Self, IdError> {
        let id = UniverseId::projection(layer)?;
        Ok(Self {
            id,
            name,
            description,
            specifications: SpecSet::new(),
            metadata: UniverseMetadata::new(),
        })
    }

    /// Get the layer number from the universe ID
    pub fn layer(&self) -> u8 {
        self.id.layer()
    }
}
