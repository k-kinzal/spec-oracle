/// Domain: The region that a specification actually covers
///
/// D represents "what this specification is about" - the subset of the universe
/// that the specification intends to govern.
///
/// Gap detection: D \ D_S (intended domain minus actually specified domain)
///
/// ## 3-Layer Structure (Phase A: Minimization)
/// - Layer 1: Identifier (`id`)
/// - Layer 2: Proof Data (`proof_data`) - formal domain boundaries, coverage tracking
/// - Layer 3: Metadata (`meta`) - human-readable info, organizational structure

use serde::{Deserialize, Serialize};
use super::{DomainId, DomainMetadata, DomainSet};
use crate::formal::universe::UniverseId;
use crate::formal::constraint::Constraint;
use crate::formal::{SpecSet, MetadataKey};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Domain {
    /// Layer 1: Unique identifier for this domain
    pub id: DomainId,

    // OLD FIELDS (deprecated, for migration compatibility)
    /// Human-readable name (DEPRECATED: use meta.name)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,

    /// What this domain covers (DEPRECATED: use meta.description)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,

    /// The universe this domain belongs to (DEPRECATED: use meta.universe_id)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub universe_id: Option<UniverseId>,

    /// Specifications that cover this domain (DEPRECATED: use proof_data.covered_by)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub covered_by: Option<SpecSet>,

    /// Sub-domains (DEPRECATED: use meta.subdomains)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subdomains: Option<DomainSet>,

    /// Metadata for extensibility (DEPRECATED: use meta)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<DomainMetadata>,

    // NEW FIELDS (preferred)
    /// Layer 2: Proof-essential data (constraints, coverage)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_data: Option<DomainProofData>,

    /// Layer 3: Metadata (name, description, organizational structure)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<DomainMetadata>,
}

/// Layer 2: Proof-essential data for Domain
///
/// Contains only the data needed for formal verification and proofs.
/// The Prover should only access this layer, never metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DomainProofData {
    /// Formal domain boundary constraints (NEW: for completeness proofs)
    /// When empty: Domain is not formalized (graceful degradation)
    /// When present: Enables formal proofs about domain coverage (D ⊆ D_S)
    pub constraints: Vec<Constraint>,

    /// Specifications that cover this domain (for completeness checking)
    pub covered_by: SpecSet,
}

impl DomainProofData {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            covered_by: SpecSet::new(),
        }
    }

    /// Add a formal constraint to the domain boundary
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Check if domain is formalized (has constraints)
    pub fn is_formalized(&self) -> bool {
        !self.constraints.is_empty()
    }
}

impl Default for DomainProofData {
    fn default() -> Self {
        Self::new()
    }
}

impl Domain {
    /// Create a new domain with generated ID (NEW: uses 3-layer structure)
    pub fn new(name: String, description: String, universe_id: UniverseId) -> Self {
        let mut meta = DomainMetadata::new();
        meta.insert(MetadataKey::Custom("name".to_string()), name.clone());
        meta.insert(MetadataKey::Custom("description".to_string()), description.clone());
        meta.insert(MetadataKey::Custom("universe_id".to_string()), universe_id.as_str().to_string());

        Self {
            id: DomainId::new(),
            // OLD fields (populated for compatibility)
            name: Some(name),
            description: Some(description),
            universe_id: Some(universe_id),
            covered_by: Some(SpecSet::new()),
            subdomains: Some(DomainSet::new()),
            metadata: Some(DomainMetadata::new()),
            // NEW fields (preferred)
            proof_data: Some(DomainProofData::new()),
            meta: Some(meta),
        }
    }

    /// Create a domain with specific ID (for loading from storage)
    pub fn with_id(id: DomainId, name: String, description: String, universe_id: UniverseId) -> Self {
        let mut meta = DomainMetadata::new();
        meta.insert(MetadataKey::Custom("name".to_string()), name.clone());
        meta.insert(MetadataKey::Custom("description".to_string()), description.clone());
        meta.insert(MetadataKey::Custom("universe_id".to_string()), universe_id.as_str().to_string());

        Self {
            id,
            // OLD fields (populated for compatibility)
            name: Some(name),
            description: Some(description),
            universe_id: Some(universe_id),
            covered_by: Some(SpecSet::new()),
            subdomains: Some(DomainSet::new()),
            metadata: Some(DomainMetadata::new()),
            // NEW fields (preferred)
            proof_data: Some(DomainProofData::new()),
            meta: Some(meta),
        }
    }

    /// Add a formal constraint to the domain boundary
    pub fn add_constraint(&mut self, constraint: Constraint) {
        if let Some(proof_data) = &mut self.proof_data {
            proof_data.add_constraint(constraint);
        }
    }

    /// Get proof data (for Prover access)
    pub fn get_proof_data(&self) -> Option<&DomainProofData> {
        self.proof_data.as_ref()
    }

    /// Get mutable proof data
    pub fn get_proof_data_mut(&mut self) -> Option<&mut DomainProofData> {
        self.proof_data.as_mut()
    }

    /// Check if this domain has any coverage gaps
    /// Tries new field first, falls back to old field
    pub fn has_gaps(&self) -> bool {
        if let Some(proof_data) = &self.proof_data {
            proof_data.covered_by.is_empty()
        } else if let Some(covered_by) = &self.covered_by {
            covered_by.is_empty()
        } else {
            true
        }
    }
}
