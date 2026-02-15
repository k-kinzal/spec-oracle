/// Admissible Set: The set of implementations allowed by a specification
///
/// A represents "what is correct" - all implementations that satisfy the specification.
/// Contradiction detection: A1 ∩ A2 = ∅ (disjoint admissible sets)
///
/// Note: This is a symbolic representation. The actual admissible set is infinite
/// and cannot be enumerated. Instead, we represent it through constraints.
///
/// ## 3-Layer Structure (Phase A: Minimization)
/// - Layer 1: Identifier (`spec_id`)
/// - Layer 2: Proof Data (`proof_data`) - constraints, contradictions
/// - Layer 3: Metadata (`meta`) - organizational info

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use super::{SpecId, SpecSet};
use crate::formal::universe::UniverseId;
use crate::formal::constraint::Constraint;
use crate::formal::Metadata;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdmissibleSet {
    /// Layer 1: The specification that defines this admissible set
    pub spec_id: SpecId,

    // OLD FIELDS (deprecated, for migration compatibility)
    /// The universe this admissible set belongs to (DEPRECATED: use meta.universe_id)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub universe_id: Option<UniverseId>,

    /// Constraints that define membership (DEPRECATED: use proof_data.constraints)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constraints: Option<Vec<Constraint>>,

    /// Known contradictions (DEPRECATED: use proof_data.contradicts)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contradicts: Option<SpecSet>,

    /// Metadata for extensibility (DEPRECATED: use meta)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Metadata>,

    // NEW FIELDS (preferred)
    /// Layer 2: Proof-essential data (constraints, contradictions)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_data: Option<AdmissibleSetProofData>,

    /// Layer 3: Metadata (organizational info)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<AdmissibleSetMetadata>,
}

/// Layer 2: Proof-essential data for AdmissibleSet
///
/// Contains only the data needed for formal verification and proofs.
/// The Prover should only access this layer, never metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdmissibleSetProofData {
    /// Constraints that define membership in this set
    pub constraints: Vec<Constraint>,

    /// Pre-marked contradictions with other admissible sets
    pub contradicts: SpecSet,
}

/// Layer 3: Metadata for AdmissibleSet
///
/// Contains human-readable and organizational information.
/// NOT used in formal proofs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdmissibleSetMetadata {
    /// The universe this admissible set belongs to (organizational)
    pub universe_id: UniverseId,

    /// Extensible metadata
    #[serde(flatten)]
    pub extra: HashMap<String, String>,
}

impl AdmissibleSetProofData {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            contradicts: SpecSet::new(),
        }
    }

    /// Add a constraint to this admissible set
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Mark this admissible set as contradicting another
    pub fn mark_contradiction(&mut self, other_id: SpecId) {
        self.contradicts.insert(other_id);
    }
}

impl Default for AdmissibleSetProofData {
    fn default() -> Self {
        Self::new()
    }
}

impl AdmissibleSetMetadata {
    pub fn new(universe_id: UniverseId) -> Self {
        Self {
            universe_id,
            extra: HashMap::new(),
        }
    }
}

impl AdmissibleSet {
    pub fn new(spec_id: SpecId, universe_id: UniverseId) -> Self {
        Self {
            spec_id,
            // OLD fields (populated for compatibility)
            universe_id: Some(universe_id.clone()),
            constraints: Some(Vec::new()),
            contradicts: Some(SpecSet::new()),
            metadata: Some(Metadata::new()),
            // NEW fields (preferred)
            proof_data: Some(AdmissibleSetProofData::new()),
            meta: Some(AdmissibleSetMetadata::new(universe_id)),
        }
    }

    /// Add a constraint to this admissible set
    pub fn add_constraint(&mut self, constraint: Constraint) {
        // Update both old and new fields during migration
        if let Some(constraints) = &mut self.constraints {
            constraints.push(constraint.clone());
        }
        if let Some(proof_data) = &mut self.proof_data {
            proof_data.add_constraint(constraint);
        }
    }

    /// Mark this admissible set as contradicting another
    pub fn mark_contradiction(&mut self, other_id: SpecId) {
        // Update both old and new fields during migration
        if let Some(contradicts) = &mut self.contradicts {
            contradicts.insert(other_id.clone());
        }
        if let Some(proof_data) = &mut self.proof_data {
            proof_data.mark_contradiction(other_id);
        }
    }

    /// Get proof data (for Prover access)
    pub fn get_proof_data(&self) -> Option<&AdmissibleSetProofData> {
        self.proof_data.as_ref()
    }

    /// Get mutable proof data
    pub fn get_proof_data_mut(&mut self) -> Option<&mut AdmissibleSetProofData> {
        self.proof_data.as_mut()
    }

    /// Check if this admissible set is likely empty (unsatisfiable constraints)
    pub fn is_likely_empty(&self) -> bool {
        // Heuristic: check for obvious contradictions in constraints
        // e.g., "x >= 10" and "x <= 5"
        // TODO: Implement SMT solver integration for precise satisfiability check
        false  // Placeholder
    }
}
