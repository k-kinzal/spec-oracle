/// Constraint: A symbolic representation of a membership condition
///
/// Represents a condition that an implementation must satisfy to be in the admissible set.
///
/// ## 2-Layer Structure (Phase A: Minimization)
/// Constraints don't have identifiers, so they have only:
/// - Layer 2: Proof Data (`formal`, `kind`) - used in formal proofs
/// - Layer 3: Metadata (`meta`) - description, pattern, source
///
/// CRITICAL: Proofs use `formal` field only. If `formal` is None, it must be extracted
/// from `meta.description` during proof preparation, but never accessed directly by Prover.
use serde::{Deserialize, Serialize};
use super::ConstraintMetadata;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Constraint {
    // Layer 2: Proof Data
    /// Formal representation (e.g., SMT-LIB, propositional logic)
    /// This is the PRIMARY representation used in proofs
    /// If None, extract from meta.description during proof preparation
    pub formal: Option<String>,

    /// Type of constraint (universal ∀, existential ∃, etc.)
    pub kind: ConstraintKind,

    // OLD FIELD (deprecated, for migration compatibility)
    /// Natural language description (DEPRECATED: use meta.description)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,

    /// Metadata (DEPRECATED: use meta)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<ConstraintMetadata>,

    // NEW FIELD (preferred)
    /// Layer 3: Metadata (description, pattern, source)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<ConstraintMetadata>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstraintKind {
    /// Universal constraint (∀): Must hold for all cases
    Universal,

    /// Existential constraint (∃): Must hold for at least one case
    Existential,

    /// Implication (→): If condition then consequence
    Implication,

    /// Equivalence (↔): Bidirectional implication
    Equivalence,
}
