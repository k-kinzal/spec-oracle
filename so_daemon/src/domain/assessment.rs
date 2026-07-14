//! Append-only audit record for one attempted specification-pair assessment.
//!
//! This is deliberately not an Edge: `Unknown` and `Independent` are facts
//! about what one versioned procedure could establish, not graph topology.
//! Recording the attempt separately distinguishes them from an unsearched pair
//! without giving Edge absence a negative meaning.

use serde::{Deserialize, Serialize};

use super::Derivation;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AssessmentOutcome {
    Refines { concrete: String, abstract_: String },
    Equivalent,
    HardContradiction,
    AdvisoryTension,
    DescriptiveConflict,
    EnvelopeConflict,
    Independent,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelationAssessment {
    pub id: String,
    /// Canonically ordered endpoint ids. Semantic direction, when any, lives
    /// in [`AssessmentOutcome::Refines`].
    pub left: String,
    pub right: String,
    /// How this pair entered the assessment frontier.
    pub candidate_derivation: Derivation,
    /// Which graph-facing judgment rules produced `outcome`.
    pub semantic_derivation: Derivation,
    pub outcome: AssessmentOutcome,
    pub recorded_at: String,
}
