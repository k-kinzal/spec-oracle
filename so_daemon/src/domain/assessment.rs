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
    /// Sentence-level force-aware refinement.
    Refines {
        concrete: String,
        abstract_: String,
    },
    Equivalent,
    HardContradiction,
    AdvisoryTension,
    DescriptiveConflict,
    EnvelopeConflict,
    Independent,
    Unknown,
    /// Formula-projection facts are force/speech-act blind and never become
    /// specification topology directly.
    FormulaEntails {
        antecedent: String,
        consequence: String,
    },
    FormulaEquivalent,
    FormulaContradiction,
    FormulaUnknown,
    /// Standard A/G relation between the current semantic contracts projected
    /// by the endpoint specifications.
    ContractRefines {
        concrete: String,
        abstract_: String,
    },
    ContractEquivalent,
    ContractIncomparable,
    /// A proved `G_source ⇒ A_target` opportunity. It remains audit data until
    /// an explicit selection promotes it to GuaranteeDischarge topology.
    DischargeCandidate {
        source: String,
        target: String,
        relied_spec_id: String,
    },
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
