//! A derived view of one Specification Node under a versioned fitness policy.
//!
//! Authored Nodes and their relationship Edges remain immutable Ledger facts.
//! This module contains only the explainable output of selection: the score
//! contributed by current graph relationships and every reason a candidate was
//! excluded from the current specification set.

use super::{DerivedNode, Edge};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScoreContributionKind {
    ConstitutiveEvidence,
    DemonstrativeEvidence,
    TestimonialEvidence,
    AssertoricEvidence,
    CircumstantialEvidence,
    UnknownEvidence,
    CounterEvidence,
    GroundedSupport,
    InertSupport,
}

impl ScoreContributionKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ConstitutiveEvidence => "constitutive_evidence",
            Self::DemonstrativeEvidence => "demonstrative_evidence",
            Self::TestimonialEvidence => "testimonial_evidence",
            Self::AssertoricEvidence => "assertoric_evidence",
            Self::CircumstantialEvidence => "circumstantial_evidence",
            Self::UnknownEvidence => "unknown_evidence",
            Self::CounterEvidence => "counter_evidence",
            Self::GroundedSupport => "grounded_support",
            Self::InertSupport => "inert_support",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScoreContribution {
    pub kind: ScoreContributionKind,
    pub points: i32,
    pub edge_id: String,
    pub source_node_id: Option<String>,
    pub evidence_node_id: Option<String>,
    pub detail: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExclusionKind {
    InsufficientSupport,
    Counterevidence,
    Defeated,
    Superseded,
    Contradicted,
    EquivalentDuplicate,
    RefinementDominated,
    SelectionCycle,
}

impl ExclusionKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::InsufficientSupport => "insufficient_support",
            Self::Counterevidence => "counterevidence",
            Self::Defeated => "defeated",
            Self::Superseded => "superseded",
            Self::Contradicted => "contradicted",
            Self::EquivalentDuplicate => "equivalent_duplicate",
            Self::RefinementDominated => "refinement_dominated",
            Self::SelectionCycle => "selection_cycle",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectionExclusion {
    pub kind: ExclusionKind,
    pub edge_id: Option<String>,
    pub competing_node_id: Option<String>,
    pub detail: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectionView {
    pub policy_version: String,
    pub current: bool,
    pub support_score: i32,
    pub evidence_score: i32,
    pub relation_score: i32,
    pub supporting_edge_ids: Vec<String>,
    pub defeating_edge_ids: Vec<String>,
    pub superseding_edge_ids: Vec<String>,
    pub contributions: Vec<ScoreContribution>,
    pub exclusions: Vec<SelectionExclusion>,
}

impl Default for SelectionView {
    fn default() -> Self {
        Self {
            policy_version: String::new(),
            current: false,
            support_score: 0,
            evidence_score: 0,
            relation_score: 0,
            supporting_edge_ids: Vec::new(),
            defeating_edge_ids: Vec::new(),
            superseding_edge_ids: Vec::new(),
            contributions: Vec::new(),
            exclusions: Vec::new(),
        }
    }
}

impl SelectionView {
    pub fn current(&self) -> bool {
        self.current
    }

    pub fn sort_and_dedup(&mut self) {
        for ids in [
            &mut self.supporting_edge_ids,
            &mut self.defeating_edge_ids,
            &mut self.superseding_edge_ids,
        ] {
            ids.sort();
            ids.dedup();
        }
        self.contributions.sort_by(|left, right| {
            (
                left.kind.as_str(),
                left.edge_id.as_str(),
                left.source_node_id.as_deref(),
                left.evidence_node_id.as_deref(),
            )
                .cmp(&(
                    right.kind.as_str(),
                    right.edge_id.as_str(),
                    right.source_node_id.as_deref(),
                    right.evidence_node_id.as_deref(),
                ))
        });
        self.exclusions.sort_by(|left, right| {
            (
                left.kind.as_str(),
                left.edge_id.as_deref(),
                left.competing_node_id.as_deref(),
            )
                .cmp(&(
                    right.kind.as_str(),
                    right.edge_id.as_deref(),
                    right.competing_node_id.as_deref(),
                ))
        });
    }
}

/// The current graph population needed by the pure fitness derivation.
/// Stores collect the complete semantic-competition and incoming-selection
/// dependency closure plus its direct Evidence inputs; policy and weights stay
/// outside storage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SelectionPopulation {
    pub relation_edges: Vec<Edge>,
    pub evidence_edges: Vec<Edge>,
    pub evidence_nodes: Vec<DerivedNode>,
}
