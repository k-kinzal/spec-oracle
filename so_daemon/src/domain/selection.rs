//! A derived view of one Specification Node under a versioned fitness policy.
//!
//! Authored Nodes and their mechanically derived Edges remain Ledger facts.
//! This module contains only the explainable output of selection: current
//! Evidence fitness and every semantic-competition reason a candidate was
//! excluded from the current specification set.

use super::{DerivedNode, Edge, Node};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScoreContributionKind {
    StructuralSupport,
    RealizationSupport,
    ConflictPressure,
    ConstitutiveEvidence,
    DemonstrativeEvidence,
    TestimonialEvidence,
    AssertoricEvidence,
    CircumstantialEvidence,
    UnknownEvidence,
    CounterEvidence,
}

impl ScoreContributionKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::StructuralSupport => "structural_support",
            Self::RealizationSupport => "realization_support",
            Self::ConflictPressure => "conflict_pressure",
            Self::ConstitutiveEvidence => "constitutive_evidence",
            Self::DemonstrativeEvidence => "demonstrative_evidence",
            Self::TestimonialEvidence => "testimonial_evidence",
            Self::AssertoricEvidence => "assertoric_evidence",
            Self::CircumstantialEvidence => "circumstantial_evidence",
            Self::UnknownEvidence => "unknown_evidence",
            Self::CounterEvidence => "counter_evidence",
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
    /// Complete Evidence path in source-to-target order. Structural
    /// contributions leave this empty and continue to use `edge_id`.
    pub path_edge_ids: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExclusionKind {
    InsufficientSupport,
    Counterevidence,
    Contradicted,
    EquivalentDuplicate,
    IncompleteGraph,
    EvidenceUnavailable,
}

impl ExclusionKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::InsufficientSupport => "insufficient_support",
            Self::Counterevidence => "counterevidence",
            Self::Contradicted => "contradicted",
            Self::EquivalentDuplicate => "equivalent_duplicate",
            Self::IncompleteGraph => "incomplete_graph",
            Self::EvidenceUnavailable => "evidence_unavailable",
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum EvaluationState {
    Current,
    Receded,
    #[default]
    Unknown,
}

impl EvaluationState {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Current => "current",
            Self::Receded => "receded",
            Self::Unknown => "unknown",
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
    pub evaluation_state: EvaluationState,
    pub support_score: i32,
    pub structural_score: i32,
    pub evidence_score: i32,
    pub relation_score: i32,
    pub conflict_pressure: i32,
    pub contributions: Vec<ScoreContribution>,
    pub exclusions: Vec<SelectionExclusion>,
}

impl Default for SelectionView {
    fn default() -> Self {
        Self {
            policy_version: String::new(),
            current: false,
            evaluation_state: EvaluationState::Unknown,
            support_score: 0,
            structural_score: 0,
            evidence_score: 0,
            relation_score: 0,
            conflict_pressure: 0,
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
/// Stores collect the complete current typed support/conflict component plus
/// its authored Specifications and direct Evidence inputs. The policy derives
/// support clauses from these existing Edges without persisting another Edge.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SelectionPopulation {
    pub nodes: Vec<Node>,
    pub relation_edges: Vec<Edge>,
    pub operational_nodes: Vec<DerivedNode>,
    pub evidence_edges: Vec<Edge>,
    pub evidence_nodes: Vec<DerivedNode>,
}
