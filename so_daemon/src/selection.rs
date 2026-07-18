//! Explicit selection judgments and the versioned fitness/current-set policy.
//!
//! Semantic relationships remain the output of `so-reason`. This module owns
//! independently asserted Supports, Defeats, and Supersedes Edges and the pure
//! selection projection over current Ledger relationships. Storage supplies a
//! complete competition components; every score contribution and exclusion
//! stays visible.

use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

use crate::domain::{
    Derivation, DerivedNode, Edge, EdgeFamily, EdgeKind, ExclusionKind, Kind, Node,
    ScoreContribution, ScoreContributionKind, SelectionExclusion, SelectionPopulation,
    SelectionView,
};
use crate::store::{GraphStore, StoreError};

pub const DERIVATION_METHOD: &str = "so-daemon.selection.explicit";
pub const DERIVATION_VERSION: &str = "selection/explicit-v1";
pub const FITNESS_POLICY_VERSION: &str = "selection/fitness-v4";

const MIN_CURRENT_SCORE: i32 = 1;
const MAX_EVIDENCE_SOURCES_PER_POLARITY: usize = 4;
const MAX_GROUNDED_SUPPORTERS: usize = 4;
const MAX_POINTS_PER_SUPPORTER: i32 = 4;

pub fn is_fitness_relation(kind: EdgeKind) -> bool {
    matches!(
        kind,
        EdgeKind::Supports
            | EdgeKind::Defeats
            | EdgeKind::Supersedes
            | EdgeKind::Refines
            | EdgeKind::Equivalent
            | EdgeKind::HardContradiction
            | EdgeKind::AdvisoryTension
            | EdgeKind::DescriptiveConflict
            | EdgeKind::EnvelopeConflict
    )
}

pub fn derivation() -> Derivation {
    Derivation {
        method: DERIVATION_METHOD.to_string(),
        version: DERIVATION_VERSION.to_string(),
    }
}

/// Return the exact Evidence vertices in the Node's convenient current capture
/// view. `None` is reserved for legacy/manually constructed rows that have no
/// capture-state marker; stores may fall back to Ledger adjacency for those.
/// `Some(empty)` is authoritative (a clear or rejected capture) and therefore
/// makes every historical GroundedBy Edge inert for fitness.
pub(crate) fn current_evidence_node_ids(node: &Node) -> Option<BTreeSet<String>> {
    let authoritative = !node.meta.evidence_request_generation.is_empty()
        || !node.meta.evidence.is_empty()
        || node
            .meta
            .updates
            .values()
            .any(|update| update.source == crate::evidence_capture::PLUGIN_NAME);
    authoritative.then(|| {
        node.meta
            .evidence
            .iter()
            .cloned()
            .map(DerivedNode::evidence)
            .map(|node| node.id().to_string())
            .collect()
    })
}

#[derive(Debug, Clone, Default)]
struct ScoreSummary {
    evidence_score: i32,
    relation_score: i32,
    positive_evidence_sources: usize,
    contributions: Vec<ScoreContribution>,
}

impl ScoreSummary {
    fn total(&self) -> i32 {
        self.evidence_score + self.relation_score
    }
}

struct EvidenceSignal<'a> {
    edge: &'a Edge,
    evidence_node_id: &'a str,
    evidence: &'a crate::domain::Evidence,
}

/// Derive a current-set view from current-version Ledger relationships.
///
/// The v1 policy deliberately has no authored-node baseline: admission creates
/// a candidate, not a fact. Direct captured Evidence supplies bounded points;
/// a unique supporter can transfer at most four points and only when it has
/// positive direct Evidence of its own. Consequently an ungrounded Supports
/// cycle cannot bootstrap itself into the current set.
pub fn derive_views(
    node_ids: &[String],
    population: &SelectionPopulation,
) -> BTreeMap<String, SelectionView> {
    let requested: BTreeSet<&str> = node_ids.iter().map(String::as_str).collect();
    let evidence_by_id: BTreeMap<&str, &DerivedNode> = population
        .evidence_nodes
        .iter()
        .map(|node| (node.id(), node))
        .collect();
    let mut latest_by_locator: BTreeMap<(String, String), EvidenceSignal<'_>> = BTreeMap::new();
    let mut scored_ids: BTreeSet<String> = node_ids.iter().cloned().collect();

    for edge in &population.relation_edges {
        scored_ids.insert(edge.source.clone());
        scored_ids.insert(edge.target.clone());
    }
    for edge in &population.evidence_edges {
        scored_ids.insert(edge.source.clone());
        let Some(evidence_node) = evidence_by_id.get(edge.target.as_str()).copied() else {
            continue;
        };
        let DerivedNode::Evidence { evidence, .. } = evidence_node else {
            continue;
        };
        let key = (edge.source.clone(), evidence.locator.render());
        let candidate = EvidenceSignal {
            edge,
            evidence_node_id: edge.target.as_str(),
            evidence,
        };
        let replace = latest_by_locator.get(&key).is_none_or(|existing| {
            (
                candidate.edge.recorded_at.as_str(),
                candidate.edge.id.as_str(),
            ) > (
                existing.edge.recorded_at.as_str(),
                existing.edge.id.as_str(),
            )
        });
        if replace {
            latest_by_locator.insert(key, candidate);
        }
    }

    let mut signals_by_node: BTreeMap<String, Vec<EvidenceSignal<'_>>> = BTreeMap::new();
    for ((node_id, _), signal) in latest_by_locator {
        signals_by_node.entry(node_id).or_default().push(signal);
    }

    let mut scores: BTreeMap<String, ScoreSummary> = scored_ids
        .iter()
        .cloned()
        .map(|id| (id, ScoreSummary::default()))
        .collect();
    for (node_id, signals) in signals_by_node {
        let summary = scores.entry(node_id).or_default();
        let (mut positive, mut counter): (Vec<_>, Vec<_>) = signals
            .into_iter()
            .partition(|signal| evidence_points(signal.evidence.kind) > 0);
        positive.sort_by(|left, right| {
            evidence_points(right.evidence.kind)
                .cmp(&evidence_points(left.evidence.kind))
                .then_with(|| left.edge.id.cmp(&right.edge.id))
        });
        counter.sort_by(|left, right| left.edge.id.cmp(&right.edge.id));
        for (index, signal) in positive.into_iter().enumerate() {
            let admitted = index < MAX_EVIDENCE_SOURCES_PER_POLARITY;
            let points = if admitted {
                evidence_points(signal.evidence.kind)
            } else {
                0
            };
            summary.evidence_score += points;
            summary.positive_evidence_sources += usize::from(points > 0);
            summary
                .contributions
                .push(evidence_contribution(&signal, points, admitted));
        }
        for (index, signal) in counter.into_iter().enumerate() {
            let admitted = index < MAX_EVIDENCE_SOURCES_PER_POLARITY;
            let points = if admitted {
                evidence_points(signal.evidence.kind)
            } else {
                0
            };
            summary.evidence_score += points;
            summary
                .contributions
                .push(evidence_contribution(&signal, points, admitted));
        }
    }

    // One contribution per supporter, regardless of repeated basis variants.
    // The chosen Edge id is only the stable explanation handle.
    let mut support_by_target_source: BTreeMap<(String, String), &Edge> = BTreeMap::new();
    for edge in population
        .relation_edges
        .iter()
        .filter(|edge| edge.kind == EdgeKind::Supports)
    {
        support_by_target_source
            .entry((edge.target.clone(), edge.source.clone()))
            .and_modify(|selected| {
                if edge.id < selected.id {
                    *selected = edge;
                }
            })
            .or_insert(edge);
    }
    // Start with every directly grounded supporter and repeatedly recompute the
    // selected set. A supporter that receded in one iteration may become
    // selected after another support contribution recedes, so the next active
    // set is rebuilt from *all* grounded selected supporters rather than only
    // shrinking the prior set.
    //
    // This dependency can oscillate (for example, two equally grounded,
    // conflicting candidates that support each other). When an active-set cycle
    // is detected, every supporter whose activity varies across the cycle is
    // conservatively disabled and derivation restarts. Each such restart
    // disables at least one previously eligible supporter, which guarantees
    // termination. Stable selected grounded supporters remain effective.
    let grounded_supporters: BTreeSet<String> = support_by_target_source
        .keys()
        .map(|(_, source)| source.clone())
        .filter(|source| scores.get(source).map_or(0, |score| score.evidence_score) > 0)
        .collect();
    let mut cycle_disabled_supporters = BTreeSet::new();
    let (scores, verdict) = 'restart: loop {
        let mut active_supporters: BTreeSet<String> = grounded_supporters
            .difference(&cycle_disabled_supporters)
            .cloned()
            .collect();
        let mut history = Vec::new();
        let mut seen = BTreeMap::new();
        loop {
            seen.insert(active_supporters.clone(), history.len());
            history.push(active_supporters.clone());
            let iteration_scores = scores_with_supports(
                &scores,
                &support_by_target_source,
                &active_supporters,
                &cycle_disabled_supporters,
            );
            let iteration_decision = select_population(node_ids, population, &iteration_scores);
            let next_active: BTreeSet<String> = grounded_supporters
                .difference(&cycle_disabled_supporters)
                .filter(|source| iteration_decision.selected.contains(*source))
                .cloned()
                .collect();
            if next_active == active_supporters {
                break 'restart (iteration_scores, iteration_decision);
            }
            if let Some(cycle_start) = seen.get(&next_active).copied() {
                let cycle = &history[cycle_start..];
                let mut present_in_any = BTreeSet::new();
                let mut present_in_every = cycle
                    .first()
                    .cloned()
                    .expect("a repeated active set starts a non-empty cycle");
                for state in cycle {
                    present_in_any.extend(state.iter().cloned());
                    present_in_every = present_in_every.intersection(state).cloned().collect();
                }
                let varying: BTreeSet<String> = present_in_any
                    .difference(&present_in_every)
                    .cloned()
                    .collect();
                debug_assert!(
                    !varying.is_empty(),
                    "a non-stable active-set cycle has a varying supporter"
                );
                cycle_disabled_supporters.extend(varying);
                continue 'restart;
            }
            active_supporters = next_active;
        }
    };

    let mut views: BTreeMap<String, SelectionView> = node_ids
        .iter()
        .map(|id| {
            let summary = scores.get(id).cloned().unwrap_or_default();
            let mut view = SelectionView {
                policy_version: FITNESS_POLICY_VERSION.into(),
                current: false,
                support_score: summary.total(),
                evidence_score: summary.evidence_score,
                relation_score: summary.relation_score,
                contributions: summary.contributions,
                ..SelectionView::default()
            };
            if view.support_score < MIN_CURRENT_SCORE {
                let kind = if view.evidence_score < 0 {
                    ExclusionKind::Counterevidence
                } else {
                    ExclusionKind::InsufficientSupport
                };
                view.exclusions.push(SelectionExclusion {
                    kind,
                    edge_id: None,
                    competing_node_id: None,
                    detail: format!(
                        "fitness {} is below the current-set threshold {MIN_CURRENT_SCORE}",
                        view.support_score
                    ),
                });
            }
            (id.clone(), view)
        })
        .collect();

    for edge in &population.relation_edges {
        if let Some(view) = views.get_mut(&edge.target) {
            match edge.kind {
                EdgeKind::Supports => view.supporting_edge_ids.push(edge.id.clone()),
                EdgeKind::Defeats => view.defeating_edge_ids.push(edge.id.clone()),
                EdgeKind::Supersedes => view.superseding_edge_ids.push(edge.id.clone()),
                _ => {}
            }
        }
    }
    for (candidate, blocker) in verdict.blockers {
        if !requested.contains(candidate.as_str()) {
            continue;
        }
        let (kind, relation) = competition_exclusion(blocker.kind, blocker.reverse_explicit);
        views
            .get_mut(&candidate)
            .expect("requested candidate has a selection view")
            .exclusions
            .push(SelectionExclusion {
                kind,
                edge_id: Some(blocker.edge_id),
                competing_node_id: Some(blocker.competitor.clone()),
                detail: format!(
                    "selected {relation} '{}' takes precedence with fitness {}",
                    blocker.competitor,
                    scores
                        .get(&blocker.competitor)
                        .map_or(0, ScoreSummary::total)
                ),
            });
    }

    for view in views.values_mut() {
        view.sort_and_dedup();
        view.current = view.exclusions.is_empty();
    }
    views
}

fn evidence_points(kind: Kind) -> i32 {
    match kind {
        Kind::Demonstrative => 8,
        Kind::Constitutive => 7,
        Kind::Testimonial => 5,
        Kind::Assertoric => 4,
        Kind::Circumstantial => 2,
        Kind::Unknown => 1,
        Kind::Counter => -8,
    }
}

fn evidence_contribution(
    signal: &EvidenceSignal<'_>,
    points: i32,
    admitted: bool,
) -> ScoreContribution {
    ScoreContribution {
        kind: match signal.evidence.kind {
            Kind::Constitutive => ScoreContributionKind::ConstitutiveEvidence,
            Kind::Demonstrative => ScoreContributionKind::DemonstrativeEvidence,
            Kind::Testimonial => ScoreContributionKind::TestimonialEvidence,
            Kind::Assertoric => ScoreContributionKind::AssertoricEvidence,
            Kind::Circumstantial => ScoreContributionKind::CircumstantialEvidence,
            Kind::Counter => ScoreContributionKind::CounterEvidence,
            Kind::Unknown => ScoreContributionKind::UnknownEvidence,
        },
        points,
        edge_id: signal.edge.id.clone(),
        source_node_id: None,
        evidence_node_id: Some(signal.evidence_node_id.to_string()),
        detail: if admitted {
            format!(
                "{} at {} contributes {points} point(s)",
                signal.evidence.kind.as_str(),
                signal.evidence.locator.render()
            )
        } else {
            format!(
                "{} at {} ignored after the first {MAX_EVIDENCE_SOURCES_PER_POLARITY} sources of this polarity",
                signal.evidence.kind.as_str(),
                signal.evidence.locator.render()
            )
        },
    }
}

pub(crate) fn is_semantic_competition(kind: EdgeKind) -> bool {
    matches!(
        kind,
        EdgeKind::Refines
            | EdgeKind::Equivalent
            | EdgeKind::HardContradiction
            | EdgeKind::AdvisoryTension
            | EdgeKind::DescriptiveConflict
            | EdgeKind::EnvelopeConflict
    )
}

fn substantive_priority(summary: &ScoreSummary) -> (i32, i32, usize) {
    (
        summary.total(),
        summary.evidence_score,
        summary.positive_evidence_sources,
    )
}

fn scores_with_supports(
    direct: &BTreeMap<String, ScoreSummary>,
    supports: &BTreeMap<(String, String), &Edge>,
    active_supporters: &BTreeSet<String>,
    cycle_disabled_supporters: &BTreeSet<String>,
) -> BTreeMap<String, ScoreSummary> {
    let mut scores = direct.clone();
    let mut by_target: BTreeMap<String, Vec<(String, &Edge, i32)>> = BTreeMap::new();
    for ((target, source), edge) in supports {
        let available = direct
            .get(source)
            .map_or(0, |summary| summary.evidence_score.max(0))
            .min(MAX_POINTS_PER_SUPPORTER);
        by_target
            .entry(target.clone())
            .or_default()
            .push((source.clone(), edge, available));
    }
    for (target, mut supporters) in by_target {
        supporters.sort_by(|left, right| {
            right
                .2
                .cmp(&left.2)
                .then_with(|| left.0.cmp(&right.0))
                .then_with(|| left.1.id.cmp(&right.1.id))
        });
        let summary = scores.entry(target).or_default();
        let mut admitted_count = 0;
        for (source, edge, available) in supporters {
            let active = active_supporters.contains(&source) && available > 0;
            let admitted = active && admitted_count < MAX_GROUNDED_SUPPORTERS;
            admitted_count += usize::from(admitted);
            let points = if admitted { available } else { 0 };
            summary.relation_score += points;
            summary.contributions.push(ScoreContribution {
                kind: if points > 0 {
                    ScoreContributionKind::GroundedSupport
                } else {
                    ScoreContributionKind::InertSupport
                },
                points,
                edge_id: edge.id.clone(),
                source_node_id: Some(source.clone()),
                evidence_node_id: None,
                detail: if available == 0 {
                    "supporter has no positive direct Evidence; support is inert".into()
                } else if cycle_disabled_supporters.contains(&source) {
                    "support_dependency_cycle: supporter activity oscillated; support is conservatively disabled"
                        .into()
                } else if !active {
                    "supporter did not survive selection; support recedes with it".into()
                } else if !admitted {
                    format!(
                        "ignored after the first {MAX_GROUNDED_SUPPORTERS} grounded supporters"
                    )
                } else {
                    format!(
                        "selected grounded supporter transfers {points} point(s), capped at {MAX_POINTS_PER_SUPPORTER}"
                    )
                },
            });
        }
    }
    scores
}

#[derive(Debug)]
struct SelectionDecision {
    selected: BTreeSet<String>,
    blockers: BTreeMap<String, SelectionBlocker>,
}

#[derive(Debug)]
struct SelectionBlocker {
    edge_id: String,
    kind: EdgeKind,
    competitor: String,
    reverse_explicit: bool,
}

fn select_population(
    requested_ids: &[String],
    population: &SelectionPopulation,
    scores: &BTreeMap<String, ScoreSummary>,
) -> SelectionDecision {
    let mut candidate_ids: BTreeSet<String> = requested_ids.iter().cloned().collect();
    let mut semantic_adjacency: BTreeMap<String, Vec<&Edge>> = BTreeMap::new();
    let mut explicit_adjacency: BTreeMap<String, Vec<&Edge>> = BTreeMap::new();
    for edge in &population.relation_edges {
        candidate_ids.insert(edge.source.clone());
        candidate_ids.insert(edge.target.clone());
        if is_semantic_competition(edge.kind) {
            semantic_adjacency
                .entry(edge.source.clone())
                .or_default()
                .push(edge);
            semantic_adjacency
                .entry(edge.target.clone())
                .or_default()
                .push(edge);
        } else if matches!(edge.kind, EdgeKind::Defeats | EdgeKind::Supersedes) {
            explicit_adjacency
                .entry(edge.target.clone())
                .or_default()
                .push(edge);
            explicit_adjacency
                .entry(edge.source.clone())
                .or_default()
                .push(edge);
        }
    }
    let viable: BTreeSet<String> = candidate_ids
        .into_iter()
        .filter(|id| scores.get(id).map_or(0, ScoreSummary::total) >= MIN_CURRENT_SCORE)
        .collect();
    let mut precedence = BTreeSet::new();
    for edge in &population.relation_edges {
        if !viable.contains(&edge.source) || !viable.contains(&edge.target) {
            continue;
        }
        if matches!(edge.kind, EdgeKind::Defeats | EdgeKind::Supersedes) {
            precedence.insert((edge.source.clone(), edge.target.clone()));
        } else if edge.kind == EdgeKind::Refines {
            // A proved, viable concrete specification is strictly more precise
            // than its abstraction. Evidence establishes viability; it does
            // not reverse the semantic refinement direction and make the less
            // precise statement the better approximation.
            precedence.insert((edge.source.clone(), edge.target.clone()));
        }
    }

    // A constrained topological order honors explicit direction only between
    // its endpoints. Among unrelated ready candidates, fitness still decides.
    // A directed cycle is broken by the same deterministic fitness/id order.
    let mut remaining = viable;
    let mut ordered = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        let mut ready: Vec<String> = remaining
            .iter()
            .filter(|candidate| {
                !precedence
                    .iter()
                    .any(|(source, target)| target == *candidate && remaining.contains(source))
            })
            .cloned()
            .collect();
        if ready.is_empty() {
            ready.extend(remaining.iter().cloned());
        }
        ready.sort_by(|left, right| {
            let left_score = scores.get(left).cloned().unwrap_or_default();
            let right_score = scores.get(right).cloned().unwrap_or_default();
            substantive_priority(&right_score)
                .cmp(&substantive_priority(&left_score))
                .then_with(|| left.cmp(right))
        });
        let candidate = ready.remove(0);
        remaining.remove(&candidate);
        ordered.push(candidate);
    }
    let order: BTreeMap<String, usize> = ordered
        .iter()
        .enumerate()
        .map(|(position, id)| (id.clone(), position))
        .collect();

    let mut selected = BTreeSet::new();
    let mut blockers = BTreeMap::new();
    for candidate in ordered {
        let semantic_blocker = semantic_adjacency
            .get(&candidate)
            .into_iter()
            .flat_map(|edges| {
                edges.iter().filter_map(|edge| {
                    let competitor = if edge.source == candidate {
                        edge.target.as_str()
                    } else {
                        edge.source.as_str()
                    };
                    selected
                        .contains(competitor)
                        .then_some((*edge, competitor, false))
                })
            });
        let explicit_blocker = explicit_adjacency
            .get(&candidate)
            .into_iter()
            .flat_map(|edges| {
                edges.iter().filter_map(|edge| {
                    let competitor = if edge.source == candidate {
                        edge.target.as_str()
                    } else {
                        edge.source.as_str()
                    };
                    selected.contains(competitor).then_some((
                        *edge,
                        competitor,
                        edge.source == candidate,
                    ))
                })
            });
        let blocker =
            semantic_blocker
                .chain(explicit_blocker)
                .min_by_key(|(edge, competitor, _)| {
                    (
                        order.get(*competitor).copied().unwrap_or(usize::MAX),
                        &edge.id,
                    )
                });
        if let Some((edge, competitor, reverse_explicit)) = blocker {
            blockers.insert(
                candidate,
                SelectionBlocker {
                    edge_id: edge.id.clone(),
                    kind: edge.kind,
                    competitor: competitor.to_string(),
                    reverse_explicit,
                },
            );
        } else {
            selected.insert(candidate);
        }
    }
    SelectionDecision { selected, blockers }
}

fn competition_exclusion(kind: EdgeKind, reverse_explicit: bool) -> (ExclusionKind, &'static str) {
    if reverse_explicit {
        return (
            ExclusionKind::SelectionCycle,
            "explicit-selection cycle winner",
        );
    }
    match kind {
        EdgeKind::Defeats => (ExclusionKind::Defeated, "defeating candidate"),
        EdgeKind::Supersedes => (ExclusionKind::Superseded, "superseding candidate"),
        EdgeKind::Equivalent => (ExclusionKind::EquivalentDuplicate, "equivalent candidate"),
        EdgeKind::Refines => (ExclusionKind::RefinementDominated, "refinement candidate"),
        _ => (ExclusionKind::Contradicted, "conflicting candidate"),
    }
}

#[derive(Debug, Error)]
pub enum SelectionError {
    #[error("selection relations require supports, defeats, or supersedes")]
    InvalidKind,
    #[error("a selection relation cannot connect a specification to itself")]
    SelfRelation,
    #[error("basis specification '{0}' repeats an endpoint already intrinsic to the relation")]
    BasisRepeatsEndpoint(String),
    #[error("specification node '{0}' does not exist")]
    MissingNode(String),
    #[error(transparent)]
    Store(#[from] StoreError),
}

impl SelectionError {
    pub fn is_bad_input(&self) -> bool {
        !matches!(self, Self::Store(_))
    }
}

/// Validate and idempotently append one explicit selection relation. The Edge
/// identity excludes recording time, so retrying the same judgment returns the
/// same Ledger fact rather than creating noise.
pub fn append_relation(
    store: &(dyn GraphStore + Send + Sync),
    kind: EdgeKind,
    source: &str,
    target: &str,
    basis_spec_ids: Vec<String>,
    recorded_at: &str,
) -> Result<Edge, SelectionError> {
    if kind.family() != EdgeFamily::Selection {
        return Err(SelectionError::InvalidKind);
    }
    if source == target {
        return Err(SelectionError::SelfRelation);
    }
    for id in &basis_spec_ids {
        if id == source || id == target {
            return Err(SelectionError::BasisRepeatsEndpoint(id.clone()));
        }
    }
    let mut required = vec![source.to_string(), target.to_string()];
    required.extend(basis_spec_ids.iter().cloned());
    required.sort();
    required.dedup();
    for id in required {
        if store.get_node(&id)?.is_none() {
            return Err(SelectionError::MissingNode(id));
        }
    }

    let edge = Edge::specification_relation(
        kind,
        source,
        target,
        basis_spec_ids,
        derivation(),
        recorded_at,
    )
    .map_err(|message| SelectionError::Store(StoreError::InvalidEdge(message)))?;
    if store.append_edge(&edge)? {
        return Ok(edge);
    }
    store.get_edge(&edge.id)?.ok_or_else(|| {
        SelectionError::Store(StoreError::Backend(format!(
            "selection Edge '{}' existed during append but could not be read back",
            edge.id
        )))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{
        Anchor, Evidence, Locator, Meta, Node, Origin, SelectionPopulation, Snapshot,
    };
    use crate::store::{InMemoryNodeStore, NodeStore};

    fn node(id: &str) -> Node {
        Node {
            id: id.into(),
            statement: "The pump shall stop.".into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: vec![],
                evidence_request_generation: String::new(),
                evidence: vec![],
                created_at: "t".into(),
                cli: "test".into(),
                cli_version: "test".into(),
                updates: Default::default(),
            },
        }
    }

    fn evidence(kind: Kind, locator: &str, hash: &str) -> DerivedNode {
        DerivedNode::evidence(Evidence {
            kind,
            locator: Locator::parse(locator),
            snapshot: Snapshot {
                content: String::new(),
                content_hash: hash.into(),
                bytes: 1,
                captured_at: "capture".into(),
                anchor: Anchor::Worktree,
            },
            origin: Origin::default(),
        })
    }

    fn grounding(specification: &str, evidence: &DerivedNode, at: &str) -> Edge {
        Edge::projection(
            EdgeKind::GroundedBy,
            specification,
            evidence.id(),
            crate::evidence_capture::evidence_derivation(),
            at,
        )
        .unwrap()
    }

    fn relation(kind: EdgeKind, source: &str, target: &str, basis: &[&str]) -> Edge {
        Edge::specification_relation(
            kind,
            source,
            target,
            basis.iter().map(|id| (*id).to_string()).collect(),
            if kind.family() == EdgeFamily::Selection {
                derivation()
            } else {
                crate::graph_generation::semantic_edge_derivation()
            },
            "relation",
        )
        .unwrap()
    }

    fn population(
        evidence: Vec<(&str, DerivedNode, &str)>,
        relations: Vec<Edge>,
    ) -> SelectionPopulation {
        let mut result = SelectionPopulation {
            relation_edges: relations,
            ..SelectionPopulation::default()
        };
        for (specification, node, at) in evidence {
            result
                .evidence_edges
                .push(grounding(specification, &node, at));
            result.evidence_nodes.push(node);
        }
        result
    }

    #[test]
    fn explicit_relation_is_checked_and_idempotent() {
        let store = InMemoryNodeStore::new();
        for id in ["source", "target", "basis"] {
            store.add_node(&node(id)).unwrap();
        }
        let first = append_relation(
            &store,
            EdgeKind::Supersedes,
            "source",
            "target",
            vec!["basis".into()],
            "t1",
        )
        .unwrap();
        let retry = append_relation(
            &store,
            EdgeKind::Supersedes,
            "source",
            "target",
            vec!["basis".into()],
            "t2",
        )
        .unwrap();
        assert_eq!(first.id, retry.id);
        assert_eq!(first.derivation, derivation());
        assert_eq!(retry.recorded_at, "t1", "a retry returns the Ledger fact");
    }

    #[test]
    fn semantic_self_and_missing_relations_are_rejected() {
        let store = InMemoryNodeStore::new();
        store.add_node(&node("source")).unwrap();
        assert!(matches!(
            append_relation(&store, EdgeKind::Refines, "source", "missing", vec![], "t"),
            Err(SelectionError::InvalidKind)
        ));
        assert!(matches!(
            append_relation(&store, EdgeKind::Supports, "source", "source", vec![], "t"),
            Err(SelectionError::SelfRelation)
        ));
        assert!(matches!(
            append_relation(&store, EdgeKind::Supports, "source", "missing", vec![], "t"),
            Err(SelectionError::MissingNode(id)) if id == "missing"
        ));
    }

    #[test]
    fn admission_alone_never_makes_a_candidate_current() {
        let views = derive_views(&["candidate".into()], &SelectionPopulation::default());
        let view = &views["candidate"];
        assert!(!view.current);
        assert_eq!(view.support_score, 0);
        assert_eq!(view.policy_version, FITNESS_POLICY_VERSION);
        assert_eq!(view.exclusions[0].kind, ExclusionKind::InsufficientSupport);
    }

    #[test]
    fn grounded_support_transfers_finite_fitness_but_cycles_cannot_bootstrap() {
        let supports_ab = relation(EdgeKind::Supports, "a", "b", &[]);
        let supports_ba = relation(EdgeKind::Supports, "b", "a", &[]);
        let relations = vec![supports_ab.clone(), supports_ba.clone()];
        let empty = population(vec![], relations.clone());
        let views = derive_views(&["a".into(), "b".into()], &empty);
        assert!(!views["a"].current);
        assert!(!views["b"].current);
        assert_eq!(views["a"].relation_score, 0);
        assert_eq!(views["b"].relation_score, 0);

        let proof = evidence(Kind::Demonstrative, "proof-a", "a");
        let grounded = population(vec![("a", proof, "t1")], relations);
        let views = derive_views(&["a".into(), "b".into()], &grounded);
        assert_eq!(views["a"].support_score, 8);
        assert_eq!(views["b"].relation_score, MAX_POINTS_PER_SUPPORTER);
        assert!(views["a"].current);
        assert!(views["b"].current);
    }

    #[test]
    fn stronger_evidence_automatically_flips_a_conflict_winner() {
        let conflict = relation(EdgeKind::HardContradiction, "low", "high", &[]);
        let low_hint = evidence(Kind::Unknown, "low-hint", "low-1");
        let high_policy = evidence(Kind::Assertoric, "high-policy", "high-1");
        let initial = population(
            vec![
                ("low", low_hint.clone(), "t1"),
                ("high", high_policy.clone(), "t1"),
            ],
            vec![conflict.clone()],
        );
        let ids = vec!["low".into(), "high".into()];
        let views = derive_views(&ids, &initial);
        assert!(!views["low"].current);
        assert!(views["high"].current);
        assert_eq!(views["low"].exclusions[0].kind, ExclusionKind::Contradicted);

        let low_proof = evidence(Kind::Demonstrative, "low-proof", "low-2");
        let improved = population(
            vec![
                ("low", low_hint, "t1"),
                ("low", low_proof, "t2"),
                ("high", high_policy, "t1"),
            ],
            vec![conflict],
        );
        let views = derive_views(&ids, &improved);
        assert!(views["low"].current);
        assert!(!views["high"].current);
        assert_eq!(views["low"].support_score, 9);
        assert_eq!(views["high"].support_score, 4);
    }

    #[test]
    fn a_viable_refiner_replaces_a_better_scored_abstraction() {
        let refines = relation(EdgeKind::Refines, "concrete", "abstract", &[]);
        let concrete_basis = evidence(Kind::Unknown, "concrete-basis", "concrete");
        let abstract_proof = evidence(Kind::Demonstrative, "abstract-proof", "abstract");
        let graph = population(
            vec![
                ("concrete", concrete_basis, "t1"),
                ("abstract", abstract_proof, "t1"),
            ],
            vec![refines],
        );
        let views = derive_views(&["concrete".into(), "abstract".into()], &graph);

        assert!(views["concrete"].current);
        assert!(!views["abstract"].current);
        assert_eq!(views["concrete"].support_score, 1);
        assert_eq!(views["abstract"].support_score, 8);
        assert_eq!(
            views["abstract"].exclusions[0].kind,
            ExclusionKind::RefinementDominated
        );
    }

    #[test]
    fn rejected_middle_candidate_cannot_remove_a_compatible_endpoint() {
        let conflict_ab = relation(EdgeKind::HardContradiction, "a", "b", &[]);
        let conflict_bc = relation(EdgeKind::HardContradiction, "b", "c", &[]);
        let proof_a = evidence(Kind::Demonstrative, "proof-a", "a");
        let proof_b = evidence(Kind::Assertoric, "proof-b", "b");
        let proof_c = evidence(Kind::Circumstantial, "proof-c", "c");
        let graph = population(
            vec![
                ("a", proof_a, "t1"),
                ("b", proof_b, "t1"),
                ("c", proof_c, "t1"),
            ],
            vec![conflict_ab, conflict_bc],
        );
        let views = derive_views(&["a".into(), "b".into(), "c".into()], &graph);

        assert!(views["a"].current);
        assert!(!views["b"].current);
        assert!(views["c"].current);
        assert_eq!(
            views["b"].exclusions[0].competing_node_id.as_deref(),
            Some("a")
        );
    }

    #[test]
    fn rejected_defeater_cannot_remove_a_candidate_from_the_current_set() {
        let defeats = relation(EdgeKind::Defeats, "a", "b", &[]);
        let conflict = relation(EdgeKind::HardContradiction, "c", "a", &[]);
        let proof_a = evidence(Kind::Assertoric, "proof-a", "a");
        let proof_b = evidence(Kind::Circumstantial, "proof-b", "b");
        let proof_c = evidence(Kind::Demonstrative, "proof-c", "c");
        let graph = population(
            vec![
                ("a", proof_a, "t1"),
                ("b", proof_b, "t1"),
                ("c", proof_c, "t1"),
            ],
            vec![defeats, conflict],
        );
        let views = derive_views(&["a".into(), "b".into(), "c".into()], &graph);

        assert!(!views["a"].current);
        assert!(views["b"].current);
        assert!(views["c"].current);
        assert!(views["b"]
            .exclusions
            .iter()
            .all(|reason| reason.kind != ExclusionKind::Defeated));
    }

    #[test]
    fn support_recedes_when_its_source_does_not_survive_selection() {
        let supports = relation(EdgeKind::Supports, "a", "b", &[]);
        let conflict = relation(EdgeKind::HardContradiction, "c", "a", &[]);
        let proof_a = evidence(Kind::Assertoric, "proof-a", "a");
        let proof_c = evidence(Kind::Demonstrative, "proof-c", "c");
        let graph = population(
            vec![("a", proof_a, "t1"), ("c", proof_c, "t1")],
            vec![supports, conflict],
        );
        let views = derive_views(&["a".into(), "b".into(), "c".into()], &graph);

        assert!(!views["a"].current);
        assert!(!views["b"].current);
        assert!(views["c"].current);
        assert_eq!(views["b"].relation_score, 0);
        assert!(views["b"].contributions.iter().any(|contribution| {
            contribution.kind == ScoreContributionKind::InertSupport
                && contribution.detail.contains("recedes with it")
        }));
    }

    #[test]
    fn grounded_supporter_reactivates_after_other_support_recedes() {
        let graph = population(
            vec![
                ("x", evidence(Kind::Assertoric, "proof-x", "x"), "t1"),
                ("y", evidence(Kind::Unknown, "hint-y", "y"), "t1"),
                ("w", evidence(Kind::Assertoric, "proof-w", "w"), "t1"),
                ("q", evidence(Kind::Demonstrative, "proof-q", "q"), "t1"),
            ],
            vec![
                relation(EdgeKind::Supports, "x", "t", &[]),
                relation(EdgeKind::Supports, "w", "y", &[]),
                relation(EdgeKind::HardContradiction, "x", "y", &[]),
                relation(EdgeKind::HardContradiction, "w", "q", &[]),
            ],
        );
        let views = derive_views(
            &["x".into(), "y".into(), "w".into(), "q".into(), "t".into()],
            &graph,
        );

        // Initially W raises Y above X, but Q removes W. Once W's support
        // recedes, X wins its conflict and must be reactivated as T's selected,
        // directly grounded supporter.
        assert!(views["x"].current);
        assert!(!views["y"].current);
        assert!(!views["w"].current);
        assert!(views["q"].current);
        assert!(views["t"].current);
        assert_eq!(views["t"].relation_score, MAX_POINTS_PER_SUPPORTER);
        assert!(views["t"].contributions.iter().any(|contribution| {
            contribution.kind == ScoreContributionKind::GroundedSupport
                && contribution.source_node_id.as_deref() == Some("x")
                && contribution.points == MAX_POINTS_PER_SUPPORTER
        }));
    }

    #[test]
    fn oscillating_supporters_are_conservatively_disabled_and_explained() {
        let graph = population(
            vec![
                ("a", evidence(Kind::Assertoric, "proof-a", "a"), "t1"),
                ("b", evidence(Kind::Assertoric, "proof-b", "b"), "t1"),
            ],
            vec![
                relation(EdgeKind::Supports, "a", "b", &[]),
                relation(EdgeKind::Supports, "b", "a", &[]),
                relation(EdgeKind::HardContradiction, "a", "b", &[]),
            ],
        );
        let views = derive_views(&["a".into(), "b".into()], &graph);

        // With both supports active, A wins the tie; A alone then boosts B,
        // and B alone boosts A. Both sources vary across that dependency cycle,
        // so neither transfer survives and direct Evidence breaks the tie.
        assert!(views["a"].current);
        assert!(!views["b"].current);
        assert_eq!(views["a"].relation_score, 0);
        assert_eq!(views["b"].relation_score, 0);
        for id in ["a", "b"] {
            assert!(views[id].contributions.iter().any(|contribution| {
                contribution.kind == ScoreContributionKind::InertSupport
                    && contribution.points == 0
                    && contribution.detail.contains("support_dependency_cycle")
            }));
        }
    }

    #[test]
    fn explicit_selection_cycle_keeps_no_opposed_endpoints_together() {
        let graph = population(
            vec![
                ("a", evidence(Kind::Assertoric, "proof-a", "a"), "t1"),
                ("b", evidence(Kind::Assertoric, "proof-b", "b"), "t1"),
                ("c", evidence(Kind::Assertoric, "proof-c", "c"), "t1"),
            ],
            vec![
                relation(EdgeKind::Defeats, "a", "b", &[]),
                relation(EdgeKind::Defeats, "b", "c", &[]),
                relation(EdgeKind::Defeats, "c", "a", &[]),
            ],
        );
        let views = derive_views(&["a".into(), "b".into(), "c".into()], &graph);
        let current: BTreeSet<&str> = views
            .iter()
            .filter(|(_, view)| view.current)
            .map(|(id, _)| id.as_str())
            .collect();

        assert_eq!(current.len(), 1);
        assert!(views.values().any(|view| {
            view.exclusions
                .iter()
                .any(|reason| reason.kind == ExclusionKind::SelectionCycle)
        }));
    }

    #[test]
    fn every_four_candidate_conflict_graph_selects_a_maximal_coherent_set() {
        let ids = ["a", "b", "c", "d"];
        let pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
        for mask in 0_u8..(1 << pairs.len()) {
            let relations: Vec<Edge> = pairs
                .iter()
                .enumerate()
                .filter(|(bit, _)| mask & (1 << bit) != 0)
                .map(|(_, &(left, right))| {
                    relation(EdgeKind::HardContradiction, ids[left], ids[right], &[])
                })
                .collect();
            let evidence = ids
                .iter()
                .map(|id| {
                    (
                        *id,
                        evidence(Kind::Assertoric, &format!("proof-{id}"), id),
                        "t1",
                    )
                })
                .collect();
            let graph = population(evidence, relations.clone());
            let requested = ids.map(str::to_string);
            let views = derive_views(&requested, &graph);

            for edge in &relations {
                assert!(
                    !(views[&edge.source].current && views[&edge.target].current),
                    "mask {mask:#08b} selected both conflict endpoints"
                );
            }
            for id in ids {
                if views[id].current {
                    continue;
                }
                assert!(
                    relations.iter().any(|edge| {
                        (edge.source == id && views[&edge.target].current)
                            || (edge.target == id && views[&edge.source].current)
                    }),
                    "mask {mask:#08b} rejected {id} without a selected competitor"
                );
            }
        }
    }

    #[test]
    fn evidence_and_support_volume_is_bounded_and_fully_explained() {
        let evidence_inputs: Vec<(&str, DerivedNode, &str)> = (0..5)
            .map(|index| {
                (
                    "target",
                    evidence(
                        Kind::Demonstrative,
                        &format!("target-proof-{index}"),
                        &format!("target-{index}"),
                    ),
                    "t1",
                )
            })
            .collect();
        let views = derive_views(&["target".into()], &population(evidence_inputs, vec![]));
        assert_eq!(views["target"].evidence_score, 32);
        assert_eq!(views["target"].contributions.len(), 5);
        assert_eq!(
            views["target"]
                .contributions
                .iter()
                .map(|contribution| contribution.points)
                .sum::<i32>(),
            views["target"].support_score
        );

        let mut supporter_evidence = Vec::new();
        let mut supports = Vec::new();
        let mut requested = vec!["supported".to_string()];
        for (index, id) in ["source-0", "source-1", "source-2", "source-3", "source-4"]
            .into_iter()
            .enumerate()
        {
            supporter_evidence.push((
                id,
                evidence(
                    Kind::Demonstrative,
                    &format!("source-proof-{index}"),
                    &format!("source-{index}"),
                ),
                "t1",
            ));
            supports.push(relation(EdgeKind::Supports, id, "supported", &[]));
            requested.push(id.to_string());
        }
        let graph = population(supporter_evidence, supports);
        let views = derive_views(&requested, &graph);
        assert_eq!(views["supported"].relation_score, 16);
        assert_eq!(views["supported"].contributions.len(), 5);
        assert_eq!(
            views["supported"]
                .contributions
                .iter()
                .filter(|contribution| contribution.points == 0)
                .count(),
            1
        );
    }

    #[test]
    fn latest_capture_per_locator_replaces_old_support_without_erasing_history() {
        let old = evidence(Kind::Demonstrative, "same-source", "old");
        let new = evidence(Kind::Counter, "same-source", "new");
        let graph = population(
            vec![("candidate", old, "t1"), ("candidate", new, "t2")],
            vec![],
        );
        let views = derive_views(&["candidate".into()], &graph);
        let view = &views["candidate"];
        assert_eq!(view.evidence_score, -8);
        assert!(!view.current);
        assert_eq!(view.contributions.len(), 1);
        assert_eq!(
            view.contributions[0].kind,
            ScoreContributionKind::CounterEvidence
        );
    }

    #[test]
    fn repeated_support_basis_does_not_multiply_one_supporter() {
        let source_proof = evidence(Kind::Demonstrative, "proof", "proof");
        let one = relation(EdgeKind::Supports, "source", "target", &["basis-a"]);
        let two = relation(EdgeKind::Supports, "source", "target", &["basis-b"]);
        let graph = population(vec![("source", source_proof, "t1")], vec![one, two]);
        let views = derive_views(&["target".into()], &graph);
        assert_eq!(views["target"].relation_score, MAX_POINTS_PER_SUPPORTER);
        assert_eq!(views["target"].supporting_edge_ids.len(), 2);
        assert_eq!(views["target"].contributions.len(), 1);
    }
}
