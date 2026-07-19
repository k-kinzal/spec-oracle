//! The versioned fitness/current-set policy.
//!
//! Every relationship consumed here is mechanically derived. Semantic
//! relationships remain the output of `so-reason`; this module only projects
//! current Evidence fitness and the coherent semantic competition set. Storage
//! supplies complete competition components, and every contribution and
//! exclusion stays visible.

use std::collections::{BTreeMap, BTreeSet};

use crate::domain::{
    DerivedNode, Edge, EdgeKind, ExclusionKind, Kind, Node, ScoreContribution,
    ScoreContributionKind, SelectionExclusion, SelectionPopulation, SelectionView,
};

pub const FITNESS_POLICY_VERSION: &str = "selection/fitness-v5";

const MIN_CURRENT_SCORE: i32 = 1;
const MAX_EVIDENCE_SOURCES_PER_POLARITY: usize = 4;

pub fn is_fitness_relation(kind: EdgeKind) -> bool {
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
    positive_evidence_sources: usize,
    contributions: Vec<ScoreContribution>,
}

impl ScoreSummary {
    fn total(&self) -> i32 {
        self.evidence_score
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
/// a candidate, not a fact. Direct captured Evidence supplies bounded points,
/// and mechanically proved semantic relationships select a coherent subset of
/// the viable candidates.
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

    let verdict = select_population(node_ids, population, &scores);

    let mut views: BTreeMap<String, SelectionView> = node_ids
        .iter()
        .map(|id| {
            let summary = scores.get(id).cloned().unwrap_or_default();
            let mut view = SelectionView {
                policy_version: FITNESS_POLICY_VERSION.into(),
                current: false,
                support_score: summary.total(),
                evidence_score: summary.evidence_score,
                relation_score: 0,
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

    for (candidate, blocker) in verdict.blockers {
        if !requested.contains(candidate.as_str()) {
            continue;
        }
        let (kind, relation) = competition_exclusion(blocker.kind);
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

#[derive(Debug)]
struct SelectionDecision {
    blockers: BTreeMap<String, SelectionBlocker>,
}

#[derive(Debug)]
struct SelectionBlocker {
    edge_id: String,
    kind: EdgeKind,
    competitor: String,
}

fn select_population(
    requested_ids: &[String],
    population: &SelectionPopulation,
    scores: &BTreeMap<String, ScoreSummary>,
) -> SelectionDecision {
    let mut candidate_ids: BTreeSet<String> = requested_ids.iter().cloned().collect();
    let mut semantic_adjacency: BTreeMap<String, Vec<&Edge>> = BTreeMap::new();
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
        if edge.kind == EdgeKind::Refines {
            // A proved, viable concrete specification is strictly more precise
            // than its abstraction. Evidence establishes viability; it does
            // not reverse the semantic refinement direction and make the less
            // precise statement the better approximation.
            precedence.insert((edge.source.clone(), edge.target.clone()));
        }
    }

    // A constrained topological order honors mechanically proved refinement.
    // Among unrelated ready candidates, fitness decides. A directed cycle is
    // broken by the same deterministic fitness/id order.
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
        let blocker = semantic_adjacency
            .get(&candidate)
            .into_iter()
            .flat_map(|edges| {
                edges.iter().filter_map(|edge| {
                    let competitor = if edge.source == candidate {
                        edge.target.as_str()
                    } else {
                        edge.source.as_str()
                    };
                    selected.contains(competitor).then_some((*edge, competitor))
                })
            })
            .min_by_key(|(edge, competitor)| {
                (
                    order.get(*competitor).copied().unwrap_or(usize::MAX),
                    &edge.id,
                )
            });
        if let Some((edge, competitor)) = blocker {
            blockers.insert(
                candidate,
                SelectionBlocker {
                    edge_id: edge.id.clone(),
                    kind: edge.kind,
                    competitor: competitor.to_string(),
                },
            );
        } else {
            selected.insert(candidate);
        }
    }
    SelectionDecision { blockers }
}

fn competition_exclusion(kind: EdgeKind) -> (ExclusionKind, &'static str) {
    match kind {
        EdgeKind::Equivalent => (ExclusionKind::EquivalentDuplicate, "equivalent candidate"),
        EdgeKind::Refines => (ExclusionKind::RefinementDominated, "refinement candidate"),
        _ => (ExclusionKind::Contradicted, "conflicting candidate"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Anchor, Evidence, Locator, Origin, SelectionPopulation, Snapshot};

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
            crate::graph_generation::semantic_edge_derivation(),
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
    fn admission_alone_never_makes_a_candidate_current() {
        let views = derive_views(&["candidate".into()], &SelectionPopulation::default());
        let view = &views["candidate"];
        assert!(!view.current);
        assert_eq!(view.support_score, 0);
        assert_eq!(view.policy_version, FITNESS_POLICY_VERSION);
        assert_eq!(view.exclusions[0].kind, ExclusionKind::InsufficientSupport);
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
    fn evidence_volume_is_bounded_and_fully_explained() {
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
}
