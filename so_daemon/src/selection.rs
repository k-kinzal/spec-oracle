//! Versioned fitness and current-set policy over the current specification graph.
//!
//! `fitness-v15` treats Specifications as the primary source of structural
//! support. It compiles weighted AND-clauses from proved semantic paths,
//! evaluates provenance-carrying explanations recursively, and combines only
//! root-disjoint alternatives. Captured Evidence remains a decaying external
//! term. Lexical/projection identity facts discover or explain candidates but
//! never become support merely because words overlap. Layered realization is
//! discovered from persisted operational roles and composed in this view; no
//! support Edge is persisted.

use std::collections::{BTreeMap, BTreeSet};

use chrono::{DateTime, Utc};

use crate::domain::{
    DerivedNode, Edge, EdgeKind, EvaluationState, ExclusionKind, Kind, Node, ScoreContribution,
    ScoreContributionKind, SelectionExclusion, SelectionPopulation, SelectionView, VertexKind,
};

pub const FITNESS_POLICY_VERSION: &str = "selection/fitness-v15";

const MIN_CURRENT_SCORE: i32 = 1;
const EVIDENCE_HALF_LIFE_DAYS: f64 = 30.0;
const MAX_POSITIVE_EVIDENCE_SCORE: i32 = 20;
const MAX_COUNTER_EVIDENCE_SCORE: i32 = 20;
const MAX_STRUCTURAL_SCORE: i32 = 80;
/// Authorship admits a specification as a weak root that may support another
/// specification. This prior is never awarded to the specification itself as
/// structural support.
const STRUCTURAL_ADMISSION_PRIOR: f64 = 0.15;

/// Edges that may participate in a typed support/conflict closure. Exact
/// Guarantee and Contract identity form semantic connectors. Lexical
/// incidence/affinity is deliberately excluded: it discovers candidates but
/// cannot itself prove that one specification supports another. Evidence
/// grounding and the universal ingest Assumption also do not form topology.
pub fn is_selection_topology(kind: EdgeKind) -> bool {
    matches!(
        kind,
        EdgeKind::Refines
            | EdgeKind::Equivalent
            | EdgeKind::HardContradiction
            | EdgeKind::AdvisoryTension
            | EdgeKind::DescriptiveConflict
            | EdgeKind::EnvelopeConflict
            | EdgeKind::OccurrenceReliance
            | EdgeKind::GuaranteeDischarge
            | EdgeKind::AdmissibilityEnvelope
            | EdgeKind::HasGuarantee
            | EdgeKind::HasContract
            | EdgeKind::ContractRefines
            | EdgeKind::ContractEquivalent
            | EdgeKind::CompositionOperand
            | EdgeKind::QuotientDividend
            | EdgeKind::QuotientDivisor
            | EdgeKind::MergeOperand
            | EdgeKind::HasBehavior
            | EdgeKind::WitnessesEntity
            | EdgeKind::EngagesEntity
    )
}

/// Whether the selection population may follow `edge` away from `vertex`.
///
/// Most logical/conflict topology remains bidirectional because the view must
/// inspect the whole competition component. Operational composition is
/// directional: an upper specification owns a Behavior, that Behavior
/// witnesses its binding objects, and an Entity leads back only to Behaviors
/// that govern it as their subject or react to it as a trigger. Following a
/// witness backwards, or following an engagement from Behavior to Entity,
/// would enumerate specifications that the requested view can support rather
/// than specifications that can support the requested view. It would also
/// turn Means and guards into population-expansion hints despite their
/// explicit exclusion from the support judgment.
pub(crate) fn follows_selection_topology(edge: &Edge, vertex: &str) -> bool {
    if vertex != edge.source && vertex != edge.target {
        return false;
    }
    match edge.kind {
        EdgeKind::HasBehavior => true,
        EdgeKind::WitnessesEntity => vertex == edge.source,
        EdgeKind::EngagesEntity => {
            vertex == edge.target
                && edge.source_anchor.as_ref().is_some_and(|anchor| {
                    matches!(
                        anchor.role.as_str(),
                        "operational_subject" | "operational_trigger"
                    )
                })
        }
        kind => is_selection_topology(kind),
    }
}

pub fn is_fitness_relation(kind: EdgeKind) -> bool {
    is_selection_topology(kind)
}

/// Return the exact Evidence vertices in the Node's convenient current capture
/// view. `Some(empty)` is authoritative after a rejected or unavailable
/// capture, so historical GroundedBy rows never become current again.
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
struct EvidenceSummary {
    positive: i32,
    counter: i32,
    contributions: Vec<ScoreContribution>,
}

impl EvidenceSummary {
    fn total(&self) -> i32 {
        self.positive + self.counter
    }
}

#[derive(Debug, Clone, Default)]
struct ScoreSummary {
    structural_score: i32,
    evidence: EvidenceSummary,
    conflict_pressure: i32,
    contributions: Vec<ScoreContribution>,
}

impl ScoreSummary {
    fn positive(&self) -> i32 {
        self.structural_score + self.evidence.positive
    }

    fn total(&self) -> i32 {
        self.positive() + self.evidence.counter - self.conflict_pressure
    }
}

#[derive(Debug, Clone)]
struct SupportClause {
    sources: Vec<String>,
    target: String,
    proof_edge_ids: Vec<String>,
    strength: f64,
    realization: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ContractSupport {
    roots: BTreeSet<String>,
    proof_edge_ids: BTreeSet<String>,
}

#[derive(Debug, Clone)]
struct ContractSupportRule {
    sources: Vec<String>,
    target: String,
    proof_edge_ids: BTreeSet<String>,
}

#[derive(Debug, Clone, PartialEq)]
struct StructuralExplanation {
    roots: BTreeSet<String>,
    proof_edge_ids: BTreeSet<String>,
    score: f64,
    realization: bool,
}

#[derive(Debug, Default)]
struct StructuralSolution {
    values: BTreeMap<String, f64>,
    selected: BTreeMap<String, Vec<StructuralExplanation>>,
}

#[derive(Debug, Default)]
struct UnionFind {
    parent: BTreeMap<String, String>,
}

impl UnionFind {
    fn insert(&mut self, id: &str) {
        self.parent
            .entry(id.to_string())
            .or_insert_with(|| id.to_string());
    }

    fn find(&mut self, id: &str) -> String {
        self.insert(id);
        let parent = self.parent[id].clone();
        if parent == id {
            return parent;
        }
        let root = self.find(&parent);
        self.parent.insert(id.to_string(), root.clone());
        root
    }

    fn union(&mut self, left: &str, right: &str) {
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            return;
        }
        let (root, child) = if left_root < right_root {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        self.parent.insert(child, root);
    }
}

pub fn derive_views(
    node_ids: &[String],
    population: &SelectionPopulation,
) -> BTreeMap<String, SelectionView> {
    derive_views_at(node_ids, population, Utc::now())
}

/// Pure time-parameterized entry used by deterministic tests and historical
/// graph views.
pub fn derive_views_at(
    node_ids: &[String],
    population: &SelectionPopulation,
    now: DateTime<Utc>,
) -> BTreeMap<String, SelectionView> {
    let requested: BTreeSet<String> = node_ids.iter().cloned().collect();
    let nodes: BTreeMap<String, &Node> = population
        .nodes
        .iter()
        .map(|node| (node.id.clone(), node))
        .collect();
    let mut specification_ids: BTreeSet<String> = requested.clone();
    specification_ids.extend(nodes.keys().cloned());
    for edge in &population.relation_edges {
        if edge.source_kind == VertexKind::Specification {
            specification_ids.insert(edge.source.clone());
        }
        if edge.target_kind == VertexKind::Specification {
            specification_ids.insert(edge.target.clone());
        }
    }

    let mut specification_classes = UnionFind::default();
    for id in &specification_ids {
        specification_classes.insert(id);
    }
    for edge in &population.relation_edges {
        if edge.kind == EdgeKind::Equivalent
            && edge.source_kind == VertexKind::Specification
            && edge.target_kind == VertexKind::Specification
        {
            specification_classes.union(&edge.source, &edge.target);
        }
    }
    let specification_class: BTreeMap<String, String> = specification_ids
        .iter()
        .map(|id| (id.clone(), specification_classes.find(id)))
        .collect();
    let class_members = grouped_members(&specification_class);
    let class_ids: BTreeSet<String> = class_members.keys().cloned().collect();

    let clauses = compile_support_clauses(
        &population.relation_edges,
        &population.operational_nodes,
        &specification_class,
        &class_ids,
    );
    let structural = solve_structural_support(&class_ids, &clauses);

    let evidence_by_spec: BTreeMap<String, EvidenceSummary> = specification_ids
        .iter()
        .map(|id| {
            let summary = nodes.get(id).map_or_else(EvidenceSummary::default, |node| {
                evidence_summary(
                    node,
                    &population.evidence_edges,
                    &population.evidence_nodes,
                    now,
                )
            });
            (id.clone(), summary)
        })
        .collect();
    let class_evidence: BTreeMap<String, EvidenceSummary> = class_members
        .iter()
        .map(|(class, members)| {
            (
                class.clone(),
                collapsed_evidence(members, &evidence_by_spec),
            )
        })
        .collect();

    let mut class_scores: BTreeMap<String, ScoreSummary> = class_ids
        .iter()
        .map(|class| {
            let structural_points =
                structural_points(*structural.values.get(class).unwrap_or(&0.0));
            let evidence = class_evidence.get(class).cloned().unwrap_or_default();
            let mut contributions = structural_contributions(
                class,
                structural_points,
                structural
                    .selected
                    .get(class)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]),
            );
            contributions.extend(evidence.contributions.iter().cloned());
            (
                class.clone(),
                ScoreSummary {
                    structural_score: structural_points,
                    evidence,
                    contributions,
                    ..ScoreSummary::default()
                },
            )
        })
        .collect();

    apply_conflict_pressure(
        &mut class_scores,
        &population.relation_edges,
        &specification_class,
    );

    let completeness: BTreeMap<String, Result<(), String>> = specification_ids
        .iter()
        .map(|id| {
            let result = nodes.get(id).map_or(Ok(()), |node| graph_complete(node));
            (id.clone(), result)
        })
        .collect();
    let unavailable: BTreeMap<String, bool> = specification_ids
        .iter()
        .map(|id| {
            (
                id.clone(),
                nodes.get(id).is_some_and(|node| evidence_unavailable(node)),
            )
        })
        .collect();

    let equivalent_winners: BTreeMap<String, String> = class_members
        .iter()
        .map(|(class, members)| {
            let winner = members
                .iter()
                .min_by(|left, right| {
                    let left_evidence = evidence_by_spec.get(*left).cloned().unwrap_or_default();
                    let right_evidence = evidence_by_spec.get(*right).cloned().unwrap_or_default();
                    right_evidence
                        .total()
                        .cmp(&left_evidence.total())
                        .then_with(|| left.cmp(right))
                })
                .cloned()
                .unwrap_or_else(|| class.clone());
            (class.clone(), winner)
        })
        .collect();

    let hard_conflicts =
        hard_conflict_adjacency(&population.relation_edges, &specification_class, &class_ids);
    let eligible_classes: BTreeSet<String> = class_ids
        .iter()
        .filter(|class| {
            let Some(score) = class_scores.get(*class) else {
                return false;
            };
            if score.total() < MIN_CURRENT_SCORE {
                return false;
            }
            class_members.get(*class).is_some_and(|members| {
                members.iter().any(|member| {
                    completeness.get(member).is_none_or(Result::is_ok)
                        && !(unavailable.get(member).copied().unwrap_or(false)
                            && score.total() < MIN_CURRENT_SCORE)
                })
            })
        })
        .cloned()
        .collect();
    let weights: BTreeMap<String, i32> = class_scores
        .iter()
        .map(|(class, score)| (class.clone(), score.total().max(0)))
        .collect();
    let selected_classes =
        maximum_weight_consistent_set(&eligible_classes, &hard_conflicts, &weights);

    let mut views = BTreeMap::new();
    for id in requested {
        let class = specification_class
            .get(&id)
            .cloned()
            .unwrap_or_else(|| id.clone());
        let summary = class_scores.get(&class).cloned().unwrap_or_default();
        let mut view = SelectionView {
            policy_version: FITNESS_POLICY_VERSION.into(),
            current: false,
            evaluation_state: EvaluationState::Receded,
            support_score: summary.total(),
            structural_score: summary.structural_score,
            evidence_score: summary.evidence.total(),
            relation_score: summary.structural_score - summary.conflict_pressure,
            conflict_pressure: summary.conflict_pressure,
            contributions: summary.contributions,
            exclusions: Vec::new(),
        };

        if let Some(Err(detail)) = completeness.get(&id) {
            view.evaluation_state = EvaluationState::Unknown;
            view.exclusions.push(SelectionExclusion {
                kind: ExclusionKind::IncompleteGraph,
                edge_id: None,
                competing_node_id: None,
                detail: detail.clone(),
            });
        } else if unavailable.get(&id).copied().unwrap_or(false)
            && view.support_score < MIN_CURRENT_SCORE
        {
            view.evaluation_state = EvaluationState::Unknown;
            view.exclusions.push(SelectionExclusion {
                kind: ExclusionKind::EvidenceUnavailable,
                edge_id: None,
                competing_node_id: None,
                detail: "requested Evidence was unavailable at capture time; the request remains recorded"
                    .into(),
            });
        } else if equivalent_winners
            .get(&class)
            .is_some_and(|winner| winner != &id)
        {
            view.exclusions.push(SelectionExclusion {
                kind: ExclusionKind::EquivalentDuplicate,
                edge_id: equivalent_edge_for(&id, &population.relation_edges),
                competing_node_id: equivalent_winners.get(&class).cloned(),
                detail: format!(
                    "equivalent specifications are one fitness population; '{}' is its representative",
                    equivalent_winners[&class]
                ),
            });
        } else if view.support_score < MIN_CURRENT_SCORE {
            view.exclusions.push(SelectionExclusion {
                kind: if view.evidence_score < 0 {
                    ExclusionKind::Counterevidence
                } else {
                    ExclusionKind::InsufficientSupport
                },
                edge_id: None,
                competing_node_id: None,
                detail: format!(
                    "fitness {} is below the current-set threshold {MIN_CURRENT_SCORE}",
                    view.support_score
                ),
            });
        } else if !selected_classes.contains(&class) {
            let blocker = hard_conflicts
                .get(&class)
                .into_iter()
                .flatten()
                .filter(|candidate| selected_classes.contains(*candidate))
                .max_by_key(|candidate| (weights.get(*candidate).copied().unwrap_or(0), *candidate))
                .cloned();
            view.exclusions.push(SelectionExclusion {
                kind: ExclusionKind::Contradicted,
                edge_id: blocker
                    .as_ref()
                    .and_then(|other| conflict_edge_for(&class, other, &population.relation_edges, &specification_class)),
                competing_node_id: blocker.clone(),
                detail: blocker.map_or_else(
                    || "a higher-fitness hard-conflict set was selected".into(),
                    |other| format!("hard-conflicting specification '{other}' belongs to the maximum-fitness coherent set"),
                ),
            });
        } else {
            view.current = true;
            view.evaluation_state = EvaluationState::Current;
        }
        view.sort_and_dedup();
        views.insert(id, view);
    }
    views
}

fn grouped_members(classes: &BTreeMap<String, String>) -> BTreeMap<String, Vec<String>> {
    let mut result: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (id, class) in classes {
        result.entry(class.clone()).or_default().push(id.clone());
    }
    result
}

fn compile_support_clauses(
    edges: &[Edge],
    operational_nodes: &[DerivedNode],
    specification_class: &BTreeMap<String, String>,
    class_ids: &BTreeSet<String>,
) -> Vec<SupportClause> {
    let mut contract_classes = UnionFind::default();
    for edge in edges {
        if edge.source_kind == VertexKind::Contract {
            contract_classes.insert(&edge.source);
        }
        if edge.target_kind == VertexKind::Contract {
            contract_classes.insert(&edge.target);
        }
        if edge.kind == EdgeKind::ContractEquivalent {
            contract_classes.union(&edge.source, &edge.target);
        }
    }

    let mut owners: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut owner_supports: BTreeMap<String, Vec<ContractSupport>> = BTreeMap::new();
    let mut contract_refinements = Vec::new();
    let mut clauses = Vec::new();

    for edge in edges {
        match edge.kind {
            EdgeKind::Refines
            | EdgeKind::OccurrenceReliance
            | EdgeKind::GuaranteeDischarge
            | EdgeKind::AdmissibilityEnvelope
                if edge.source_kind == VertexKind::Specification
                    && edge.target_kind == VertexKind::Specification =>
            {
                let Some(source) = specification_class.get(&edge.source) else {
                    continue;
                };
                let Some(target) = specification_class.get(&edge.target) else {
                    continue;
                };
                if source != target {
                    clauses.push(SupportClause {
                        sources: vec![source.clone()],
                        target: target.clone(),
                        proof_edge_ids: vec![edge.id.clone()],
                        strength: 1.0,
                        realization: false,
                    });
                }
            }
            EdgeKind::HasContract => {
                let Some(owner) = specification_class.get(&edge.source) else {
                    continue;
                };
                let contract = contract_classes.find(&edge.target);
                owners
                    .entry(contract.clone())
                    .or_default()
                    .insert(owner.clone());
                insert_contract_support(
                    owner_supports.entry(contract).or_default(),
                    ContractSupport {
                        roots: BTreeSet::from([owner.clone()]),
                        proof_edge_ids: BTreeSet::from([edge.id.clone()]),
                    },
                );
            }
            EdgeKind::ContractRefines => {
                let source = contract_classes.find(&edge.source);
                let target = contract_classes.find(&edge.target);
                if source != target {
                    contract_refinements.push((source, target, edge.id.clone()));
                }
            }
            _ => {}
        }
    }

    let mut contract_rules: Vec<ContractSupportRule> = contract_refinements
        .iter()
        .map(|(source, target, edge_id)| ContractSupportRule {
            sources: vec![source.clone()],
            target: target.clone(),
            proof_edge_ids: BTreeSet::from([edge_id.clone()]),
        })
        .collect();
    contract_rules.extend(
        crate::store::contract_operations(edges)
            .into_iter()
            .map(|operation| ContractSupportRule {
                sources: operation
                    .operands
                    .into_iter()
                    .map(|operand| contract_classes.find(&operand))
                    .collect(),
                target: contract_classes.find(&operation.result),
                proof_edge_ids: operation.proof_edge_ids.into_iter().collect(),
            }),
    );
    for rule in &mut contract_rules {
        rule.sources.sort();
        rule.sources.dedup();
    }
    contract_rules.sort_by(|left, right| {
        (&left.target, &left.sources, &left.proof_edge_ids).cmp(&(
            &right.target,
            &right.sources,
            &right.proof_edge_ids,
        ))
    });
    contract_rules.dedup_by(|left, right| {
        left.target == right.target
            && left.sources == right.sources
            && left.proof_edge_ids == right.proof_edge_ids
    });
    let contract_support = solve_contract_support(owner_supports, &contract_rules);

    // Every proof that reaches an authored Contract supports its owner.
    // This includes a binary operation whose content-addressed result is the
    // owner's Contract itself; such a proof must not need a synthetic
    // self-refinement Edge. Refinement rules have already carried their proof
    // Edge ids through the fixed point.
    for (target_contract, target_owners) in &owners {
        let Some(supports) = contract_support.get(target_contract) else {
            continue;
        };
        for support in supports {
            for target in target_owners {
                // A proof group that needs its own conclusion is circular.
                // Removing the target from that AND-set would be unsound:
                // it would turn `{target, source}` into an apparent
                // single-source proof. Reject the whole group instead.
                if support.roots.contains(target) {
                    continue;
                }
                let mut sources: Vec<String> = support
                    .roots
                    .iter()
                    .filter(|source| class_ids.contains(*source))
                    .cloned()
                    .collect();
                sources.sort();
                sources.dedup();
                if !sources.is_empty() {
                    clauses.push(SupportClause {
                        sources,
                        target: target.clone(),
                        proof_edge_ids: support.proof_edge_ids.iter().cloned().collect(),
                        strength: 1.0,
                        realization: false,
                    });
                }
            }
        }
    }

    clauses.extend(compile_realization_support_clauses(
        edges,
        operational_nodes,
        specification_class,
        class_ids,
    ));

    let mut deduplicated: BTreeMap<(Vec<String>, String), SupportClause> = BTreeMap::new();
    for mut clause in clauses {
        clause.sources.sort();
        clause.sources.dedup();
        clause.proof_edge_ids.sort();
        clause.proof_edge_ids.dedup();
        let key = (clause.sources.clone(), clause.target.clone());
        deduplicated
            .entry(key)
            .and_modify(|existing| {
                existing.strength = (existing.strength + clause.strength).min(1.0);
                existing.realization &= clause.realization;
                existing
                    .proof_edge_ids
                    .extend(clause.proof_edge_ids.clone());
                existing.proof_edge_ids.sort();
                existing.proof_edge_ids.dedup();
            })
            .or_insert(clause);
    }
    deduplicated.into_values().collect()
}

fn solve_contract_support(
    mut support: BTreeMap<String, Vec<ContractSupport>>,
    rules: &[ContractSupportRule],
) -> BTreeMap<String, Vec<ContractSupport>> {
    loop {
        let snapshot = support.clone();
        let mut changed = false;
        for rule in rules {
            for candidate in contract_rule_supports(rule, &snapshot) {
                changed |= insert_contract_support(
                    support.entry(rule.target.clone()).or_default(),
                    candidate,
                );
            }
        }
        if !changed {
            return support;
        }
    }
}

fn contract_rule_supports(
    rule: &ContractSupportRule,
    support: &BTreeMap<String, Vec<ContractSupport>>,
) -> Vec<ContractSupport> {
    let mut combinations = vec![ContractSupport {
        roots: BTreeSet::new(),
        proof_edge_ids: rule.proof_edge_ids.clone(),
    }];
    for source in &rule.sources {
        let Some(options) = support.get(source) else {
            return Vec::new();
        };
        let mut next = Vec::new();
        for existing in &combinations {
            for option in options {
                let mut combined = existing.clone();
                combined.roots.extend(option.roots.iter().cloned());
                combined
                    .proof_edge_ids
                    .extend(option.proof_edge_ids.iter().cloned());
                insert_contract_support(&mut next, combined);
            }
        }
        combinations = next;
    }
    combinations
}

fn insert_contract_support(
    supports: &mut Vec<ContractSupport>,
    candidate: ContractSupport,
) -> bool {
    let changed;
    if let Some(existing) = supports
        .iter_mut()
        .find(|existing| existing.roots == candidate.roots)
    {
        if candidate.proof_edge_ids < existing.proof_edge_ids {
            *existing = candidate;
            changed = true;
        } else {
            return false;
        }
    } else if !supports
        .iter()
        .any(|existing| existing.roots.is_subset(&candidate.roots))
    {
        supports.retain(|existing| !candidate.roots.is_subset(&existing.roots));
        supports.push(candidate);
        changed = true;
    } else {
        return false;
    }
    supports.sort_by(|left, right| {
        left.roots
            .cmp(&right.roots)
            .then_with(|| left.proof_edge_ids.cmp(&right.proof_edge_ids))
    });
    changed
}

#[derive(Debug, Clone)]
struct RealizationCandidate {
    source: String,
    target: String,
    proof_edge_ids: Vec<String>,
    strength: f64,
    basis: so_reason::operational::RealizationBasis,
}

#[derive(Debug, Clone)]
struct EntityCompositionCandidate {
    source: String,
    target: String,
    proof_edge_ids: Vec<String>,
    strength: f64,
    basis: so_reason::operational::EntityCompositionBasis,
    entity: so_reason::operational::EntityRef,
}

/// Discover lower-layer→upper-layer realization and composition from persisted
/// operational profiles.
///
/// An exact action match and compatible actor/object roles produce candidates
/// in `so-reason`. The view starts with `ExplicitMeans` candidates and expands
/// toward more concrete layers only when an `ObjectRefinement` targets an
/// already anchored class. Independently, an affirmative binding object's
/// exact Entity may be elaborated by a lower specification that governs it as
/// its subject or continued by one that reacts to it as a trigger. The latter
/// relation requires both persisted operational role Edges; Means and guards
/// never establish it. This prevents a lexical, untyped Entity, or object-shape
/// match from becoming support in isolation.
fn compile_realization_support_clauses(
    edges: &[Edge],
    operational_nodes: &[DerivedNode],
    specification_class: &BTreeMap<String, String>,
    class_ids: &BTreeSet<String>,
) -> Vec<SupportClause> {
    use so_reason::operational::{
        assess_entity_composition, assess_layered_realization, EngagementSite, RealizationBasis,
    };

    let profiles: BTreeMap<String, so_reason::operational::OperationalProfile> = operational_nodes
        .iter()
        .filter_map(|node| {
            node.operational_profile()
                .filter(|profile| profile.claim.is_some())
                .map(|profile| (node.id().to_string(), profile))
        })
        .collect();
    if profiles.is_empty() {
        return Vec::new();
    }

    let mut owners: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    for edge in edges
        .iter()
        .filter(|edge| edge.kind == EdgeKind::HasBehavior)
    {
        let Some(class) = specification_class.get(&edge.source) else {
            continue;
        };
        if class_ids.contains(class) && profiles.contains_key(&edge.target) {
            owners
                .entry(edge.target.clone())
                .or_default()
                .insert(class.clone(), edge.id.clone());
        }
    }

    let mut role_proofs: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    let mut exact_role_proofs: BTreeMap<(String, String, String, EdgeKind), BTreeSet<String>> =
        BTreeMap::new();
    for edge in edges.iter().filter(|edge| {
        matches!(
            edge.kind,
            EdgeKind::WitnessesEntity | EdgeKind::EngagesEntity
        )
    }) {
        for basis in &edge.basis_spec_ids {
            let Some(class) = specification_class.get(basis) else {
                continue;
            };
            role_proofs
                .entry((edge.source.clone(), class.clone()))
                .or_default()
                .insert(edge.id.clone());
            exact_role_proofs
                .entry((
                    edge.source.clone(),
                    edge.target.clone(),
                    class.clone(),
                    edge.kind,
                ))
                .or_default()
                .insert(edge.id.clone());
        }
    }
    let entity_ids: BTreeMap<(String, String), String> = operational_nodes
        .iter()
        .filter_map(|node| match node {
            DerivedNode::Entity { id, full, head, .. } => {
                Some(((full.clone(), head.clone()), id.clone()))
            }
            _ => None,
        })
        .collect();

    let mut by_action: BTreeMap<Vec<String>, Vec<String>> = BTreeMap::new();
    for (behavior, profile) in &profiles {
        let Some(claim) = &profile.claim else {
            continue;
        };
        if owners.contains_key(behavior) {
            by_action
                .entry(claim.action.clone())
                .or_default()
                .push(behavior.clone());
        }
    }

    let mut candidates = Vec::new();
    for behavior_ids in by_action.values() {
        for source_behavior in behavior_ids {
            for target_behavior in behavior_ids {
                if source_behavior == target_behavior {
                    continue;
                }
                let Some(relation) = assess_layered_realization(
                    &profiles[source_behavior],
                    &profiles[target_behavior],
                ) else {
                    continue;
                };
                let Some(source_owners) = owners.get(source_behavior) else {
                    continue;
                };
                let Some(target_owners) = owners.get(target_behavior) else {
                    continue;
                };
                for (source, source_owner_edge) in source_owners {
                    for (target, target_owner_edge) in target_owners {
                        if source == target {
                            continue;
                        }
                        let mut proofs =
                            BTreeSet::from([source_owner_edge.clone(), target_owner_edge.clone()]);
                        proofs.extend(
                            role_proofs
                                .get(&(source_behavior.clone(), source.clone()))
                                .into_iter()
                                .flatten()
                                .cloned(),
                        );
                        proofs.extend(
                            role_proofs
                                .get(&(target_behavior.clone(), target.clone()))
                                .into_iter()
                                .flatten()
                                .cloned(),
                        );
                        candidates.push(RealizationCandidate {
                            source: source.clone(),
                            target: target.clone(),
                            proof_edge_ids: proofs.into_iter().collect(),
                            strength: relation.strength,
                            basis: relation.basis,
                        });
                    }
                }
            }
        }
    }
    candidates.sort_by(|left, right| {
        (&left.target, &left.source, left.basis).cmp(&(&right.target, &right.source, right.basis))
    });

    let mut anchored = BTreeSet::new();
    let mut clauses = Vec::new();
    for candidate in candidates
        .iter()
        .filter(|candidate| candidate.basis == RealizationBasis::ExplicitMeans)
    {
        anchored.insert(candidate.source.clone());
        clauses.push(realization_clause(candidate));
    }

    let mut admitted = BTreeSet::new();
    loop {
        let mut changed = false;
        for (index, candidate) in candidates
            .iter()
            .enumerate()
            .filter(|(_, candidate)| candidate.basis == RealizationBasis::ObjectRefinement)
        {
            if admitted.contains(&index) || !anchored.contains(&candidate.target) {
                continue;
            }
            admitted.insert(index);
            changed |= anchored.insert(candidate.source.clone());
            clauses.push(realization_clause(candidate));
        }
        if !changed {
            break;
        }
    }

    let mut upper_by_entity: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    let mut lower_by_entity: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    for (behavior, profile) in &profiles {
        if !owners.contains_key(behavior) {
            continue;
        }
        for witness in &profile.witnesses {
            upper_by_entity
                .entry((witness.entity.full.clone(), witness.entity.head.clone()))
                .or_default()
                .insert(behavior.clone());
        }
        for engagement in profile.engagements.iter().filter(|engagement| {
            matches!(
                engagement.site,
                EngagementSite::Subject | EngagementSite::Trigger
            )
        }) {
            lower_by_entity
                .entry((
                    engagement.entity.full.clone(),
                    engagement.entity.head.clone(),
                ))
                .or_default()
                .insert(behavior.clone());
        }
    }

    let mut composition_candidates = Vec::new();
    for (entity_key, upper_behaviors) in &upper_by_entity {
        let Some(lower_behaviors) = lower_by_entity.get(entity_key) else {
            continue;
        };
        let Some(entity_id) = entity_ids.get(entity_key) else {
            continue;
        };
        for lower_behavior in lower_behaviors {
            for upper_behavior in upper_behaviors {
                if lower_behavior == upper_behavior {
                    continue;
                }
                let relations =
                    assess_entity_composition(&profiles[lower_behavior], &profiles[upper_behavior]);
                if relations.is_empty() {
                    continue;
                }
                let Some(lower_owners) = owners.get(lower_behavior) else {
                    continue;
                };
                let Some(upper_owners) = owners.get(upper_behavior) else {
                    continue;
                };
                for (source, lower_owner_edge) in lower_owners {
                    for (target, upper_owner_edge) in upper_owners {
                        if source == target {
                            continue;
                        }
                        let Some(lower_role_edges) = exact_role_proofs.get(&(
                            lower_behavior.clone(),
                            entity_id.clone(),
                            source.clone(),
                            EdgeKind::EngagesEntity,
                        )) else {
                            continue;
                        };
                        let Some(upper_role_edges) = exact_role_proofs.get(&(
                            upper_behavior.clone(),
                            entity_id.clone(),
                            target.clone(),
                            EdgeKind::WitnessesEntity,
                        )) else {
                            continue;
                        };
                        for relation in &relations {
                            if (relation.entity.full.as_str(), relation.entity.head.as_str())
                                != (entity_key.0.as_str(), entity_key.1.as_str())
                            {
                                continue;
                            }
                            let mut proofs = BTreeSet::new();
                            proofs.extend(lower_role_edges.iter().cloned());
                            proofs.extend(upper_role_edges.iter().cloned());
                            proofs.insert(lower_owner_edge.clone());
                            proofs.insert(upper_owner_edge.clone());
                            composition_candidates.push(EntityCompositionCandidate {
                                source: source.clone(),
                                target: target.clone(),
                                proof_edge_ids: proofs.into_iter().collect(),
                                strength: relation.strength,
                                basis: relation.basis,
                                entity: relation.entity.clone(),
                            });
                        }
                    }
                }
            }
        }
    }
    composition_candidates.sort_by(|left, right| {
        (&left.target, &left.source, left.basis, &left.entity).cmp(&(
            &right.target,
            &right.source,
            right.basis,
            &right.entity,
        ))
    });
    composition_candidates.dedup_by(|left, right| {
        left.source == right.source
            && left.target == right.target
            && left.basis == right.basis
            && left.entity.full == right.entity.full
            && left.entity.head == right.entity.head
    });
    clauses.extend(composition_candidates.iter().map(entity_composition_clause));
    clauses
}

fn realization_clause(candidate: &RealizationCandidate) -> SupportClause {
    SupportClause {
        sources: vec![candidate.source.clone()],
        target: candidate.target.clone(),
        proof_edge_ids: candidate.proof_edge_ids.clone(),
        strength: candidate.strength,
        realization: true,
    }
}

fn entity_composition_clause(candidate: &EntityCompositionCandidate) -> SupportClause {
    SupportClause {
        sources: vec![candidate.source.clone()],
        target: candidate.target.clone(),
        proof_edge_ids: candidate.proof_edge_ids.clone(),
        strength: candidate.strength,
        realization: true,
    }
}

fn solve_structural_support(
    class_ids: &BTreeSet<String>,
    clauses: &[SupportClause],
) -> StructuralSolution {
    let mut explanations: BTreeMap<String, Vec<StructuralExplanation>> = class_ids
        .iter()
        .map(|id| {
            (
                id.clone(),
                vec![StructuralExplanation {
                    roots: BTreeSet::from([id.clone()]),
                    proof_edge_ids: BTreeSet::new(),
                    score: STRUCTURAL_ADMISSION_PRIOR,
                    realization: false,
                }],
            )
        })
        .collect();
    let mut dependents: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    for (index, clause) in clauses.iter().enumerate() {
        for source in &clause.sources {
            dependents.entry(source.clone()).or_default().insert(index);
        }
    }
    let mut pending: BTreeSet<usize> = (0..clauses.len()).collect();
    while let Some(index) = pending.pop_first() {
        let clause = &clauses[index];
        let candidates = clause_explanations(clause, &explanations);
        let target = explanations.entry(clause.target.clone()).or_default();
        let mut target_changed = false;
        for candidate in candidates {
            target_changed |= insert_explanation(target, candidate);
        }
        if target_changed {
            pending.extend(
                dependents
                    .get(&clause.target)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
    }

    let mut solution = StructuralSolution::default();
    for id in class_ids {
        let derived: Vec<StructuralExplanation> = explanations
            .get(id)
            .into_iter()
            .flatten()
            .filter(|explanation| !explanation.proof_edge_ids.is_empty())
            .cloned()
            .collect();
        let selected = independent_explanations(derived);
        let value = selected.iter().fold(0.0, |combined, explanation| {
            1.0 - (1.0 - combined) * (1.0 - explanation.score.clamp(0.0, 1.0))
        });
        solution.values.insert(id.clone(), value);
        solution.selected.insert(id.clone(), selected);
    }
    solution
}

fn clause_explanations(
    clause: &SupportClause,
    explanations: &BTreeMap<String, Vec<StructuralExplanation>>,
) -> Vec<StructuralExplanation> {
    let mut combinations = vec![StructuralExplanation {
        roots: BTreeSet::new(),
        proof_edge_ids: BTreeSet::new(),
        score: 1.0,
        realization: false,
    }];
    for source in &clause.sources {
        let Some(options) = explanations.get(source) else {
            return Vec::new();
        };
        let mut next = Vec::new();
        for existing in &combinations {
            for option in options {
                let mut combined = existing.clone();
                combined.roots.extend(option.roots.iter().cloned());
                combined
                    .proof_edge_ids
                    .extend(option.proof_edge_ids.iter().cloned());
                combined.score = combined.score.min(option.score);
                combined.realization |= option.realization;
                insert_explanation(&mut next, combined);
            }
        }
        combinations = next;
        if combinations.is_empty() {
            return Vec::new();
        }
    }
    let clause_edges: BTreeSet<String> = clause.proof_edge_ids.iter().cloned().collect();
    combinations
        .into_iter()
        .filter_map(|mut explanation| {
            if explanation.roots.contains(&clause.target) {
                return None;
            }
            explanation
                .proof_edge_ids
                .extend(clause_edges.iter().cloned());
            explanation.score *= clause.strength;
            explanation.realization |= clause.realization;
            (explanation.score > 0.0).then_some(explanation)
        })
        .collect()
}

fn insert_explanation(
    explanations: &mut Vec<StructuralExplanation>,
    candidate: StructuralExplanation,
) -> bool {
    const EPSILON: f64 = 1.0e-12;
    let changed;
    if let Some(existing) = explanations
        .iter_mut()
        .find(|existing| existing.roots == candidate.roots)
    {
        if candidate.score > existing.score + EPSILON
            || ((candidate.score - existing.score).abs() <= EPSILON
                && candidate.proof_edge_ids < existing.proof_edge_ids)
        {
            *existing = candidate;
            changed = true;
        } else {
            return false;
        }
    } else if !explanations.iter().any(|existing| {
        existing.roots.is_subset(&candidate.roots) && existing.score + EPSILON >= candidate.score
    }) {
        explanations.retain(|existing| {
            !(candidate.roots.is_subset(&existing.roots)
                && candidate.score + EPSILON >= existing.score)
        });
        explanations.push(candidate);
        changed = true;
    } else {
        return false;
    }
    explanations.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| left.roots.len().cmp(&right.roots.len()))
            .then_with(|| left.roots.cmp(&right.roots))
            .then_with(|| left.proof_edge_ids.cmp(&right.proof_edge_ids))
    });
    changed
}

fn independent_explanations(
    mut candidates: Vec<StructuralExplanation>,
) -> Vec<StructuralExplanation> {
    candidates.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| left.roots.len().cmp(&right.roots.len()))
            .then_with(|| left.roots.cmp(&right.roots))
            .then_with(|| left.proof_edge_ids.cmp(&right.proof_edge_ids))
    });
    let mut all_roots = BTreeSet::new();
    if candidates.iter().all(|candidate| {
        candidate.roots.is_disjoint(&all_roots) && {
            all_roots.extend(candidate.roots.iter().cloned());
            true
        }
    }) {
        return candidates;
    }
    let mut best = Vec::new();
    search_independent_explanations(
        &candidates,
        0,
        &mut BTreeSet::new(),
        &mut Vec::new(),
        &mut best,
    );
    best
}

fn search_independent_explanations(
    candidates: &[StructuralExplanation],
    index: usize,
    covered: &mut BTreeSet<String>,
    chosen: &mut Vec<StructuralExplanation>,
    best: &mut Vec<StructuralExplanation>,
) {
    const EPSILON: f64 = 1.0e-12;
    let current = combined_explanation_score(chosen);
    let optimistic = candidates[index..]
        .iter()
        .fold(current, |combined, explanation| {
            1.0 - (1.0 - combined) * (1.0 - explanation.score.clamp(0.0, 1.0))
        });
    if optimistic + EPSILON < combined_explanation_score(best) {
        return;
    }
    if index == candidates.len() {
        let best_score = combined_explanation_score(best);
        if current > best_score + EPSILON
            || ((current - best_score).abs() <= EPSILON
                && explanation_selection_key(chosen) < explanation_selection_key(best))
        {
            *best = chosen.clone();
        }
        return;
    }

    let candidate = &candidates[index];
    if candidate.roots.is_disjoint(covered) {
        covered.extend(candidate.roots.iter().cloned());
        chosen.push(candidate.clone());
        search_independent_explanations(candidates, index + 1, covered, chosen, best);
        chosen.pop();
        for root in &candidate.roots {
            covered.remove(root);
        }
    }
    search_independent_explanations(candidates, index + 1, covered, chosen, best);
}

fn combined_explanation_score(explanations: &[StructuralExplanation]) -> f64 {
    explanations.iter().fold(0.0, |combined, explanation| {
        1.0 - (1.0 - combined) * (1.0 - explanation.score.clamp(0.0, 1.0))
    })
}

fn explanation_selection_key(
    explanations: &[StructuralExplanation],
) -> Vec<(BTreeSet<String>, BTreeSet<String>, bool)> {
    let mut key: Vec<_> = explanations
        .iter()
        .map(|explanation| {
            (
                explanation.roots.clone(),
                explanation.proof_edge_ids.clone(),
                explanation.realization,
            )
        })
        .collect();
    key.sort();
    key
}

fn structural_points(value: f64) -> i32 {
    (value.clamp(0.0, 1.0) * f64::from(MAX_STRUCTURAL_SCORE)).round() as i32
}

fn structural_contributions(
    _target: &str,
    total_points: i32,
    explanations: &[StructuralExplanation],
) -> Vec<ScoreContribution> {
    if total_points <= 0 || explanations.is_empty() {
        return Vec::new();
    }
    let total_activation: f64 = explanations.iter().map(|item| item.score).sum();
    if total_activation <= 0.0 {
        return Vec::new();
    }
    let mut remaining = total_points;
    explanations
        .iter()
        .enumerate()
        .map(|(index, explanation)| {
            let points = if index + 1 == explanations.len() {
                remaining
            } else {
                let allocated =
                    (f64::from(total_points) * explanation.score / total_activation).round() as i32;
                remaining -= allocated;
                allocated
            };
            ScoreContribution {
                kind: if explanation.realization {
                    ScoreContributionKind::RealizationSupport
                } else {
                    ScoreContributionKind::StructuralSupport
                },
                points,
                edge_id: explanation
                    .proof_edge_ids
                    .iter()
                    .next()
                    .cloned()
                    .unwrap_or_else(|| "typed-support-path".into()),
                source_node_id: (explanation.roots.len() == 1)
                    .then(|| explanation.roots.iter().next().cloned())
                    .flatten(),
                evidence_node_id: None,
                detail: format!(
                    "independent {} proof rooted at [{}] contributes {points} point(s)",
                    if explanation.realization {
                        "realization"
                    } else {
                        "logical"
                    },
                    explanation
                        .roots
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                path_edge_ids: Vec::new(),
            }
        })
        .filter(|contribution| contribution.points != 0)
        .collect()
}

fn evidence_summary(
    node: &Node,
    evidence_edges: &[Edge],
    evidence_nodes: &[DerivedNode],
    now: DateTime<Utc>,
) -> EvidenceSummary {
    let edge_by_evidence: BTreeMap<String, &Edge> = evidence_edges
        .iter()
        .filter(|edge| edge.source == node.id && edge.kind == EdgeKind::GroundedBy)
        .map(|edge| (edge.target.clone(), edge))
        .collect();
    let mut owned_evidence = node.meta.evidence.clone();
    // Legacy rows and low-level store tests may have Ledger GroundedBy facts
    // without the later authoritative capture-state marker. Preserve that
    // documented fallback, but never revive history after Some(empty).
    if current_evidence_node_ids(node).is_none() {
        let by_id: BTreeMap<&str, &DerivedNode> = evidence_nodes
            .iter()
            .map(|derived| (derived.id(), derived))
            .collect();
        for edge in evidence_edges
            .iter()
            .filter(|edge| edge.source == node.id && edge.kind == EdgeKind::GroundedBy)
        {
            let Some(DerivedNode::Evidence { evidence, .. }) =
                by_id.get(edge.target.as_str()).copied()
            else {
                continue;
            };
            let mut evidence = evidence.clone();
            if evidence.snapshot.captured_at.is_empty() {
                evidence.snapshot.captured_at = edge.recorded_at.clone();
            }
            owned_evidence.push(evidence);
        }
    }
    let mut latest: BTreeMap<String, &crate::domain::Evidence> = BTreeMap::new();
    for evidence in &owned_evidence {
        let locator = evidence.locator.render();
        let replace = latest.get(&locator).is_none_or(|existing| {
            (
                &evidence.snapshot.captured_at,
                &evidence.snapshot.content_hash,
            ) > (
                &existing.snapshot.captured_at,
                &existing.snapshot.content_hash,
            )
        });
        if replace {
            latest.insert(locator, evidence);
        }
    }
    let mut evidence_by_id: BTreeMap<String, crate::domain::Evidence> = evidence_nodes
        .iter()
        .filter_map(|node| match node {
            DerivedNode::Evidence { id, evidence } => Some((id.clone(), evidence.clone())),
            _ => None,
        })
        .collect();
    let mut captured_at = BTreeMap::new();
    let mut grounding_roots = Vec::new();
    for evidence in latest.into_values() {
        let derived = DerivedNode::evidence(evidence.clone());
        let evidence_id = derived.id().to_string();
        evidence_by_id.insert(evidence_id.clone(), evidence.clone());
        captured_at.insert(evidence_id.clone(), evidence.snapshot.captured_at.clone());
        let edge_id = edge_by_evidence
            .get(&evidence_id)
            .map(|edge| edge.id.clone())
            .unwrap_or_else(|| format!("grounding:{evidence_id}"));
        let sign = if evidence.kind == Kind::Counter {
            -1
        } else {
            1
        };
        grounding_roots.push((evidence_id, edge_id, sign));
    }
    for edge in evidence_edges.iter().filter(|edge| {
        edge.source_kind == VertexKind::Evidence
            && matches!(
                edge.kind,
                EdgeKind::EvidenceAffirms | EdgeKind::EvidenceDenies
            )
    }) {
        captured_at
            .entry(edge.source.clone())
            .and_modify(|existing| {
                if edge.recorded_at < *existing {
                    *existing = edge.recorded_at.clone();
                }
            })
            .or_insert_with(|| edge.recorded_at.clone());
    }
    let mut incoming: BTreeMap<String, Vec<&Edge>> = BTreeMap::new();
    for edge in evidence_edges.iter().filter(|edge| {
        edge.target_kind == VertexKind::Evidence
            && matches!(
                edge.kind,
                EdgeKind::EvidenceAffirms | EdgeKind::EvidenceDenies
            )
    }) {
        incoming.entry(edge.target.clone()).or_default().push(edge);
    }
    for edges in incoming.values_mut() {
        edges.sort_by_key(|edge| &edge.id);
    }

    let mut roots = grounding_roots;
    roots.extend(
        evidence_edges
            .iter()
            .filter(|edge| {
                edge.target == node.id
                    && edge.target_kind == VertexKind::Specification
                    && matches!(
                        edge.kind,
                        EdgeKind::EvidenceAffirms | EdgeKind::EvidenceDenies
                    )
            })
            .map(|edge| {
                (
                    edge.source.clone(),
                    edge.id.clone(),
                    if edge.kind == EdgeKind::EvidenceAffirms {
                        1
                    } else {
                        -1
                    },
                )
            }),
    );

    let mut positive = Vec::new();
    let mut counter = Vec::new();
    for (root, edge_id, sign) in roots {
        for contribution in evidence_path_contributions(
            node,
            &root,
            &edge_id,
            sign,
            &evidence_by_id,
            &captured_at,
            &incoming,
            now,
        ) {
            if contribution.points < 0 {
                counter.push(contribution);
            } else {
                positive.push(contribution);
            }
        }
    }
    positive.sort_by(|left, right| {
        right
            .points
            .cmp(&left.points)
            .then_with(|| left.edge_id.cmp(&right.edge_id))
    });
    counter.sort_by(|left, right| {
        left.points
            .cmp(&right.points)
            .then_with(|| left.edge_id.cmp(&right.edge_id))
    });
    cap_contributions(&mut positive, MAX_POSITIVE_EVIDENCE_SCORE);
    cap_contributions(&mut counter, MAX_COUNTER_EVIDENCE_SCORE);
    EvidenceSummary {
        positive: positive.iter().map(|item| item.points).sum(),
        counter: counter.iter().map(|item| item.points).sum(),
        contributions: positive.into_iter().chain(counter).collect(),
    }
}

fn evidence_path_contributions(
    node: &Node,
    root: &str,
    terminal_edge_id: &str,
    root_sign: i32,
    evidence_by_id: &BTreeMap<String, crate::domain::Evidence>,
    captured_at: &BTreeMap<String, String>,
    incoming: &BTreeMap<String, Vec<&Edge>>,
    now: DateTime<Utc>,
) -> Vec<ScoreContribution> {
    use std::collections::VecDeque;

    let mut queue = VecDeque::from([(
        root.to_string(),
        root_sign,
        vec![terminal_edge_id.to_string()],
    )]);
    // One shortest path per (Evidence, polarity) gives cyclic graphs a finite,
    // deterministic meaning while retaining both independently signed routes.
    let mut shortest: BTreeMap<(String, i32), usize> = BTreeMap::new();
    let mut contributions = Vec::new();
    while let Some((evidence_id, sign, path)) = queue.pop_front() {
        let state = (evidence_id.clone(), sign);
        if shortest
            .get(&state)
            .is_some_and(|known| *known <= path.len())
        {
            continue;
        }
        shortest.insert(state, path.len());
        let Some(evidence) = evidence_by_id.get(&evidence_id) else {
            continue;
        };
        let captured = captured_at
            .get(&evidence_id)
            .map(String::as_str)
            .filter(|value| !value.is_empty())
            .unwrap_or_default();
        let magnitude = decayed_evidence_points(evidence.kind, captured, now).abs();
        let points = sign * magnitude;
        if points != 0 {
            contributions.push(ScoreContribution {
                kind: if points < 0 {
                    ScoreContributionKind::CounterEvidence
                } else {
                    evidence_contribution_kind(evidence.kind)
                },
                points,
                edge_id: terminal_edge_id.to_string(),
                source_node_id: Some(node.id.clone()),
                evidence_node_id: Some(evidence_id.clone()),
                detail: format!(
                    "{} Evidence at {} contributes {points} point(s) through {}",
                    evidence.kind.as_str(),
                    evidence.locator.render(),
                    path.join(" -> ")
                ),
                path_edge_ids: path.clone(),
            });
        }
        for edge in incoming.get(&evidence_id).into_iter().flatten().copied() {
            let next_sign = if edge.kind == EdgeKind::EvidenceAffirms {
                sign
            } else {
                -sign
            };
            let mut next_path = Vec::with_capacity(path.len() + 1);
            next_path.push(edge.id.clone());
            next_path.extend(path.iter().cloned());
            queue.push_back((edge.source.clone(), next_sign, next_path));
        }
    }
    contributions
}

fn cap_contributions(contributions: &mut [ScoreContribution], cap: i32) {
    let negative = contributions.first().is_some_and(|item| item.points < 0);
    let mut remaining = cap;
    for contribution in contributions {
        let magnitude = contribution.points.abs().min(remaining);
        contribution.points = if negative { -magnitude } else { magnitude };
        remaining -= magnitude;
    }
}

fn decayed_evidence_points(kind: Kind, captured_at: &str, now: DateTime<Utc>) -> i32 {
    let base = match kind {
        Kind::Demonstrative => 20,
        Kind::Constitutive => 18,
        Kind::Testimonial => 14,
        Kind::Assertoric => 10,
        Kind::Circumstantial => 6,
        Kind::Unknown => 2,
        Kind::Counter => -20,
    };
    let age_days = DateTime::parse_from_rfc3339(captured_at)
        .ok()
        .map(|captured| {
            (now.signed_duration_since(captured.with_timezone(&Utc))
                .num_seconds()
                .max(0) as f64)
                / 86_400.0
        })
        .unwrap_or_default();
    let decay = 2.0_f64.powf(-age_days / EVIDENCE_HALF_LIFE_DAYS);
    (f64::from(base) * decay).round() as i32
}

fn evidence_contribution_kind(kind: Kind) -> ScoreContributionKind {
    match kind {
        Kind::Constitutive => ScoreContributionKind::ConstitutiveEvidence,
        Kind::Demonstrative => ScoreContributionKind::DemonstrativeEvidence,
        Kind::Testimonial => ScoreContributionKind::TestimonialEvidence,
        Kind::Assertoric => ScoreContributionKind::AssertoricEvidence,
        Kind::Circumstantial => ScoreContributionKind::CircumstantialEvidence,
        Kind::Counter => ScoreContributionKind::CounterEvidence,
        Kind::Unknown => ScoreContributionKind::UnknownEvidence,
    }
}

fn collapsed_evidence(
    members: &[String],
    evidence: &BTreeMap<String, EvidenceSummary>,
) -> EvidenceSummary {
    let positive = members
        .iter()
        .filter_map(|member| evidence.get(member))
        .max_by_key(|summary| summary.positive)
        .cloned()
        .unwrap_or_default();
    let counter = members
        .iter()
        .filter_map(|member| evidence.get(member))
        .min_by_key(|summary| summary.counter)
        .cloned()
        .unwrap_or_default();
    EvidenceSummary {
        positive: positive.positive,
        counter: counter.counter,
        contributions: positive
            .contributions
            .into_iter()
            .filter(|item| item.points >= 0)
            .chain(
                counter
                    .contributions
                    .into_iter()
                    .filter(|item| item.points < 0),
            )
            .collect(),
    }
}

fn apply_conflict_pressure(
    scores: &mut BTreeMap<String, ScoreSummary>,
    edges: &[Edge],
    specification_class: &BTreeMap<String, String>,
) {
    let mut signals: BTreeMap<String, Vec<(String, String, f64)>> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    for edge in edges {
        let coefficient = match edge.kind {
            EdgeKind::HardContradiction => 1.0,
            EdgeKind::EnvelopeConflict => 0.75,
            EdgeKind::DescriptiveConflict => 0.50,
            EdgeKind::AdvisoryTension => 0.25,
            _ => continue,
        };
        let Some(left) = specification_class.get(&edge.source) else {
            continue;
        };
        let Some(right) = specification_class.get(&edge.target) else {
            continue;
        };
        if left == right {
            continue;
        }
        let pair = if left < right {
            (left.clone(), right.clone(), edge.kind.as_str())
        } else {
            (right.clone(), left.clone(), edge.kind.as_str())
        };
        if !seen.insert(pair) {
            continue;
        }
        signals.entry(left.clone()).or_default().push((
            right.clone(),
            edge.id.clone(),
            coefficient,
        ));
        signals.entry(right.clone()).or_default().push((
            left.clone(),
            edge.id.clone(),
            coefficient,
        ));
    }
    let positives: BTreeMap<String, i32> = scores
        .iter()
        .map(|(id, score)| (id.clone(), score.positive()))
        .collect();
    for (id, score) in scores.iter_mut() {
        let mut survival = 1.0;
        let mut raw = Vec::new();
        for (competitor, edge_id, coefficient) in signals.get(id).into_iter().flatten() {
            let competitor_strength =
                f64::from(positives.get(competitor).copied().unwrap_or(0).max(0)) / 100.0;
            let signal = (coefficient * competitor_strength).clamp(0.0, 1.0);
            survival *= 1.0 - signal;
            raw.push((competitor.clone(), edge_id.clone(), signal));
        }
        let penalty = (f64::from(score.positive().max(0)) * (1.0 - survival)).round() as i32;
        score.conflict_pressure = penalty;
        if penalty > 0 {
            let total_signal: f64 = raw.iter().map(|(_, _, signal)| *signal).sum();
            let mut remaining = penalty;
            for (index, (competitor, edge_id, signal)) in raw.iter().enumerate() {
                let points = if index + 1 == raw.len() {
                    remaining
                } else if total_signal > 0.0 {
                    let allocated = (f64::from(penalty) * signal / total_signal).round() as i32;
                    remaining -= allocated;
                    allocated
                } else {
                    0
                };
                if points != 0 {
                    score.contributions.push(ScoreContribution {
                        kind: ScoreContributionKind::ConflictPressure,
                        points: -points,
                        edge_id: edge_id.clone(),
                        source_node_id: Some(competitor.clone()),
                        evidence_node_id: None,
                        detail: format!(
                            "conflict pressure from '{competitor}' subtracts {points} point(s)"
                        ),
                        path_edge_ids: Vec::new(),
                    });
                }
            }
        }
    }
}

fn graph_complete(node: &Node) -> Result<(), String> {
    if node.lang_version != so_lang::LANG_VERSION {
        return Err(format!(
            "language version '{}' is not current '{}'",
            node.lang_version,
            so_lang::LANG_VERSION
        ));
    }
    let term_complete = node.meta.updates.values().any(|update| {
        (update.source == "term-projection"
            && update
                .value
                .get("method")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::TERM_DERIVATION_METHOD)
            && update
                .value
                .get("version")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::GENERATION_VERSION))
            || (update.source == "graph-generation"
                && update
                    .value
                    .pointer("/term_generation/method")
                    .and_then(serde_json::Value::as_str)
                    == Some(crate::graph_generation::TERM_DERIVATION_METHOD)
                && update
                    .value
                    .pointer("/term_generation/version")
                    .and_then(serde_json::Value::as_str)
                    == Some(crate::graph_generation::GENERATION_VERSION))
    });
    let contract_complete = node.meta.updates.values().any(|update| {
        (update.source == "contract-projection"
            && update
                .value
                .get("method")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::CONTRACT_PROJECTION_METHOD)
            && update
                .value
                .get("version")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::CONTRACT_PROJECTION_VERSION))
            || (update.source == "graph-generation"
                && update
                    .value
                    .pointer("/contract_projection/method")
                    .and_then(serde_json::Value::as_str)
                    == Some(crate::graph_generation::CONTRACT_PROJECTION_METHOD)
                && update
                    .value
                    .pointer("/contract_projection/version")
                    .and_then(serde_json::Value::as_str)
                    == Some(crate::graph_generation::CONTRACT_PROJECTION_VERSION))
    });
    let operational = crate::graph_generation::operational_projection_derivation();
    let operational_complete = node.meta.updates.values().any(|update| {
        (update.source == "term-projection"
            && update
                .value
                .get("operational_method")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::OPERATIONAL_PROJECTION_METHOD)
            && update
                .value
                .get("operational_version")
                .and_then(serde_json::Value::as_str)
                == Some(operational.version.as_str()))
            || (update.source == "graph-generation"
                && update
                    .value
                    .pointer("/operational_projection/method")
                    .and_then(serde_json::Value::as_str)
                    == Some(crate::graph_generation::OPERATIONAL_PROJECTION_METHOD)
                && update
                    .value
                    .pointer("/operational_projection/version")
                    .and_then(serde_json::Value::as_str)
                    == Some(operational.version.as_str()))
    });
    let semantic_edge = crate::graph_generation::semantic_edge_derivation();
    let lexical_edge = crate::graph_generation::lexical_affinity_derivation();
    let semantic_complete = node.meta.updates.values().any(|update| {
        (update.source == "semantic-relation"
            && update
                .value
                .get("edge_method")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::SEMANTIC_EDGE_METHOD)
            && update
                .value
                .get("edge_version")
                .and_then(serde_json::Value::as_str)
                == Some(semantic_edge.version.as_str())
            && update
                .value
                .get("candidate_method")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::CANDIDATE_METHOD)
            && update
                .value
                .get("candidate_version")
                .and_then(serde_json::Value::as_str)
                == Some(crate::graph_generation::CANDIDATE_VERSION)
            && update
                .value
                .get("lexical_edge_version")
                .and_then(serde_json::Value::as_str)
                == Some(lexical_edge.version.as_str()))
            || (update.source == "graph-generation"
                && update
                    .value
                    .pointer("/semantic_relations/method")
                    .and_then(serde_json::Value::as_str)
                    == Some(crate::graph_generation::SEMANTIC_EDGE_METHOD)
                && update
                    .value
                    .pointer("/semantic_relations/version")
                    .and_then(serde_json::Value::as_str)
                    == Some(semantic_edge.version.as_str()))
    });
    let mut missing = Vec::new();
    if !term_complete {
        missing.push("term projection");
    }
    if !contract_complete {
        missing.push("contract projection");
    }
    if !operational_complete {
        missing.push("operational projection");
    }
    if !semantic_complete {
        missing.push("semantic relation assessment");
    }
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "current graph derivation is incomplete: missing {}",
            missing.join(", ")
        ))
    }
}

fn evidence_unavailable(node: &Node) -> bool {
    if node.meta.evidence_requests.is_empty() || !node.meta.evidence.is_empty() {
        return false;
    }
    node.meta
        .updates
        .values()
        .filter(|update| update.source == crate::evidence_capture::PLUGIN_NAME)
        .max_by_key(|update| (&update.applied_at, &update.source))
        .and_then(|update| update.value.get("status"))
        .and_then(serde_json::Value::as_str)
        .is_some_and(|status| status == "unavailable")
}

fn hard_conflict_adjacency(
    edges: &[Edge],
    specification_class: &BTreeMap<String, String>,
    classes: &BTreeSet<String>,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut result: BTreeMap<String, BTreeSet<String>> = classes
        .iter()
        .map(|id| (id.clone(), BTreeSet::new()))
        .collect();
    for edge in edges
        .iter()
        .filter(|edge| edge.kind == EdgeKind::HardContradiction)
    {
        let Some(left) = specification_class.get(&edge.source) else {
            continue;
        };
        let Some(right) = specification_class.get(&edge.target) else {
            continue;
        };
        if left != right {
            result
                .entry(left.clone())
                .or_default()
                .insert(right.clone());
            result
                .entry(right.clone())
                .or_default()
                .insert(left.clone());
        }
    }
    result
}

fn maximum_weight_consistent_set(
    eligible: &BTreeSet<String>,
    adjacency: &BTreeMap<String, BTreeSet<String>>,
    weights: &BTreeMap<String, i32>,
) -> BTreeSet<String> {
    let mut selected = BTreeSet::new();
    let mut unseen = eligible.clone();
    while let Some(seed) = unseen.iter().next().cloned() {
        let mut component = BTreeSet::new();
        let mut frontier = vec![seed];
        while let Some(node) = frontier.pop() {
            if !unseen.remove(&node) || !component.insert(node.clone()) {
                continue;
            }
            for neighbor in adjacency.get(&node).into_iter().flatten() {
                if unseen.contains(neighbor) {
                    frontier.push(neighbor.clone());
                }
            }
        }
        if component.len() == 1 {
            selected.extend(component);
        } else {
            let mut best = (i32::MIN, BTreeSet::new());
            search_independent_set(component, BTreeSet::new(), 0, adjacency, weights, &mut best);
            selected.extend(best.1);
        }
    }
    selected
}

fn search_independent_set(
    remaining: BTreeSet<String>,
    chosen: BTreeSet<String>,
    score: i32,
    adjacency: &BTreeMap<String, BTreeSet<String>>,
    weights: &BTreeMap<String, i32>,
    best: &mut (i32, BTreeSet<String>),
) {
    let upper_bound = score
        + remaining
            .iter()
            .map(|id| weights.get(id).copied().unwrap_or_default().max(0))
            .sum::<i32>();
    if upper_bound < best.0 {
        return;
    }
    let Some(candidate) = remaining
        .iter()
        .max_by_key(|id| adjacency.get(*id).map_or(0, BTreeSet::len))
        .cloned()
    else {
        if score > best.0 || (score == best.0 && chosen < best.1) {
            *best = (score, chosen);
        }
        return;
    };
    let mut without = remaining.clone();
    without.remove(&candidate);
    search_independent_set(
        without.clone(),
        chosen.clone(),
        score,
        adjacency,
        weights,
        best,
    );
    let mut with_remaining = without;
    if let Some(neighbors) = adjacency.get(&candidate) {
        for neighbor in neighbors {
            with_remaining.remove(neighbor);
        }
    }
    let mut with_chosen = chosen;
    with_chosen.insert(candidate.clone());
    search_independent_set(
        with_remaining,
        with_chosen,
        score + weights.get(&candidate).copied().unwrap_or_default(),
        adjacency,
        weights,
        best,
    );
}

fn equivalent_edge_for(id: &str, edges: &[Edge]) -> Option<String> {
    edges
        .iter()
        .filter(|edge| edge.kind == EdgeKind::Equivalent)
        .filter(|edge| edge.source == id || edge.target == id)
        .map(|edge| edge.id.clone())
        .min()
}

fn conflict_edge_for(
    left_class: &str,
    right_class: &str,
    edges: &[Edge],
    classes: &BTreeMap<String, String>,
) -> Option<String> {
    edges
        .iter()
        .filter(|edge| edge.kind == EdgeKind::HardContradiction)
        .filter(|edge| {
            let source = classes.get(&edge.source).map(String::as_str);
            let target = classes.get(&edge.target).map(String::as_str);
            (source == Some(left_class) && target == Some(right_class))
                || (source == Some(right_class) && target == Some(left_class))
        })
        .map(|edge| edge.id.clone())
        .min()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{
        Anchor, Derivation, Evidence, Locator, Meta, MetaUpdate, Origin, Snapshot,
    };
    use serde_json::json;

    fn at(value: &str) -> DateTime<Utc> {
        DateTime::parse_from_rfc3339(value)
            .unwrap()
            .with_timezone(&Utc)
    }

    fn complete_node(id: &str, evidence: Vec<Evidence>) -> Node {
        let semantic = crate::graph_generation::semantic_edge_derivation();
        let updates = BTreeMap::from([
            (
                "term".into(),
                MetaUpdate {
                    source: "term-projection".into(),
                    applied_at: "2026-01-01T00:00:00Z".into(),
                    value: json!({
                        "method": crate::graph_generation::TERM_DERIVATION_METHOD,
                        "version": crate::graph_generation::GENERATION_VERSION,
                        "operational_method": crate::graph_generation::OPERATIONAL_PROJECTION_METHOD,
                        "operational_version": crate::graph_generation::operational_projection_derivation().version,
                    }),
                },
            ),
            (
                "contract".into(),
                MetaUpdate {
                    source: "contract-projection".into(),
                    applied_at: "2026-01-01T00:00:00Z".into(),
                    value: json!({
                        "method": crate::graph_generation::CONTRACT_PROJECTION_METHOD,
                        "version": crate::graph_generation::CONTRACT_PROJECTION_VERSION,
                    }),
                },
            ),
            (
                "semantic".into(),
                MetaUpdate {
                    source: "semantic-relation".into(),
                    applied_at: "2026-01-01T00:00:00Z".into(),
                    value: json!({
                        "candidate_method": crate::graph_generation::CANDIDATE_METHOD,
                        "candidate_version": crate::graph_generation::CANDIDATE_VERSION,
                        "lexical_edge_method": crate::graph_generation::LEXICAL_AFFINITY_METHOD,
                        "lexical_edge_version": crate::graph_generation::lexical_affinity_derivation().version,
                        "edge_method": crate::graph_generation::SEMANTIC_EDGE_METHOD,
                        "edge_version": semantic.version,
                    }),
                },
            ),
        ]);
        Node {
            id: id.into(),
            statement: "The system shall behave.".into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: evidence.iter().map(|item| item.locator.render()).collect(),
                evidence_request_generation: "generation".into(),
                evidence,
                created_at: "2026-01-01T00:00:00Z".into(),
                cli: "test".into(),
                cli_version: "test".into(),
                updates,
            },
        }
    }

    fn evidence(kind: Kind, locator: &str, captured_at: &str) -> Evidence {
        Evidence {
            kind,
            locator: Locator::parse(locator),
            snapshot: Snapshot {
                content: String::new(),
                content_hash: format!("hash-{locator}"),
                bytes: 1,
                captured_at: captured_at.into(),
                anchor: Anchor::Worktree,
            },
            origin: Origin::default(),
        }
    }

    fn relation(kind: EdgeKind, source: &str, target: &str) -> Edge {
        Edge::specification_relation(
            kind,
            source,
            target,
            vec![],
            Derivation {
                method: "test".into(),
                version: "v1".into(),
            },
            "2026-01-01T00:00:00Z",
        )
        .unwrap()
    }

    fn connector(kind: EdgeKind, source: &str, target: &str) -> Edge {
        if kind == EdgeKind::MentionsTerm {
            let mut edge = Edge {
                id: String::new(),
                source: source.into(),
                source_kind: VertexKind::Specification,
                source_role: crate::domain::EndpointRole::Mentioner,
                target: target.into(),
                target_kind: VertexKind::Term,
                target_role: crate::domain::EndpointRole::MentionedTerm,
                kind,
                source_anchor: None,
                target_anchor: None,
                relied_spec_id: None,
                basis_spec_ids: Vec::new(),
                derivation: Derivation {
                    method: "test-connector".into(),
                    version: "v1".into(),
                },
                recorded_at: "2026-01-01T00:00:00Z".into(),
            };
            edge.id = edge.identity_key();
            return edge;
        }
        Edge::projection(
            kind,
            source,
            target,
            Derivation {
                method: "test-connector".into(),
                version: "v1".into(),
            },
            "2026-01-01T00:00:00Z",
        )
        .unwrap()
    }

    fn population(nodes: Vec<Node>, relation_edges: Vec<Edge>) -> SelectionPopulation {
        let mut evidence_edges = Vec::new();
        let mut evidence_nodes = Vec::new();
        for node in &nodes {
            for item in &node.meta.evidence {
                let derived = DerivedNode::evidence(item.clone());
                evidence_edges.push(
                    Edge::projection(
                        EdgeKind::GroundedBy,
                        &node.id,
                        derived.id(),
                        crate::evidence_capture::evidence_derivation(),
                        &item.snapshot.captured_at,
                    )
                    .unwrap(),
                );
                evidence_nodes.push(derived);
            }
        }
        SelectionPopulation {
            nodes,
            relation_edges,
            operational_nodes: Vec::new(),
            evidence_edges,
            evidence_nodes,
        }
    }

    fn operational_population(specifications: &[(&str, &str)]) -> SelectionPopulation {
        let mut nodes = Vec::new();
        let mut relation_edges = Vec::new();
        let mut operational_nodes = BTreeMap::new();
        let derivation = crate::graph_generation::operational_projection_derivation();
        for (id, statement) in specifications {
            let mut node = complete_node(id, Vec::new());
            node.statement = (*statement).into();
            let parsed = so_lang::parse::parse(statement).unwrap();
            let profile = so_reason::operational::operational_profile(&parsed.sentences[0]);
            let behavior =
                DerivedNode::behavior(&profile, so_reason::operational::OPERATIONAL_VERSION);
            relation_edges.push(
                Edge::projection(
                    EdgeKind::HasBehavior,
                    id,
                    behavior.id(),
                    derivation.clone(),
                    "2026-01-01T00:00:00Z",
                )
                .unwrap(),
            );
            for (kind, entity) in profile
                .witnesses
                .iter()
                .map(|item| (EdgeKind::WitnessesEntity, &item.entity))
                .chain(
                    profile
                        .engagements
                        .iter()
                        .map(|item| (EdgeKind::EngagesEntity, &item.entity)),
                )
            {
                let entity =
                    DerivedNode::entity(entity, so_reason::operational::OPERATIONAL_VERSION);
                let mut edge = Edge::operational_role(
                    kind,
                    behavior.id(),
                    entity.id(),
                    derivation.clone(),
                    "2026-01-01T00:00:00Z",
                )
                .unwrap();
                edge.basis_spec_ids = vec![(*id).to_string()];
                edge.id = edge.identity_key();
                edge.validate().unwrap();
                relation_edges.push(edge);
                operational_nodes.insert(entity.id().to_string(), entity);
            }
            operational_nodes.insert(behavior.id().to_string(), behavior);
            nodes.push(node);
        }
        relation_edges.sort_by(|left, right| left.id.cmp(&right.id));
        relation_edges.dedup_by(|left, right| left.id == right.id);
        SelectionPopulation {
            nodes,
            relation_edges,
            operational_nodes: operational_nodes.into_values().collect(),
            evidence_edges: Vec::new(),
            evidence_nodes: Vec::new(),
        }
    }

    #[test]
    fn layered_realization_recursively_supports_the_upper_specification() {
        let graph = operational_population(&[
            (
                "rpc",
                "The Add RPC shall accept exactly one constrained-language specification sentence.",
            ),
            (
                "operation",
                "The `spec add` operation shall accept exactly one language sentence.",
            ),
            (
                "system",
                "The system shall accept a constrained natural-language specification through `spec add`.",
            ),
        ]);
        let views = derive_views_at(&["system".into()], &graph, at("2026-01-01T00:00:00Z"));
        let view = &views["system"];
        assert!(view.structural_score > 0);
        assert!(view.contributions.iter().any(|contribution| {
            contribution.kind == ScoreContributionKind::RealizationSupport
                && contribution.source_node_id.as_deref() == Some("rpc")
        }));
        assert!(view.contributions.iter().any(|contribution| {
            contribution.kind == ScoreContributionKind::RealizationSupport
                && contribution.source_node_id.as_deref() == Some("operation")
        }));
    }

    #[test]
    fn realization_requires_the_explicitly_anchored_middle_layer() {
        let without_middle = operational_population(&[
            (
                "rpc",
                "The Add RPC shall accept exactly one constrained-language specification sentence.",
            ),
            (
                "system",
                "The system shall accept a constrained natural-language specification through `spec add`.",
            ),
        ]);
        let views = derive_views_at(
            &["system".into()],
            &without_middle,
            at("2026-01-01T00:00:00Z"),
        );
        assert_eq!(views["system"].structural_score, 0);
        assert!(views["system"].contributions.is_empty());
    }

    #[test]
    fn unanchored_object_similarity_is_not_realization_support() {
        let graph = operational_population(&[
            (
                "specific",
                "The report service shall accept exactly one signed report.",
            ),
            ("general", "The service shall accept exactly one report."),
        ]);
        let views = derive_views_at(&["general".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert_eq!(views["general"].structural_score, 0);
        assert!(views["general"].contributions.is_empty());
    }

    #[test]
    fn exact_entity_roles_compose_support_across_different_actions() {
        let graph = operational_population(&[
            (
                "rpc",
                "an AddSpecification RPC shall submit an AddNode Command.",
            ),
            (
                "command",
                "the AddNode Command shall cause a NodeAdded Event.",
            ),
            (
                "consumer",
                "When a NodeAdded Event is delivered, the term projection Consumer shall submit a ProjectNodeTerms Command.",
            ),
        ]);

        let views = derive_views_at(&["rpc".into()], &graph, at("2026-01-01T00:00:00Z"));
        let view = &views["rpc"];

        assert!(view.structural_score > 0);
        assert!(view.contributions.iter().any(|contribution| {
            contribution.kind == ScoreContributionKind::RealizationSupport
                && contribution.source_node_id.as_deref() == Some("command")
        }));
        assert!(view.contributions.iter().any(|contribution| {
            contribution.kind == ScoreContributionKind::RealizationSupport
                && contribution.source_node_id.as_deref() == Some("consumer")
        }));
    }

    #[test]
    fn independent_subject_and_trigger_elaborations_both_support_the_target() {
        let graph = operational_population(&[
            ("upper", "The daemon shall create a report."),
            ("subject", "The report shall contain a summary."),
            (
                "trigger",
                "When a report is ready, the publisher shall emit a notification.",
            ),
        ]);

        let views = derive_views_at(&["upper".into()], &graph, at("2026-01-01T00:00:00Z"));
        let sources: BTreeSet<_> = views["upper"]
            .contributions
            .iter()
            .filter(|contribution| contribution.kind == ScoreContributionKind::RealizationSupport)
            .filter_map(|contribution| contribution.source_node_id.as_deref())
            .collect();

        assert_eq!(sources, BTreeSet::from(["subject", "trigger"]));
    }

    #[test]
    fn means_and_guard_entity_sharing_do_not_contribute_support() {
        let graph = operational_population(&[
            ("upper", "The daemon shall create a report."),
            ("means", "The renderer shall display a page using a report."),
            (
                "guard",
                "While a report is ready, the renderer shall display a page.",
            ),
        ]);

        let views = derive_views_at(&["upper".into()], &graph, at("2026-01-01T00:00:00Z"));

        assert_eq!(views["upper"].structural_score, 0);
        assert!(views["upper"].contributions.is_empty());
    }

    #[test]
    fn entity_composition_requires_both_persisted_role_edges() {
        let graph = operational_population(&[
            ("upper", "The daemon shall create a report."),
            ("lower", "The report shall contain a summary."),
        ]);

        let complete = derive_views_at(&["upper".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert!(complete["upper"].structural_score > 0);

        for missing_kind in [EdgeKind::WitnessesEntity, EdgeKind::EngagesEntity] {
            let mut incomplete = graph.clone();
            incomplete
                .relation_edges
                .retain(|edge| edge.kind != missing_kind);
            let views = derive_views_at(&["upper".into()], &incomplete, at("2026-01-01T00:00:00Z"));

            assert_eq!(
                views["upper"].structural_score, 0,
                "{missing_kind:?} is a required graph proof, not a replaceable shared Entity hint"
            );
            assert!(views["upper"].contributions.is_empty());
        }
    }

    #[test]
    fn evidence_is_a_decaying_external_term() {
        let node = complete_node(
            "candidate",
            vec![evidence(
                Kind::Assertoric,
                "README.md:1",
                "2026-01-01T00:00:00Z",
            )],
        );
        let graph = population(vec![node], vec![]);
        let fresh = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));
        let old = derive_views_at(&["candidate".into()], &graph, at("2027-01-01T00:00:00Z"));
        assert_eq!(fresh["candidate"].evidence_score, 10);
        assert!(fresh["candidate"].current);
        assert_eq!(old["candidate"].evidence_score, 0);
        assert!(!old["candidate"].current);
    }

    #[test]
    fn evidence_denial_cancels_an_obsolete_affirmation_and_can_itself_be_denied() {
        let old_evidence = DerivedNode::evidence(evidence(
            Kind::Assertoric,
            "old-release.md",
            "2026-01-01T00:00:00Z",
        ));
        let correction = DerivedNode::evidence(evidence(
            Kind::Assertoric,
            "current-release.md",
            "2026-01-01T00:00:00Z",
        ));
        let correction_retraction = DerivedNode::evidence(evidence(
            Kind::Assertoric,
            "retraction.md",
            "2026-01-01T00:00:00Z",
        ));
        let affirm = Edge::evidence_relation(
            EdgeKind::EvidenceAffirms,
            old_evidence.id(),
            "candidate",
            VertexKind::Specification,
            crate::evidence_graph::derivation(),
            "2026-01-01T00:00:00Z",
        )
        .unwrap();
        let deny = Edge::evidence_relation(
            EdgeKind::EvidenceDenies,
            correction.id(),
            old_evidence.id(),
            VertexKind::Evidence,
            crate::evidence_graph::derivation(),
            "2026-01-01T00:00:00Z",
        )
        .unwrap();
        let deny_the_denial = Edge::evidence_relation(
            EdgeKind::EvidenceDenies,
            correction_retraction.id(),
            correction.id(),
            VertexKind::Evidence,
            crate::evidence_graph::derivation(),
            "2026-01-01T00:00:00Z",
        )
        .unwrap();
        let mut graph = SelectionPopulation {
            nodes: vec![complete_node("candidate", vec![])],
            evidence_edges: vec![affirm.clone()],
            evidence_nodes: vec![
                old_evidence.clone(),
                correction.clone(),
                correction_retraction.clone(),
            ],
            ..SelectionPopulation::default()
        };
        let affirmed = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert_eq!(affirmed["candidate"].evidence_score, 10);
        assert!(affirmed["candidate"].current);

        graph.evidence_edges.push(deny.clone());
        let denied = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert_eq!(denied["candidate"].evidence_score, 0);
        assert!(!denied["candidate"].current);
        assert!(denied["candidate"]
            .contributions
            .iter()
            .any(|contribution| {
                contribution.evidence_node_id.as_deref() == Some(correction.id())
                    && contribution.points == -10
                    && contribution.path_edge_ids == vec![deny.id.clone(), affirm.id.clone()]
            }));

        graph.evidence_edges.push(deny_the_denial.clone());
        let restored = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert_eq!(restored["candidate"].evidence_score, 10);
        assert!(restored["candidate"].current);
        assert!(restored["candidate"]
            .contributions
            .iter()
            .any(|contribution| {
                contribution.evidence_node_id.as_deref() == Some(correction_retraction.id())
                    && contribution.points == 10
                    && contribution.path_edge_ids
                        == vec![
                            deny_the_denial.id.clone(),
                            deny.id.clone(),
                            affirm.id.clone(),
                        ]
            }));
    }

    #[test]
    fn refinement_supports_the_abstraction_without_removing_either_layer() {
        let concrete = complete_node(
            "concrete",
            vec![evidence(Kind::Assertoric, "c", "2026-01-01T00:00:00Z")],
        );
        let abstract_ = complete_node(
            "abstract",
            vec![evidence(Kind::Assertoric, "a", "2026-01-01T00:00:00Z")],
        );
        let graph = population(
            vec![concrete, abstract_],
            vec![relation(EdgeKind::Refines, "concrete", "abstract")],
        );
        let views = derive_views_at(
            &["concrete".into(), "abstract".into()],
            &graph,
            at("2026-01-01T00:00:00Z"),
        );
        assert!(views["concrete"].current);
        assert!(views["abstract"].current);
        assert!(views["abstract"].structural_score > 0);
        assert_eq!(views["concrete"].structural_score, 0);
    }

    #[test]
    fn structural_cycles_are_bounded_and_do_not_need_evidence_as_their_source() {
        let graph = population(
            vec![complete_node("a", vec![]), complete_node("b", vec![])],
            vec![
                relation(EdgeKind::Refines, "a", "b"),
                relation(EdgeKind::Refines, "b", "a"),
            ],
        );
        let views = derive_views_at(
            &["a".into(), "b".into()],
            &graph,
            at("2026-01-01T00:00:00Z"),
        );
        assert!(views["a"].structural_score > 0);
        assert!(views["a"].structural_score <= MAX_STRUCTURAL_SCORE);
        assert!(views["a"].current);
        assert_eq!(views["a"].structural_score, views["b"].structural_score);
    }

    #[test]
    fn lexical_and_projection_identity_are_not_support_without_a_proof() {
        let lexical_edges: Vec<Edge> = (0..5)
            .flat_map(|index| {
                let term = format!("term-{index}");
                [
                    connector(EdgeKind::MentionsTerm, "a", &term),
                    connector(EdgeKind::MentionsTerm, "b", &term),
                ]
            })
            .collect();
        let lexical = population(
            vec![complete_node("a", vec![]), complete_node("b", vec![])],
            lexical_edges,
        );
        let lexical_views = derive_views_at(
            &["a".into(), "b".into()],
            &lexical,
            at("2026-01-01T00:00:00Z"),
        );
        assert_eq!(lexical_views["a"].structural_score, 0);

        let guarantee = population(
            vec![complete_node("a", vec![]), complete_node("b", vec![])],
            vec![
                connector(EdgeKind::HasGuarantee, "a", "guarantee"),
                connector(EdgeKind::HasGuarantee, "b", "guarantee"),
            ],
        );
        let guarantee_views = derive_views_at(
            &["a".into(), "b".into()],
            &guarantee,
            at("2026-01-01T00:00:00Z"),
        );
        assert_eq!(guarantee_views["a"].structural_score, 0);
        assert_eq!(guarantee_views["b"].structural_score, 0);
    }

    #[test]
    fn a_shared_upstream_root_is_counted_once_across_branches() {
        let ids = ["root", "left", "right", "target"]
            .into_iter()
            .map(str::to_string)
            .collect();
        let clauses = vec![
            SupportClause {
                sources: vec!["root".into()],
                target: "left".into(),
                proof_edge_ids: vec!["root-left".into()],
                strength: 1.0,
                realization: false,
            },
            SupportClause {
                sources: vec!["root".into()],
                target: "right".into(),
                proof_edge_ids: vec!["root-right".into()],
                strength: 1.0,
                realization: false,
            },
            SupportClause {
                sources: vec!["left".into()],
                target: "target".into(),
                proof_edge_ids: vec!["left-target".into()],
                strength: 1.0,
                realization: false,
            },
            SupportClause {
                sources: vec!["right".into()],
                target: "target".into(),
                proof_edge_ids: vec!["right-target".into()],
                strength: 1.0,
                realization: false,
            },
        ];
        let solution = solve_structural_support(&ids, &clauses);
        assert_eq!(
            solution.selected["target"]
                .iter()
                .filter(|explanation| explanation.roots == BTreeSet::from(["root".into()]))
                .count(),
            1,
            "the root path branches twice but has one provenance set"
        );
        assert_eq!(
            solution.selected["target"].len(),
            3,
            "the independently authored left and right specifications retain their own priors"
        );
    }

    #[test]
    fn independent_roots_increase_support_without_linear_path_counting() {
        let ids = ["a", "b", "target"]
            .into_iter()
            .map(str::to_string)
            .collect();
        let clauses = vec![
            SupportClause {
                sources: vec!["a".into()],
                target: "target".into(),
                proof_edge_ids: vec!["a-target".into()],
                strength: 1.0,
                realization: false,
            },
            SupportClause {
                sources: vec!["b".into()],
                target: "target".into(),
                proof_edge_ids: vec!["b-target".into()],
                strength: 1.0,
                realization: false,
            },
        ];
        let solution = solve_structural_support(&ids, &clauses);
        assert_eq!(solution.selected["target"].len(), 2);
        assert!(solution.values["target"] > STRUCTURAL_ADMISSION_PRIOR);
        assert!(solution.values["target"] < STRUCTURAL_ADMISSION_PRIOR * 2.0);
    }

    #[test]
    fn contract_support_fixed_point_keeps_every_recursive_alternative() {
        let derivation = Derivation {
            method: "test-contract-proof".into(),
            version: "v1".into(),
        };
        let mut edges = Vec::new();
        let mut specification_class = BTreeMap::new();
        let mut class_ids = BTreeSet::new();
        for leaf in 0..7 {
            for alternative in ["a", "b"] {
                let owner = format!("root-{leaf}-{alternative}");
                specification_class.insert(owner.clone(), owner.clone());
                class_ids.insert(owner.clone());
                edges.push(
                    Edge::projection(
                        EdgeKind::HasContract,
                        &owner,
                        &format!("leaf-{leaf}"),
                        derivation.clone(),
                        "2026-01-01T00:00:00Z",
                    )
                    .unwrap(),
                );
            }
        }
        specification_class.insert("target".into(), "target".into());
        class_ids.insert("target".into());

        let mut result = "leaf-0".to_string();
        for leaf in 1..7 {
            let next = format!("composition-{leaf}");
            let basis = vec![format!("operation-{leaf}")];
            for operand in [result.clone(), format!("leaf-{leaf}")] {
                edges.push(
                    Edge::contract_relation(
                        EdgeKind::CompositionOperand,
                        &operand,
                        &next,
                        basis.clone(),
                        derivation.clone(),
                        "2026-01-01T00:00:00Z",
                    )
                    .unwrap(),
                );
            }
            result = next;
        }
        edges.push(
            Edge::projection(
                EdgeKind::HasContract,
                "target",
                &result,
                derivation,
                "2026-01-01T00:00:00Z",
            )
            .unwrap(),
        );

        let clauses = compile_support_clauses(&edges, &[], &specification_class, &class_ids);
        let target_clauses: BTreeSet<Vec<String>> = clauses
            .into_iter()
            .filter(|clause| clause.target == "target")
            .map(|clause| clause.sources)
            .collect();
        assert_eq!(
            target_clauses.len(),
            128,
            "seven independent binary alternatives produce all 2^7 minimal proof roots"
        );
        assert!(target_clauses.iter().all(|sources| sources.len() == 7));
    }

    #[test]
    fn structural_fixed_point_has_no_depth_or_explanation_count_cutoff() {
        let depth = 140;
        let target = format!("n-{depth:03}");
        let ids = BTreeSet::from(["n-000".to_string(), target.clone()]);
        let clauses: Vec<SupportClause> = (0..depth)
            .rev()
            .map(|index| SupportClause {
                sources: vec![format!("n-{index:03}")],
                target: format!("n-{:03}", index + 1),
                proof_edge_ids: vec![format!("edge-{index:03}")],
                strength: 1.0,
                realization: false,
            })
            .collect();

        let solution = solve_structural_support(&ids, &clauses);
        assert!(solution.selected[&target]
            .iter()
            .any(|explanation| { explanation.roots == BTreeSet::from(["n-000".to_string()]) }));
    }

    #[test]
    fn structural_fixed_point_keeps_more_than_sixteen_independent_roots() {
        let mut ids = BTreeSet::from(["target".to_string()]);
        let clauses: Vec<SupportClause> = (0..20)
            .map(|index| {
                let source = format!("root-{index:02}");
                ids.insert(source.clone());
                SupportClause {
                    sources: vec![source],
                    target: "target".into(),
                    proof_edge_ids: vec![format!("edge-{index:02}")],
                    strength: 1.0,
                    realization: false,
                }
            })
            .collect();

        let solution = solve_structural_support(&ids, &clauses);
        assert_eq!(solution.selected["target"].len(), 20);
    }

    #[test]
    fn independent_explanation_selection_is_globally_optimal() {
        let explanation = |roots: &[&str], edge: &str, score: f64| StructuralExplanation {
            roots: roots.iter().map(|root| (*root).to_string()).collect(),
            proof_edge_ids: BTreeSet::from([edge.to_string()]),
            score,
            realization: false,
        };
        let selected = independent_explanations(vec![
            explanation(&["a", "b"], "combined", 0.90),
            explanation(&["a"], "a", 0.70),
            explanation(&["b"], "b", 0.70),
        ]);

        assert_eq!(selected.len(), 2);
        assert!((combined_explanation_score(&selected) - 0.91).abs() < 1.0e-12);
        assert!(selected
            .iter()
            .all(|item| item.proof_edge_ids != BTreeSet::from(["combined".to_string()])));
    }

    #[test]
    fn evidence_selection_does_not_drop_the_fifth_source() {
        let evidence = (0..5)
            .map(|index| {
                evidence(
                    Kind::Unknown,
                    &format!("source-{index}"),
                    "2026-01-01T00:00:00Z",
                )
            })
            .collect();
        let graph = population(vec![complete_node("candidate", evidence)], vec![]);
        let views = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));

        assert_eq!(views["candidate"].evidence_score, 10);
        assert_eq!(
            views["candidate"]
                .contributions
                .iter()
                .filter(|contribution| contribution.evidence_node_id.is_some())
                .count(),
            5
        );
    }

    #[test]
    fn hard_conflict_selection_remains_exact_above_twenty_four_nodes() {
        let center = "center".to_string();
        let leaves: BTreeSet<String> = (0..25).map(|index| format!("leaf-{index:02}")).collect();
        let mut eligible = leaves.clone();
        eligible.insert(center.clone());
        let mut adjacency = BTreeMap::new();
        adjacency.insert(center.clone(), leaves.clone());
        for leaf in &leaves {
            adjacency.insert(leaf.clone(), BTreeSet::from([center.clone()]));
        }
        let mut weights: BTreeMap<String, i32> =
            leaves.iter().map(|leaf| (leaf.clone(), 1)).collect();
        weights.insert(center.clone(), 10);

        let selected = maximum_weight_consistent_set(&eligible, &adjacency, &weights);
        assert_eq!(selected, leaves);
        assert!(!selected.contains(&center));
    }

    #[test]
    fn equivalent_duplicates_share_fitness_and_select_one_representative() {
        let graph = population(
            vec![
                complete_node(
                    "a",
                    vec![evidence(Kind::Assertoric, "a", "2026-01-01T00:00:00Z")],
                ),
                complete_node(
                    "b",
                    vec![evidence(Kind::Assertoric, "b", "2026-01-01T00:00:00Z")],
                ),
            ],
            vec![relation(EdgeKind::Equivalent, "a", "b")],
        );
        let views = derive_views_at(
            &["a".into(), "b".into()],
            &graph,
            at("2026-01-01T00:00:00Z"),
        );
        assert_eq!(
            views["a"].support_score, 10,
            "duplicate Evidence is not summed"
        );
        assert!(views["a"].current);
        assert!(!views["b"].current);
        assert_eq!(
            views["b"].exclusions[0].kind,
            ExclusionKind::EquivalentDuplicate
        );
    }

    #[test]
    fn contract_refinement_path_supports_its_abstract_specification() {
        let derivation = Derivation {
            method: "test".into(),
            version: "v1".into(),
        };
        let has = |specification: &str, contract: &str| {
            Edge::projection(
                EdgeKind::HasContract,
                specification,
                contract,
                derivation.clone(),
                "t",
            )
            .unwrap()
        };
        let contract_refines = Edge::contract_relation(
            EdgeKind::ContractRefines,
            "concrete-contract",
            "abstract-contract",
            vec!["concrete".into(), "abstract".into()],
            derivation.clone(),
            "t",
        )
        .unwrap();
        let graph = population(
            vec![
                complete_node("concrete", vec![]),
                complete_node("abstract", vec![]),
            ],
            vec![
                has("concrete", "concrete-contract"),
                has("abstract", "abstract-contract"),
                contract_refines,
            ],
        );
        let views = derive_views_at(&["abstract".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert!(views["abstract"].structural_score > 0);
        assert!(views["abstract"].current);
    }

    #[test]
    fn maximum_weight_hard_conflict_selection_can_choose_two_leaves() {
        let strong = |id: &str| {
            complete_node(
                id,
                vec![evidence(Kind::Assertoric, id, "2026-01-01T00:00:00Z")],
            )
        };
        let graph = population(
            vec![strong("left"), strong("center"), strong("right")],
            vec![
                relation(EdgeKind::HardContradiction, "left", "center"),
                relation(EdgeKind::HardContradiction, "center", "right"),
            ],
        );
        let views = derive_views_at(
            &["left".into(), "center".into(), "right".into()],
            &graph,
            at("2026-01-01T00:00:00Z"),
        );
        assert!(views["left"].current);
        assert!(!views["center"].current);
        assert!(views["right"].current);
        assert!(views["center"].conflict_pressure > 0);
    }

    #[test]
    fn unavailable_evidence_is_unknown_instead_of_disappearing() {
        let mut node = complete_node("candidate", vec![]);
        node.meta.evidence_requests = vec!["missing.md".into()];
        node.meta.updates.insert(
            "evidence".into(),
            MetaUpdate {
                source: crate::evidence_capture::PLUGIN_NAME.into(),
                applied_at: "2026-01-01T00:00:00Z".into(),
                value: json!({"status": "unavailable"}),
            },
        );
        let graph = population(vec![node], vec![]);
        let views = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert_eq!(
            views["candidate"].evaluation_state,
            EvaluationState::Unknown
        );
        assert_eq!(
            views["candidate"].exclusions[0].kind,
            ExclusionKind::EvidenceUnavailable
        );
    }

    #[test]
    fn stale_graph_projection_is_unknown_not_low_fitness() {
        let mut node = complete_node("candidate", vec![]);
        node.meta.updates.remove("contract");
        let graph = population(vec![node], vec![]);
        let views = derive_views_at(&["candidate".into()], &graph, at("2026-01-01T00:00:00Z"));
        assert_eq!(
            views["candidate"].evaluation_state,
            EvaluationState::Unknown
        );
        assert_eq!(
            views["candidate"].exclusions[0].kind,
            ExclusionKind::IncompleteGraph
        );
    }

    #[test]
    fn semantic_connectors_are_topology_while_lexical_and_evidence_facts_are_not() {
        assert!(!is_selection_topology(EdgeKind::MentionsTerm));
        assert!(!is_selection_topology(EdgeKind::SameLexeme));
        assert!(!is_selection_topology(EdgeKind::GroundedBy));
        assert!(is_selection_topology(EdgeKind::HasGuarantee));
        assert!(!is_selection_topology(EdgeKind::HasAssumption));
    }
}
