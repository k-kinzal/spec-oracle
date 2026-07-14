//! Incremental structure derived from one newly stored specification.
//!
//! Written term forms become shared connector vertices and each behavioral
//! sentence projects to shared Assumption/Guarantee vertices. Mention edges
//! are exact lexical facts and a versioned, replaceable candidate search—not
//! claims of referent identity. Candidate pairs are assessed by the pure
//! force-aware relation engine, and only proved graph-facing outcomes become
//! append-only specification-to-specification Edges. `Unknown`, `Independent`,
//! and unsearched pairs remain absent from topology; their absence says
//! nothing about whether a relationship exists.

use std::collections::BTreeMap;

use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use so_reason::relate::{assess, Outcome};

use crate::domain::{
    AssessmentOutcome, Derivation, DerivedNode, Edge, EdgeKind, EndpointRole, Node,
    RelationAssessment, TermNode, TextAnchor, VertexKind,
};
use crate::jobs::{JobOutput, NodeMetaPlugin, PluginContext, PluginRegistration};
use crate::store::{GraphStore, StoreError};

pub const TERM_DERIVATION_METHOD: &str = "so-daemon.graph.term-form";
pub const GENERATION_VERSION: &str = "spec-graph/term-form-v3";
pub const CANDIDATE_METHOD: &str = "so-daemon.graph.shared-term-candidates";
pub const CANDIDATE_VERSION: &str = "spec-graph/shared-term-candidates-v1";
pub const SEMANTIC_DERIVATION_METHOD: &str = "so-reason.relate.assess";
pub const SEMANTIC_DERIVATION_VERSION: &str = so_reason::relate::ASSESS_VERSION;
pub const SEMANTIC_EDGE_METHOD: &str = "so-daemon.graph.semantic-relations";
pub const SEMANTIC_EDGE_VERSION: &str = "spec-graph/semantic-relations-v2";
pub const CONTRACT_PROJECTION_METHOD: &str = "so-daemon.graph.ingest-contract";
pub const CONTRACT_PROJECTION_VERSION: &str = "spec-graph/ingest-contract-v1";
pub const RUN_VERSION: &str = "spec-graph/node-relations-v3";
const PLUGIN_NAME: &str = "graph-generation";
const CANDIDATE_PAGE_SIZE: usize = 500;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GenerationReport {
    pub terms_seen: usize,
    pub terms_inserted: usize,
    pub mention_edges_inserted: usize,
    pub contract_nodes_inserted: usize,
    pub contract_edges_inserted: usize,
    pub candidates_discovered: usize,
    pub candidates_examined: usize,
    pub candidates_unassessable: usize,
    pub assessments_inserted: usize,
    pub semantic_edges_inserted: usize,
    pub outcomes: BTreeMap<String, usize>,
}

#[derive(Debug, Clone)]
struct TermOccurrence {
    term: TermNode,
    anchor: TextAnchor,
}

pub fn generation_version() -> &'static str {
    GENERATION_VERSION
}

/// Version of the complete Node graph-generation run. Unlike an Edge
/// derivation version, this includes candidate-search behavior and therefore
/// changes the reconciliation Job identity without conflating discovery with
/// semantic proof.
pub fn reconciliation_version() -> String {
    format!(
        "{RUN_VERSION};term={GENERATION_VERSION};candidates={CANDIDATE_VERSION};assessment={SEMANTIC_DERIVATION_VERSION};semantic-edge={}",
        semantic_edge_derivation().version
    )
}

pub fn term_derivation() -> Derivation {
    Derivation {
        method: TERM_DERIVATION_METHOD.to_string(),
        version: GENERATION_VERSION.to_string(),
    }
}

pub fn semantic_derivation() -> Derivation {
    Derivation {
        method: SEMANTIC_DERIVATION_METHOD.to_string(),
        version: SEMANTIC_DERIVATION_VERSION.to_string(),
    }
}

/// Projection version for persisted semantic Edges. It includes the pure
/// assessment version so a changed reasoner appends new history even when the
/// resulting EdgeKind happens to remain the same.
pub fn semantic_edge_derivation() -> Derivation {
    Derivation {
        method: SEMANTIC_EDGE_METHOD.to_string(),
        version: format!("{SEMANTIC_EDGE_VERSION};assess={SEMANTIC_DERIVATION_VERSION}"),
    }
}

pub fn candidate_derivation() -> Derivation {
    Derivation {
        method: CANDIDATE_METHOD.to_string(),
        version: CANDIDATE_VERSION.to_string(),
    }
}

pub fn contract_projection_derivation() -> Derivation {
    Derivation {
        method: CONTRACT_PROJECTION_METHOD.to_string(),
        version: CONTRACT_PROJECTION_VERSION.to_string(),
    }
}

/// One selected version per Edge-producing method in the current graph view.
pub fn current_derivations() -> Vec<Derivation> {
    vec![
        term_derivation(),
        semantic_edge_derivation(),
        crate::selection::derivation(),
        crate::pairing::derivation(),
        contract_projection_derivation(),
        crate::pairing::projection_derivation(),
        crate::evidence_capture::evidence_derivation(),
    ]
}

pub fn needs_generation(node: &Node) -> bool {
    let semantic_edge = semantic_edge_derivation();
    !node.meta.updates.values().any(|update| {
        update.source == PLUGIN_NAME
            && update.value.get("run_version").and_then(Value::as_str) == Some(RUN_VERSION)
            && update
                .value
                .pointer("/contract_projection/method")
                .and_then(Value::as_str)
                == Some(CONTRACT_PROJECTION_METHOD)
            && update
                .value
                .pointer("/contract_projection/version")
                .and_then(Value::as_str)
                == Some(CONTRACT_PROJECTION_VERSION)
            && update
                .value
                .pointer("/term_generation/method")
                .and_then(Value::as_str)
                == Some(TERM_DERIVATION_METHOD)
            && update
                .value
                .pointer("/term_generation/version")
                .and_then(Value::as_str)
                == Some(GENERATION_VERSION)
            && update
                .value
                .pointer("/candidate_search/method")
                .and_then(Value::as_str)
                == Some(CANDIDATE_METHOD)
            && update
                .value
                .pointer("/candidate_search/version")
                .and_then(Value::as_str)
                == Some(CANDIDATE_VERSION)
            && update
                .value
                .pointer("/semantic_relations/method")
                .and_then(Value::as_str)
                == Some(SEMANTIC_EDGE_METHOD)
            && update
                .value
                .pointer("/semantic_relations/version")
                .and_then(Value::as_str)
                == Some(semantic_edge.version.as_str())
            && update
                .value
                .pointer("/semantic_relations/assessment_method")
                .and_then(Value::as_str)
                == Some(SEMANTIC_DERIVATION_METHOD)
            && update
                .value
                .pointer("/semantic_relations/assessment_version")
                .and_then(Value::as_str)
                == Some(SEMANTIC_DERIVATION_VERSION)
    })
}

pub fn generate_and_persist(
    added: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    let Some(sentence) = parse_current(added) else {
        return Ok(GenerationReport::default());
    };
    let occurrences = term_occurrences(added, &sentence);
    let mut term_ids: Vec<String> = occurrences
        .iter()
        .map(|occurrence| occurrence.term.id.clone())
        .collect();
    term_ids.sort();
    term_ids.dedup();
    let mut report = GenerationReport {
        terms_seen: occurrences.len(),
        ..GenerationReport::default()
    };
    persist_contract_projection(added, &sentence, store, recorded_at, &mut report)?;
    for occurrence in &occurrences {
        let edge = mention_edge(added, occurrence, recorded_at);
        let write = store.put_term_mention(&occurrence.term, &edge)?;
        report.terms_inserted += usize::from(write.term_inserted);
        report.mention_edges_inserted += usize::from(write.edge_inserted);
    }

    // Shared written terms are only a discovery mechanism. Every returned pair
    // still goes through `assess`, and omitted pairs remain explicitly
    // unsearched—not independent and not Unknown.
    let mut cursor: Option<String> = None;
    loop {
        let page = store.list_term_candidates(
            &term_ids,
            &term_derivation(),
            &added.id,
            cursor.as_deref(),
            CANDIDATE_PAGE_SIZE,
        )?;
        for candidate in page.nodes {
            report.candidates_discovered += 1;
            let Some(candidate_sentence) = parse_current(&candidate) else {
                report.candidates_unassessable += 1;
                continue;
            };
            report.candidates_examined += 1;
            let outcome = assess(&sentence, &candidate_sentence);
            *report
                .outcomes
                .entry(outcome_name(outcome).to_string())
                .or_default() += 1;
            let assessment = relation_assessment(added, &candidate, outcome, recorded_at);
            report.assessments_inserted +=
                usize::from(store.append_relation_assessment(&assessment)?);
            if let Some(edge) = semantic_edge(added, &candidate, outcome, recorded_at) {
                report.semantic_edges_inserted += usize::from(store.append_edge(&edge)?);
            }
        }
        match page.next_cursor {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }

    Ok(report)
}

fn persist_contract_projection(
    node: &Node,
    sentence: &so_lang::ast::Sentence,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    report: &mut GenerationReport,
) -> Result<(), StoreError> {
    let Some(contract) = so_reason::semantics::ingest_contract(sentence) else {
        return Ok(());
    };
    let derivation = contract_projection_derivation();
    let assumption =
        DerivedNode::assumption(contract.assumption.render(), CONTRACT_PROJECTION_VERSION);
    let assumption_edge = Edge::projection(
        EdgeKind::HasAssumption,
        &node.id,
        assumption.id(),
        derivation.clone(),
        recorded_at,
    )
    .expect("ingest assumptions always form a valid projection");
    let write = store.put_derived_node(&assumption, &assumption_edge)?;
    report.contract_nodes_inserted += usize::from(write.node_inserted);
    report.contract_edges_inserted += usize::from(write.edge_inserted);

    // Purpose states intent rather than guaranteed behavior, matching the
    // existing ContractView projection on the wire.
    let mut assertion = sentence.clone();
    assertion.purpose = None;
    let force = match contract.force {
        Some(so_reason::semantics::Force::Binding) => "binding",
        Some(so_reason::semantics::Force::Recommended) => "recommended",
        None => "",
    };
    let guarantee = DerivedNode::guarantee(&assertion.render(), force, CONTRACT_PROJECTION_VERSION);
    let guarantee_edge = Edge::projection(
        EdgeKind::HasGuarantee,
        &node.id,
        guarantee.id(),
        derivation,
        recorded_at,
    )
    .expect("ingest guarantees always form a valid projection");
    let write = store.put_derived_node(&guarantee, &guarantee_edge)?;
    report.contract_nodes_inserted += usize::from(write.node_inserted);
    report.contract_edges_inserted += usize::from(write.edge_inserted);
    Ok(())
}

fn relation_assessment(
    added: &Node,
    candidate: &Node,
    outcome: Outcome,
    recorded_at: &str,
) -> RelationAssessment {
    let (left, right) = if added.id <= candidate.id {
        (added.id.as_str(), candidate.id.as_str())
    } else {
        (candidate.id.as_str(), added.id.as_str())
    };
    let normalized_outcome = match outcome {
        Outcome::Refinement {
            concrete_is_a: true,
        } => AssessmentOutcome::Refines {
            concrete: added.id.clone(),
            abstract_: candidate.id.clone(),
        },
        Outcome::Refinement {
            concrete_is_a: false,
        } => AssessmentOutcome::Refines {
            concrete: candidate.id.clone(),
            abstract_: added.id.clone(),
        },
        Outcome::Equivalent => AssessmentOutcome::Equivalent,
        Outcome::HardContradiction => AssessmentOutcome::HardContradiction,
        Outcome::AdvisoryTension => AssessmentOutcome::AdvisoryTension,
        Outcome::DescriptiveConflict => AssessmentOutcome::DescriptiveConflict,
        Outcome::EnvelopeConflict => AssessmentOutcome::EnvelopeConflict,
        Outcome::Independent => AssessmentOutcome::Independent,
        Outcome::Unknown => AssessmentOutcome::Unknown,
    };
    let candidate_derivation = candidate_derivation();
    let semantic_derivation = semantic_derivation();
    RelationAssessment {
        id: stable_id(
            "assessment",
            &[
                &candidate_derivation.method,
                &candidate_derivation.version,
                &semantic_derivation.method,
                &semantic_derivation.version,
                left,
                right,
            ],
        ),
        left: left.to_string(),
        right: right.to_string(),
        candidate_derivation,
        semantic_derivation,
        outcome: normalized_outcome,
        recorded_at: recorded_at.to_string(),
    }
}

fn outcome_name(outcome: Outcome) -> &'static str {
    match outcome {
        Outcome::HardContradiction => "hard_contradiction",
        Outcome::AdvisoryTension => "advisory_tension",
        Outcome::DescriptiveConflict => "descriptive_conflict",
        Outcome::Refinement { .. } => "refinement",
        Outcome::Equivalent => "equivalent",
        Outcome::Independent => "independent",
        Outcome::EnvelopeConflict => "envelope_conflict",
        Outcome::Unknown => "unknown",
    }
}

fn semantic_edge(
    added: &Node,
    candidate: &Node,
    outcome: Outcome,
    recorded_at: &str,
) -> Option<Edge> {
    let (kind, source, target) = match outcome {
        Outcome::Refinement {
            concrete_is_a: true,
        } => (EdgeKind::Refines, added.id.as_str(), candidate.id.as_str()),
        Outcome::Refinement {
            concrete_is_a: false,
        } => (EdgeKind::Refines, candidate.id.as_str(), added.id.as_str()),
        Outcome::Equivalent => symmetric_endpoints(EdgeKind::Equivalent, added, candidate),
        Outcome::HardContradiction => {
            symmetric_endpoints(EdgeKind::HardContradiction, added, candidate)
        }
        Outcome::AdvisoryTension => {
            symmetric_endpoints(EdgeKind::AdvisoryTension, added, candidate)
        }
        Outcome::DescriptiveConflict => {
            symmetric_endpoints(EdgeKind::DescriptiveConflict, added, candidate)
        }
        Outcome::EnvelopeConflict => {
            symmetric_endpoints(EdgeKind::EnvelopeConflict, added, candidate)
        }
        Outcome::Independent | Outcome::Unknown => return None,
    };
    let derivation = semantic_edge_derivation();
    Some(
        Edge::specification_relation(kind, source, target, Vec::new(), derivation, recorded_at)
            .expect("semantic outcomes always map to valid specification relationships"),
    )
}

fn symmetric_endpoints<'a>(
    kind: EdgeKind,
    a: &'a Node,
    b: &'a Node,
) -> (EdgeKind, &'a str, &'a str) {
    if a.id <= b.id {
        (kind, &a.id, &b.id)
    } else {
        (kind, &b.id, &a.id)
    }
}

fn parse_current(node: &Node) -> Option<so_lang::ast::Sentence> {
    if node.lang_version != so_lang::LANG_VERSION {
        return None;
    }
    so_lang::parse::parse(&node.statement)
        .ok()
        .and_then(|specification| specification.sentences.into_iter().next())
}

fn term_occurrences(node: &Node, sentence: &so_lang::ast::Sentence) -> Vec<TermOccurrence> {
    let value = serde_json::to_value(sentence).expect("sentence AST serializes");
    let mut found = Vec::new();
    walk_terms(node, &value, "", &mut found);
    found.sort_by(|a, b| {
        a.term
            .id
            .cmp(&b.term.id)
            .then_with(|| a.anchor.selector.cmp(&b.anchor.selector))
    });
    found.dedup_by(|a, b| a.term.id == b.term.id && a.anchor.selector == b.anchor.selector);
    found
}

fn walk_terms(node: &Node, value: &Value, path: &str, found: &mut Vec<TermOccurrence>) {
    match value {
        Value::Object(map) => {
            if map.contains_key("head") && map.contains_key("modifiers") {
                if let Ok(np) = serde_json::from_value::<so_lang::ast::Np>(value.clone()) {
                    let mut without_det = np.clone();
                    without_det.det = None;
                    let form = without_det.render().to_lowercase();
                    let head = np.head.to_lowercase();
                    let term = TermNode {
                        id: stable_id("term", &[&node.lang_version, GENERATION_VERSION, &form]),
                        form,
                        head,
                        lang_version: node.lang_version.clone(),
                        derivation_version: GENERATION_VERSION.to_string(),
                    };
                    found.push(TermOccurrence {
                        term,
                        anchor: TextAnchor {
                            selector: if path.is_empty() {
                                "/".to_string()
                            } else {
                                path.to_string()
                            },
                            text: np.render(),
                            role: grammatical_role(path).to_string(),
                        },
                    });
                }
            }
            for (key, child) in map {
                let escaped = key.replace('~', "~0").replace('/', "~1");
                let next = format!("{path}/{escaped}");
                walk_terms(node, child, &next, found);
            }
        }
        Value::Array(items) => {
            for (index, child) in items.iter().enumerate() {
                walk_terms(node, child, &format!("{path}/{index}"), found);
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
    }
}

fn grammatical_role(path: &str) -> &'static str {
    if path.ends_with("/core/term") {
        "definition_term"
    } else if path.contains("/subject") {
        "subject"
    } else if path.contains("/object") {
        "object"
    } else if path.contains("/agent") {
        "agent"
    } else if path.contains("/roles") {
        "role"
    } else if path.contains("/predicate") {
        "predicate"
    } else if path.contains("/definiens") {
        "definition"
    } else {
        "noun"
    }
}

fn mention_edge(node: &Node, occurrence: &TermOccurrence, recorded_at: &str) -> Edge {
    let mut edge = Edge {
        id: String::new(),
        source: node.id.clone(),
        source_kind: VertexKind::Specification,
        source_role: EndpointRole::Mentioner,
        target: occurrence.term.id.clone(),
        target_kind: VertexKind::Term,
        target_role: EndpointRole::MentionedTerm,
        kind: EdgeKind::MentionsTerm,
        source_anchor: Some(occurrence.anchor.clone()),
        target_anchor: None,
        relied_spec_id: None,
        basis_spec_ids: Vec::new(),
        derivation: Derivation {
            method: TERM_DERIVATION_METHOD.to_string(),
            version: GENERATION_VERSION.to_string(),
        },
        recorded_at: recorded_at.to_string(),
    };
    edge.id = edge.identity_key();
    edge
}

fn stable_id(kind: &str, parts: &[&str]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(kind.as_bytes());
    for part in parts {
        hasher.update([0]);
        hasher.update(part.as_bytes());
    }
    format!("{kind}-{:x}", hasher.finalize())
}

struct GraphGenerationPlugin;

impl NodeMetaPlugin for GraphGenerationPlugin {
    fn handles(&self, node: &Node) -> bool {
        node.lang_version == so_lang::LANG_VERSION && needs_generation(node)
    }

    fn run(&self, node: &Node, context: &PluginContext<'_>) -> Result<JobOutput, String> {
        let report = generate_and_persist(node, context.graph, context.now)
            .map_err(|error| error.to_string())?;
        Ok(JobOutput::metadata(json!({
            "run_version": RUN_VERSION,
            "term_generation": {
                "method": TERM_DERIVATION_METHOD,
                "version": GENERATION_VERSION,
                "terms_seen": report.terms_seen,
                "terms_inserted": report.terms_inserted,
                "mention_edges_inserted": report.mention_edges_inserted,
            },
            "contract_projection": {
                "method": CONTRACT_PROJECTION_METHOD,
                "version": CONTRACT_PROJECTION_VERSION,
                "nodes_inserted": report.contract_nodes_inserted,
                "edges_inserted": report.contract_edges_inserted,
            },
            "candidate_search": {
                "method": CANDIDATE_METHOD,
                "version": CANDIDATE_VERSION,
                "candidates_discovered": report.candidates_discovered,
                "candidates_examined": report.candidates_examined,
                "candidates_unassessable": report.candidates_unassessable,
                "assessments_inserted": report.assessments_inserted,
                "outcomes": report.outcomes,
            },
            "semantic_relations": {
                "method": SEMANTIC_EDGE_METHOD,
                "version": semantic_edge_derivation().version,
                "assessment_method": SEMANTIC_DERIVATION_METHOD,
                "assessment_version": SEMANTIC_DERIVATION_VERSION,
                "edges_inserted": report.semantic_edges_inserted,
            },
        })))
    }
}

fn graph_generation_factory() -> Box<dyn NodeMetaPlugin> {
    Box::new(GraphGenerationPlugin)
}

inventory::submit! {
    PluginRegistration::new(PLUGIN_NAME, graph_generation_factory)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, MetaUpdate, VertexKind};
    use crate::store::{GraphStore, InMemoryNodeStore, NodeStore};

    fn node(id: &str, statement: &str) -> Node {
        Node {
            id: id.into(),
            statement: statement.into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: vec![],
                evidence_request_generation: String::new(),
                evidence: vec![],
                created_at: "2026-07-12T00:00:00Z".into(),
                cli: "test".into(),
                cli_version: "test".into(),
                updates: Default::default(),
            },
        }
    }

    #[test]
    fn reconciliation_requires_every_pipeline_method_version() {
        let mut current = node("a", "The pump shall stop.");
        current.meta.updates.insert(
            "job".into(),
            MetaUpdate {
                source: PLUGIN_NAME.into(),
                applied_at: "t".into(),
                value: json!({
                    "run_version": RUN_VERSION,
                    "term_generation": {
                        "method": TERM_DERIVATION_METHOD,
                        "version": GENERATION_VERSION,
                    },
                    "candidate_search": {
                        "method": CANDIDATE_METHOD,
                        "version": CANDIDATE_VERSION,
                    },
                    "contract_projection": {
                        "method": CONTRACT_PROJECTION_METHOD,
                        "version": CONTRACT_PROJECTION_VERSION,
                    },
                    "semantic_relations": {
                        "method": SEMANTIC_EDGE_METHOD,
                        "version": semantic_edge_derivation().version,
                        "assessment_method": SEMANTIC_DERIVATION_METHOD,
                        "assessment_version": SEMANTIC_DERIVATION_VERSION,
                    },
                }),
            },
        );
        assert!(!needs_generation(&current));

        current.meta.updates.get_mut("job").unwrap().value["candidate_search"]["version"] =
            Value::String("old-candidate-version".into());
        assert!(needs_generation(&current));
    }

    #[test]
    fn stop_command_is_a_shared_term_hub_not_a_spec_to_spec_lexical_edge() {
        let store = InMemoryNodeStore::new();
        let a = node(
            "a",
            "When the emergency-stop button is pressed, the button controller shall issue the stop command.",
        );
        let b = node(
            "b",
            "When the motor controller receives the stop command, the motor controller shall disable the drive.",
        );
        store.add_node(&a).unwrap();
        store.add_node(&b).unwrap();
        generate_and_persist(&a, &store, "2026-07-12T00:00:01Z").unwrap();
        let report = generate_and_persist(&b, &store, "2026-07-12T00:00:02Z").unwrap();

        let edges = store
            .list_edges(&["a".into(), "b".into()], &current_derivations())
            .unwrap();
        let shared_term = edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::MentionsTerm)
            .filter_map(|edge| {
                store
                    .get_term_nodes(std::slice::from_ref(&edge.target))
                    .unwrap()
                    .into_iter()
                    .next()
            })
            .find(|term| term.form == "stop command")
            .unwrap();
        let mentions = edges
            .iter()
            .filter(|edge| edge.target == shared_term.id)
            .collect::<Vec<_>>();
        assert_eq!(mentions.len(), 2);
        assert!(mentions
            .iter()
            .all(|edge| edge.target_kind == VertexKind::Term));
        assert!(!edges.iter().any(|edge| {
            edge.source_kind == VertexKind::Specification
                && edge.target_kind == VertexKind::Specification
        }));
        assert_eq!(report.candidates_examined, 1);
        assert_eq!(report.outcomes.get("unknown"), Some(&1));
        assert_eq!(report.assessments_inserted, 1);
        let audit = relation_assessment(&b, &a, Outcome::Unknown, "ignored");
        let stored = store
            .get_relation_assessment(&audit.id)
            .unwrap()
            .expect("Unknown is audited outside topology");
        assert_eq!(stored.outcome, AssessmentOutcome::Unknown);
    }

    #[test]
    fn contract_projection_creates_and_reuses_assumption_and_guarantee_nodes() {
        let store = InMemoryNodeStore::new();
        let a = node("a", "The pump shall stop.");
        let b = node("b", "The pump shall stop.");
        store.add_node(&a).unwrap();
        store.add_node(&b).unwrap();

        let first = generate_and_persist(&a, &store, "t1").unwrap();
        let second = generate_and_persist(&b, &store, "t2").unwrap();
        assert_eq!(first.contract_nodes_inserted, 2);
        assert_eq!(first.contract_edges_inserted, 2);
        assert_eq!(second.contract_nodes_inserted, 0);
        assert_eq!(second.contract_edges_inserted, 2);

        let projection_edges: Vec<Edge> = store
            .list_edges(
                &["a".into(), "b".into()],
                &[contract_projection_derivation()],
            )
            .unwrap();
        assert_eq!(projection_edges.len(), 4);
        let mut ids: Vec<String> = projection_edges
            .iter()
            .map(|edge| edge.target.clone())
            .collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), 2, "both specifications share the same A/G nodes");
        let nodes = store.get_derived_nodes(&ids).unwrap();
        assert!(nodes.iter().any(
            |node| matches!(node, DerivedNode::Assumption { expression, .. } if expression == "⊤")
        ));
        assert!(nodes.iter().any(|node| {
            matches!(node, DerivedNode::Guarantee { expression, force, .. }
                if expression == "the pump shall stop." && force == "binding")
        }));
    }

    #[test]
    fn proved_refinement_is_persisted_in_its_semantic_direction() {
        let store = InMemoryNodeStore::new();
        let abstract_ = node(
            "abstract",
            "The daemon shall flush the buffer within 10 seconds.",
        );
        let concrete = node(
            "concrete",
            "The daemon shall flush the buffer within 5 seconds.",
        );
        store.add_node(&abstract_).unwrap();
        store.add_node(&concrete).unwrap();
        generate_and_persist(&abstract_, &store, "t1").unwrap();
        let report = generate_and_persist(&concrete, &store, "t2").unwrap();

        let semantic: Vec<Edge> = store
            .list_edges(
                &["abstract".into(), "concrete".into()],
                &current_derivations(),
            )
            .unwrap()
            .into_iter()
            .filter(|edge| edge.family() == crate::domain::EdgeFamily::Semantic)
            .collect();
        assert_eq!(semantic.len(), 1);
        assert_eq!(semantic[0].kind, EdgeKind::Refines);
        assert_eq!(semantic[0].source, "concrete");
        assert_eq!(semantic[0].target, "abstract");
        assert_eq!(semantic[0].derivation, semantic_edge_derivation());
        assert_eq!(semantic[0].source_role, EndpointRole::Refiner);
        assert_eq!(semantic[0].target_role, EndpointRole::Refined);
        assert_eq!(report.outcomes.get("refinement"), Some(&1));
        assert_eq!(report.assessments_inserted, 1);
        assert_eq!(report.semantic_edges_inserted, 1);

        // Reassessment is harmless: the stable derivation-derived ID makes the
        // append a no-op while the proved relation remains current.
        let retry = generate_and_persist(&concrete, &store, "t3").unwrap();
        assert_eq!(retry.assessments_inserted, 0);
        assert_eq!(retry.semantic_edges_inserted, 0);
    }

    #[test]
    fn symmetric_outcomes_canonicalize_endpoints_and_unknown_is_not_an_edge() {
        let a = node("z", "The pump shall stop.");
        let b = node("a", "The pump shall stop.");
        let equivalent = semantic_edge(&a, &b, Outcome::Equivalent, "t").unwrap();
        assert_eq!(equivalent.kind, EdgeKind::Equivalent);
        assert_eq!(
            (equivalent.source.as_str(), equivalent.target.as_str()),
            ("a", "z")
        );
        let reverse = semantic_edge(&b, &a, Outcome::Equivalent, "later").unwrap();
        assert_eq!(equivalent.id, reverse.id);

        for outcome in [Outcome::Independent, Outcome::Unknown] {
            assert!(semantic_edge(&a, &b, outcome, "t").is_none());
        }
    }

    #[test]
    fn every_proved_conflict_family_maps_to_a_symmetric_edge_kind() {
        let a = node("b", "The pump shall stop.");
        let b = node("a", "The pump shall not stop.");
        for (outcome, expected) in [
            (Outcome::HardContradiction, EdgeKind::HardContradiction),
            (Outcome::AdvisoryTension, EdgeKind::AdvisoryTension),
            (Outcome::DescriptiveConflict, EdgeKind::DescriptiveConflict),
            (Outcome::EnvelopeConflict, EdgeKind::EnvelopeConflict),
        ] {
            let edge = semantic_edge(&a, &b, outcome, "t").unwrap();
            assert_eq!(edge.kind, expected);
            assert_eq!((edge.source.as_str(), edge.target.as_str()), ("a", "b"));
            assert_eq!(edge.source_role, EndpointRole::ConflictPeer);
            assert_eq!(edge.target_role, EndpointRole::ConflictPeer);
            assert!(!edge.kind.directed());
        }
    }
}
