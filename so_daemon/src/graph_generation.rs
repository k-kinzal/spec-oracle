//! Incremental structure derived from one newly stored specification.
//!
//! Written term forms become shared connector vertices and each behavioral
//! sentence projects to shared Assumption/Guarantee vertices. Mention edges
//! are exact lexical facts and a versioned, replaceable candidate search—not
//! claims of referent identity. Candidate pairs are assessed by the pure
//! force-aware relation engine, and only proved graph-facing verdicts become
//! append-only specification-to-specification Edges. `Unknown`, `Independent`,
//! and unsearched pairs remain absent from topology; their absence says
//! nothing about whether a relationship exists.

use std::collections::BTreeMap;

use serde_json::Value;
use sha2::{Digest, Sha256};
use so_reason::contract::{assess_contracts, ContractRelation};
use so_reason::formula::assertion_formula;
use so_reason::relate::{assess, assess_formulas, FormulaRelation, RelationVerdict};

use crate::domain::{
    AssessmentVerdict, Derivation, DerivedNode, Edge, EdgeKind, EndpointRole, Node,
    RelationAssessment, TermNode, TextAnchor, VertexKind,
};
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
pub const CONTRACT_PROJECTION_VERSION: &str = "spec-graph/ingest-contract-v2";
pub const FORMULA_ASSESSMENT_METHOD: &str = "so-reason.relate.assess-formulas";
pub const CONTRACT_ASSESSMENT_METHOD: &str = "so-reason.contract.assess";
pub const CONTRACT_ASSESSMENT_VERSION: &str = "so-reason/contract-assess-v1";
pub const CONTRACT_RELATION_METHOD: &str = "so-daemon.graph.contract-relations";
pub const CONTRACT_RELATION_VERSION: &str = "spec-graph/contract-relations-v1";
pub const DISCHARGE_CANDIDATE_METHOD: &str = "so-daemon.graph.discharge-candidates";
pub const DISCHARGE_CANDIDATE_VERSION: &str = "spec-graph/discharge-candidates-v1";
pub const RUN_VERSION: &str = "spec-graph/node-relations-v4";
const PLUGIN_NAME: &str = "graph-generation";
const CANDIDATE_PAGE_SIZE: usize = 500;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GenerationReport {
    pub terms_seen: usize,
    pub terms_inserted: usize,
    pub mention_edges_inserted: usize,
    pub contract_nodes_inserted: usize,
    pub contract_edges_inserted: usize,
    /// The reconciliation subject has a formed A/G contract.
    pub subject_has_contract: bool,
    /// The subject cannot be interpreted by the current language/reasoner.
    /// This is a durable applicability result, not a retryable store failure.
    pub subject_unassessable: bool,
    pub candidates_discovered: usize,
    pub candidates_examined: usize,
    pub candidates_unassessable: usize,
    pub assessments_inserted: usize,
    pub semantic_edges_inserted: usize,
    pub verdicts: BTreeMap<String, usize>,
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
/// identifies the aggregate compatibility projection without conflating discovery with
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
        crate::pairing::derivation(),
        contract_projection_derivation(),
        contract_relation_derivation(),
        crate::contract_algebra::derivation(),
        crate::pairing::projection_derivation(),
        crate::evidence_capture::evidence_derivation(),
    ]
}

pub fn contract_relation_derivation() -> Derivation {
    Derivation {
        method: CONTRACT_RELATION_METHOD.to_string(),
        version: format!("{CONTRACT_RELATION_VERSION};reason={CONTRACT_ASSESSMENT_VERSION}"),
    }
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
    let added_contract_node =
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
            let verdict = assess(&sentence, &candidate_sentence);
            *report
                .verdicts
                .entry(verdict_name(verdict).to_string())
                .or_default() += 1;
            let assessment = relation_assessment(added, &candidate, verdict, recorded_at);
            report.assessments_inserted +=
                usize::from(store.append_relation_assessment(&assessment)?);
            if let (Some(added_formula), Some(candidate_formula)) = (
                assertion_formula(&sentence),
                assertion_formula(&candidate_sentence),
            ) {
                let formula_assessment = formula_relation_assessment(
                    added,
                    &candidate,
                    assess_formulas(&added_formula, &candidate_formula),
                    recorded_at,
                );
                report.assessments_inserted +=
                    usize::from(store.append_relation_assessment(&formula_assessment)?);
            }
            if let Some(edge) = semantic_edge(added, &candidate, verdict, recorded_at) {
                report.semantic_edges_inserted += usize::from(store.append_edge(&edge)?);
            }
            if let (Some(added_contract_node), Some(candidate_contract)) = (
                added_contract_node.as_ref(),
                crate::pairing::current_formed_contract(store, &candidate)
                    .map_err(|error| StoreError::Backend(error.to_string()))?,
            ) {
                let candidate_contract_node = DerivedNode::contract(
                    &candidate_contract.semantic(),
                    "formed",
                    CONTRACT_PROJECTION_VERSION,
                );
                persist_contract_assessment_and_edge(
                    added,
                    added_contract_node,
                    &candidate,
                    &candidate_contract_node,
                    store,
                    recorded_at,
                    &mut report,
                )?;
                persist_discharge_candidates(added, &candidate, store, recorded_at, &mut report)?;
            }
        }
        match page.next_cursor {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }

    Ok(report)
}

pub(crate) fn persist_term_projection_only(
    node: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    let Some(sentence) = parse_current(node) else {
        return Ok(GenerationReport::default());
    };
    let occurrences = term_occurrences(node, &sentence);
    let mut report = GenerationReport {
        terms_seen: occurrences.len(),
        ..GenerationReport::default()
    };
    for occurrence in &occurrences {
        let edge = mention_edge(node, occurrence, recorded_at);
        let write = store.put_term_mention(&occurrence.term, &edge)?;
        report.terms_inserted += usize::from(write.term_inserted);
        report.mention_edges_inserted += usize::from(write.edge_inserted);
    }
    Ok(report)
}

pub(crate) fn persist_contract_projection_only(
    node: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<(GenerationReport, Option<String>), StoreError> {
    let Some(sentence) = parse_current(node) else {
        return Ok((GenerationReport::default(), None));
    };
    let mut report = GenerationReport::default();
    let contract = persist_contract_projection(node, &sentence, store, recorded_at, &mut report)?;
    Ok((report, contract.map(|contract| contract.id().to_string())))
}

pub(crate) fn persist_semantic_relations_only(
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
    let mut report = GenerationReport::default();
    let mut cursor = None;
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
            let verdict = assess(&sentence, &candidate_sentence);
            *report
                .verdicts
                .entry(verdict_name(verdict).to_string())
                .or_default() += 1;
            let assessment = relation_assessment(added, &candidate, verdict, recorded_at);
            report.assessments_inserted +=
                usize::from(store.append_relation_assessment(&assessment)?);
            if let (Some(added_formula), Some(candidate_formula)) = (
                assertion_formula(&sentence),
                assertion_formula(&candidate_sentence),
            ) {
                let formula_assessment = formula_relation_assessment(
                    added,
                    &candidate,
                    assess_formulas(&added_formula, &candidate_formula),
                    recorded_at,
                );
                report.assessments_inserted +=
                    usize::from(store.append_relation_assessment(&formula_assessment)?);
            }
            if let Some(edge) = semantic_edge(added, &candidate, verdict, recorded_at) {
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

/// Re-assess every contract involving `changed` after its selected assumption
/// changes. Relationships attach to content-addressed Contract vertices, so
/// prior results remain valid Ledger facts about prior `(A,G)` values while
/// the new HasContract projection selects the new value.
pub fn reconcile_contract_relations_for(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    reconcile_contract_work(changed, store, recorded_at, true, true)
}

pub(crate) fn reconcile_contract_relations_only(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    reconcile_contract_work(changed, store, recorded_at, true, false)
}

pub(crate) fn reconcile_discharge_candidates_only(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    reconcile_contract_work(changed, store, recorded_at, false, true)
}

fn reconcile_contract_work(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    assess_relations: bool,
    assess_discharges: bool,
) -> Result<GenerationReport, StoreError> {
    let changed_contract = match contract_for_reconciliation(store, changed)? {
        ReconciliationContract::Formed(contract) => contract,
        ReconciliationContract::NoContract => return Ok(GenerationReport::default()),
        ReconciliationContract::Unassessable => {
            return Ok(GenerationReport {
                subject_unassessable: true,
                ..GenerationReport::default()
            });
        }
    };
    let changed_contract_node = DerivedNode::contract(
        &changed_contract.semantic(),
        "formed",
        CONTRACT_PROJECTION_VERSION,
    );
    let mut report = GenerationReport {
        subject_has_contract: true,
        ..GenerationReport::default()
    };
    let mut cursor = None;
    loop {
        let page = store.list_nodes(cursor.as_deref(), CANDIDATE_PAGE_SIZE)?;
        for candidate in page.nodes {
            if candidate.id == changed.id {
                continue;
            }
            let candidate_contract = match contract_for_reconciliation(store, &candidate)? {
                ReconciliationContract::Formed(contract) => contract,
                ReconciliationContract::NoContract => continue,
                ReconciliationContract::Unassessable => {
                    report.candidates_unassessable += 1;
                    continue;
                }
            };
            let candidate_contract_node = DerivedNode::contract(
                &candidate_contract.semantic(),
                "formed",
                CONTRACT_PROJECTION_VERSION,
            );
            if assess_relations {
                persist_contract_assessment_and_edge(
                    changed,
                    &changed_contract_node,
                    &candidate,
                    &candidate_contract_node,
                    store,
                    recorded_at,
                    &mut report,
                )?;
            }
            if assess_discharges {
                persist_discharge_candidates(changed, &candidate, store, recorded_at, &mut report)?;
            }
        }
        match page.next_cursor {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    Ok(report)
}

enum ReconciliationContract {
    Formed(so_reason::contract::FormedContract),
    NoContract,
    Unassessable,
}

/// Separate deterministic applicability from retryable infrastructure failure.
/// A stored Node that no longer parses cannot become healthy by redelivering
/// the same Event, so it must complete as unassessable rather than poison the
/// at-least-once stream. Store errors remain errors and are retried.
fn contract_for_reconciliation(
    store: &(dyn GraphStore + Send + Sync),
    node: &Node,
) -> Result<ReconciliationContract, StoreError> {
    match crate::pairing::current_formed_contract(store, node) {
        Ok(Some(contract)) => Ok(ReconciliationContract::Formed(contract)),
        Ok(None) => Ok(ReconciliationContract::NoContract),
        Err(crate::pairing::PairingError::Store(error)) => Err(error),
        Err(_) => Ok(ReconciliationContract::Unassessable),
    }
}

fn persist_contract_projection(
    node: &Node,
    sentence: &so_lang::ast::Sentence,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    report: &mut GenerationReport,
) -> Result<Option<DerivedNode>, StoreError> {
    let Some(contract) = so_reason::contract::formed_contract(sentence) else {
        return Ok(None);
    };
    let derivation = contract_projection_derivation();
    let assumption_json =
        serde_json::to_string(&contract.assumption).map_err(StoreError::Serialize)?;
    let assumption =
        DerivedNode::assumption_formula("⊤", &assumption_json, CONTRACT_PROJECTION_VERSION);
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
    let force = match so_reason::semantics::force(sentence) {
        Some(so_reason::semantics::Force::Binding) => "binding",
        Some(so_reason::semantics::Force::Recommended) => "recommended",
        None => "",
    };
    let guarantee_json =
        serde_json::to_string(&contract.guarantee).map_err(StoreError::Serialize)?;
    let guarantee = DerivedNode::guarantee_formula(
        &assertion.render(),
        force,
        &guarantee_json,
        CONTRACT_PROJECTION_VERSION,
    );
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

    let semantic =
        DerivedNode::contract(&contract.semantic(), "formed", CONTRACT_PROJECTION_VERSION);
    let contract_edge = Edge::projection(
        EdgeKind::HasContract,
        &node.id,
        semantic.id(),
        contract_projection_derivation(),
        recorded_at,
    )
    .expect("formed contracts always form a valid semantic projection");
    let write = store.put_derived_node(&semantic, &contract_edge)?;
    report.contract_nodes_inserted += usize::from(write.node_inserted);
    report.contract_edges_inserted += usize::from(write.edge_inserted);
    Ok(Some(semantic))
}

fn relation_assessment(
    added: &Node,
    candidate: &Node,
    verdict: RelationVerdict,
    recorded_at: &str,
) -> RelationAssessment {
    let (left, right) = if added.id <= candidate.id {
        (added.id.as_str(), candidate.id.as_str())
    } else {
        (candidate.id.as_str(), added.id.as_str())
    };
    let normalized_verdict = match verdict {
        RelationVerdict::Refinement {
            concrete_is_a: true,
        } => AssessmentVerdict::Refines {
            concrete: added.id.clone(),
            abstract_: candidate.id.clone(),
        },
        RelationVerdict::Refinement {
            concrete_is_a: false,
        } => AssessmentVerdict::Refines {
            concrete: candidate.id.clone(),
            abstract_: added.id.clone(),
        },
        RelationVerdict::Equivalent => AssessmentVerdict::Equivalent,
        RelationVerdict::HardContradiction => AssessmentVerdict::HardContradiction,
        RelationVerdict::AdvisoryTension => AssessmentVerdict::AdvisoryTension,
        RelationVerdict::DescriptiveConflict => AssessmentVerdict::DescriptiveConflict,
        RelationVerdict::EnvelopeConflict => AssessmentVerdict::EnvelopeConflict,
        RelationVerdict::Independent => AssessmentVerdict::Independent,
        RelationVerdict::Unknown => AssessmentVerdict::Unknown,
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
        verdict: normalized_verdict,
        recorded_at: recorded_at.to_string(),
    }
}

fn formula_relation_assessment(
    added: &Node,
    candidate: &Node,
    relation: FormulaRelation,
    recorded_at: &str,
) -> RelationAssessment {
    let (left, right) = ordered_ids(&added.id, &candidate.id);
    let verdict = match relation {
        FormulaRelation::Equivalent => AssessmentVerdict::FormulaEquivalent,
        FormulaRelation::Entails => AssessmentVerdict::FormulaEntails {
            antecedent: added.id.clone(),
            consequence: candidate.id.clone(),
        },
        FormulaRelation::EntailedBy => AssessmentVerdict::FormulaEntails {
            antecedent: candidate.id.clone(),
            consequence: added.id.clone(),
        },
        FormulaRelation::Contradicts => AssessmentVerdict::FormulaContradiction,
        FormulaRelation::Unknown => AssessmentVerdict::FormulaUnknown,
    };
    assessment_record(
        left,
        right,
        Derivation {
            method: FORMULA_ASSESSMENT_METHOD.to_string(),
            version: so_reason::relate::FORMULA_ASSESS_VERSION.to_string(),
        },
        verdict,
        recorded_at,
        &[],
    )
}

fn persist_contract_assessment_and_edge(
    added: &Node,
    added_contract_node: &DerivedNode,
    candidate: &Node,
    candidate_contract_node: &DerivedNode,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    report: &mut GenerationReport,
) -> Result<(), StoreError> {
    let added_contract = added_contract_node
        .semantic_contract()
        .expect("a contract projection contains a semantic contract");
    let candidate_contract = candidate_contract_node
        .semantic_contract()
        .expect("a contract projection contains a semantic contract");
    let relation = assess_contracts(&added_contract, &candidate_contract);
    let (left, right) = ordered_ids(&added.id, &candidate.id);
    let verdict = match relation {
        ContractRelation::Refines => AssessmentVerdict::ContractRefines {
            concrete: added.id.clone(),
            abstract_: candidate.id.clone(),
        },
        ContractRelation::RefinedBy => AssessmentVerdict::ContractRefines {
            concrete: candidate.id.clone(),
            abstract_: added.id.clone(),
        },
        ContractRelation::Equivalent => AssessmentVerdict::ContractEquivalent,
        ContractRelation::Incomparable => AssessmentVerdict::ContractIncomparable,
    };
    let assessment = assessment_record(
        left,
        right,
        Derivation {
            method: CONTRACT_ASSESSMENT_METHOD.to_string(),
            version: CONTRACT_ASSESSMENT_VERSION.to_string(),
        },
        verdict,
        recorded_at,
        &[added_contract_node.id(), candidate_contract_node.id()],
    );
    report.assessments_inserted += usize::from(store.append_relation_assessment(&assessment)?);

    let edge = match relation {
        ContractRelation::Refines => Some(Edge::contract_relation(
            EdgeKind::ContractRefines,
            added_contract_node.id(),
            candidate_contract_node.id(),
            vec![added.id.clone(), candidate.id.clone()],
            contract_relation_derivation(),
            recorded_at,
        )),
        ContractRelation::RefinedBy => Some(Edge::contract_relation(
            EdgeKind::ContractRefines,
            candidate_contract_node.id(),
            added_contract_node.id(),
            vec![added.id.clone(), candidate.id.clone()],
            contract_relation_derivation(),
            recorded_at,
        )),
        ContractRelation::Equivalent
            if added_contract_node.id() != candidate_contract_node.id() =>
        {
            Some(Edge::contract_relation(
                EdgeKind::ContractEquivalent,
                added_contract_node.id(),
                candidate_contract_node.id(),
                vec![added.id.clone(), candidate.id.clone()],
                contract_relation_derivation(),
                recorded_at,
            ))
        }
        ContractRelation::Equivalent => None,
        ContractRelation::Incomparable => None,
    };
    if let Some(edge) = edge {
        let edge = edge.expect("contract judgments map to valid contract edges");
        report.semantic_edges_inserted += usize::from(store.append_edge(&edge)?);
    }
    Ok(())
}

fn persist_discharge_candidates(
    first: &Node,
    second: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    report: &mut GenerationReport,
) -> Result<(), StoreError> {
    for (source, target) in [(first, second), (second, first)] {
        let source_contract = crate::pairing::current_formed_contract(store, source)
            .map_err(|error| StoreError::Backend(error.to_string()))?;
        let Some(source_contract) = source_contract else {
            continue;
        };
        let pairing_edges =
            store.list_pairing_edges(target.id.as_str(), &crate::pairing::derivation())?;
        let mut relied_ids: Vec<String> = pairing_edges
            .iter()
            .filter(|edge| edge.kind != EdgeKind::AdmissibilityEnvelope)
            .filter_map(|edge| edge.relied_spec_id.clone())
            .collect();
        relied_ids.sort();
        relied_ids.dedup();
        for relied_id in relied_ids {
            let Some(relied) = store.get_node(&relied_id)? else {
                continue;
            };
            let Some(relied_sentence) = parse_current(&relied) else {
                continue;
            };
            let Some(relied_formula) = assertion_formula(&relied_sentence) else {
                continue;
            };
            if !source_contract
                .semantic()
                .guarantee
                .entails(&so_reason::contract::Assertion::from(&relied_formula))
            {
                continue;
            }
            let (left, right) = ordered_ids(&source.id, &target.id);
            let assessment = assessment_record(
                left,
                right,
                Derivation {
                    method: DISCHARGE_CANDIDATE_METHOD.to_string(),
                    version: DISCHARGE_CANDIDATE_VERSION.to_string(),
                },
                AssessmentVerdict::DischargeCandidate {
                    source: source.id.clone(),
                    target: target.id.clone(),
                    relied_spec_id: relied_id.clone(),
                },
                recorded_at,
                &[&relied_id],
            );
            report.assessments_inserted +=
                usize::from(store.append_relation_assessment(&assessment)?);
        }
    }
    Ok(())
}

fn ordered_ids<'a>(a: &'a str, b: &'a str) -> (&'a str, &'a str) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn assessment_record(
    left: &str,
    right: &str,
    semantic_derivation: Derivation,
    verdict: AssessmentVerdict,
    recorded_at: &str,
    identity_basis: &[&str],
) -> RelationAssessment {
    let candidate_derivation = candidate_derivation();
    let mut identity = vec![
        candidate_derivation.method.as_str(),
        candidate_derivation.version.as_str(),
        semantic_derivation.method.as_str(),
        semantic_derivation.version.as_str(),
        left,
        right,
    ];
    identity.extend_from_slice(identity_basis);
    RelationAssessment {
        id: stable_id("assessment", &identity),
        left: left.to_string(),
        right: right.to_string(),
        candidate_derivation,
        semantic_derivation,
        verdict,
        recorded_at: recorded_at.to_string(),
    }
}

fn verdict_name(verdict: RelationVerdict) -> &'static str {
    match verdict {
        RelationVerdict::HardContradiction => "hard_contradiction",
        RelationVerdict::AdvisoryTension => "advisory_tension",
        RelationVerdict::DescriptiveConflict => "descriptive_conflict",
        RelationVerdict::Refinement { .. } => "refinement",
        RelationVerdict::Equivalent => "equivalent",
        RelationVerdict::Independent => "independent",
        RelationVerdict::EnvelopeConflict => "envelope_conflict",
        RelationVerdict::Unknown => "unknown",
    }
}

fn semantic_edge(
    added: &Node,
    candidate: &Node,
    verdict: RelationVerdict,
    recorded_at: &str,
) -> Option<Edge> {
    let (kind, source, target) = match verdict {
        RelationVerdict::Refinement {
            concrete_is_a: true,
        } => (EdgeKind::Refines, added.id.as_str(), candidate.id.as_str()),
        RelationVerdict::Refinement {
            concrete_is_a: false,
        } => (EdgeKind::Refines, candidate.id.as_str(), added.id.as_str()),
        RelationVerdict::Equivalent => symmetric_endpoints(EdgeKind::Equivalent, added, candidate),
        RelationVerdict::HardContradiction => {
            symmetric_endpoints(EdgeKind::HardContradiction, added, candidate)
        }
        RelationVerdict::AdvisoryTension => {
            symmetric_endpoints(EdgeKind::AdvisoryTension, added, candidate)
        }
        RelationVerdict::DescriptiveConflict => {
            symmetric_endpoints(EdgeKind::DescriptiveConflict, added, candidate)
        }
        RelationVerdict::EnvelopeConflict => {
            symmetric_endpoints(EdgeKind::EnvelopeConflict, added, candidate)
        }
        RelationVerdict::Independent | RelationVerdict::Unknown => return None,
    };
    let derivation = semantic_edge_derivation();
    Some(
        Edge::specification_relation(kind, source, target, Vec::new(), derivation, recorded_at)
            .expect("semantic verdicts always map to valid specification relationships"),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, MetaUpdate, VertexKind};
    use crate::store::{GraphStore, InMemoryNodeStore, NodeStore};
    use serde_json::json;

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
        assert_eq!(report.verdicts.get("unknown"), Some(&1));
        assert_eq!(
            report.assessments_inserted, 3,
            "sentence, formula, and A/G contract judgments are audited independently"
        );
        let audit = relation_assessment(&b, &a, RelationVerdict::Unknown, "ignored");
        let stored = store
            .get_relation_assessment(&audit.id)
            .unwrap()
            .expect("Unknown is audited outside topology");
        assert_eq!(stored.verdict, AssessmentVerdict::Unknown);
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
        assert_eq!(first.contract_nodes_inserted, 3);
        assert_eq!(first.contract_edges_inserted, 3);
        assert_eq!(second.contract_nodes_inserted, 0);
        assert_eq!(second.contract_edges_inserted, 3);

        let projection_edges: Vec<Edge> = store
            .list_edges(
                &["a".into(), "b".into()],
                &[contract_projection_derivation()],
            )
            .unwrap();
        assert_eq!(projection_edges.len(), 6);
        let mut ids: Vec<String> = projection_edges
            .iter()
            .map(|edge| edge.target.clone())
            .collect();
        ids.sort();
        ids.dedup();
        assert_eq!(
            ids.len(),
            3,
            "both specifications share the same A, G, and Contract nodes"
        );
        let nodes = store.get_derived_nodes(&ids).unwrap();
        assert!(nodes.iter().any(
            |node| matches!(node, DerivedNode::Assumption { expression, .. } if expression == "⊤")
        ));
        assert!(nodes.iter().any(|node| {
            matches!(node, DerivedNode::Guarantee { expression, force, .. }
                if expression == "the pump shall stop." && force == "binding")
        }));
        assert!(nodes
            .iter()
            .any(|node| matches!(node, DerivedNode::Contract { .. })));
    }

    #[test]
    fn contract_reconciliation_completes_for_unparseable_stored_nodes() {
        let store = InMemoryNodeStore::new();
        let valid = node("valid", "The pump shall stop.");
        let unparseable = node(
            "unparseable",
            "When the client sends telemetry, the fan shall run.",
        );
        store.add_node(&valid).unwrap();
        store.add_node(&unparseable).unwrap();

        let valid_report = reconcile_contract_relations_only(&valid, &store, "t1").unwrap();
        assert!(valid_report.subject_has_contract);
        assert!(!valid_report.subject_unassessable);
        assert_eq!(valid_report.candidates_unassessable, 1);

        let unparseable_report =
            reconcile_contract_relations_only(&unparseable, &store, "t2").unwrap();
        assert!(!unparseable_report.subject_has_contract);
        assert!(unparseable_report.subject_unassessable);
        assert_eq!(unparseable_report.assessments_inserted, 0);
        assert_eq!(unparseable_report.semantic_edges_inserted, 0);
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
        assert_eq!(report.verdicts.get("refinement"), Some(&1));
        assert_eq!(
            report.assessments_inserted, 3,
            "sentence, formula, and A/G contract judgments are audited independently"
        );
        assert_eq!(report.semantic_edges_inserted, 1);

        // Reassessment is harmless: the stable derivation-derived ID makes the
        // append a no-op while the proved relation remains current.
        let retry = generate_and_persist(&concrete, &store, "t3").unwrap();
        assert_eq!(retry.assessments_inserted, 0);
        assert_eq!(retry.semantic_edges_inserted, 0);
    }

    #[test]
    fn symmetric_verdicts_canonicalize_endpoints_and_unknown_is_not_an_edge() {
        let a = node("z", "The pump shall stop.");
        let b = node("a", "The pump shall stop.");
        let equivalent = semantic_edge(&a, &b, RelationVerdict::Equivalent, "t").unwrap();
        assert_eq!(equivalent.kind, EdgeKind::Equivalent);
        assert_eq!(
            (equivalent.source.as_str(), equivalent.target.as_str()),
            ("a", "z")
        );
        let reverse = semantic_edge(&b, &a, RelationVerdict::Equivalent, "later").unwrap();
        assert_eq!(equivalent.id, reverse.id);

        for verdict in [RelationVerdict::Independent, RelationVerdict::Unknown] {
            assert!(semantic_edge(&a, &b, verdict, "t").is_none());
        }
    }

    #[test]
    fn every_proved_conflict_family_maps_to_a_symmetric_edge_kind() {
        let a = node("b", "The pump shall stop.");
        let b = node("a", "The pump shall not stop.");
        for (verdict, expected) in [
            (
                RelationVerdict::HardContradiction,
                EdgeKind::HardContradiction,
            ),
            (RelationVerdict::AdvisoryTension, EdgeKind::AdvisoryTension),
            (
                RelationVerdict::DescriptiveConflict,
                EdgeKind::DescriptiveConflict,
            ),
            (
                RelationVerdict::EnvelopeConflict,
                EdgeKind::EnvelopeConflict,
            ),
        ] {
            let edge = semantic_edge(&a, &b, verdict, "t").unwrap();
            assert_eq!(edge.kind, expected);
            assert_eq!((edge.source.as_str(), edge.target.as_str()), ("a", "b"));
            assert_eq!(edge.source_role, EndpointRole::ConflictPeer);
            assert_eq!(edge.target_role, EndpointRole::ConflictPeer);
            assert!(!edge.kind.directed());
        }
    }
}
