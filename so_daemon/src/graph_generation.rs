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

use std::collections::{BTreeMap, BTreeSet};

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
pub const GENERATION_VERSION: &str = "spec-graph/term-form-v4";
pub const CANDIDATE_METHOD: &str = "so-daemon.graph.multi-signal-candidates";
pub const CANDIDATE_VERSION: &str = "spec-graph/multi-signal-candidates-v2";
pub const LEXICAL_AFFINITY_METHOD: &str = "so-daemon.graph.lexical-affinity";
pub const LEXICAL_AFFINITY_VERSION: &str = "spec-graph/lexical-affinity-v1";
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
pub const COMPOSED_SUPPORT_METHOD: &str = "so-daemon.graph.composed-support";
pub const COMPOSED_SUPPORT_VERSION: &str = "spec-graph/composed-support-v2";
pub const OPERATIONAL_PROJECTION_METHOD: &str = "so-daemon.graph.operational-structure";
pub const OPERATIONAL_PROJECTION_VERSION: &str = "spec-graph/operational-structure-v2";
pub const DISCHARGE_CANDIDATE_METHOD: &str = "so-daemon.graph.discharge-candidates";
pub const DISCHARGE_CANDIDATE_VERSION: &str = "spec-graph/discharge-candidates-v1";
pub const RUN_VERSION: &str = "spec-graph/node-relations-v8";
const PLUGIN_NAME: &str = "graph-generation";
const CANDIDATE_PAGE_SIZE: usize = 500;
const CONTRACT_RECONCILIATION_PAGE_SIZE: usize = 10_000;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GenerationReport {
    pub terms_seen: usize,
    pub terms_inserted: usize,
    pub mention_edges_inserted: usize,
    pub contract_nodes_inserted: usize,
    pub contract_edges_inserted: usize,
    pub operational_nodes_inserted: usize,
    pub operational_edges_inserted: usize,
    /// The reconciliation subject has a formed A/G contract.
    pub subject_has_contract: bool,
    /// The subject cannot be interpreted by the current language/reasoner.
    /// This is a durable applicability result, not a retryable store failure.
    pub subject_unassessable: bool,
    pub candidates_discovered: usize,
    pub candidates_examined: usize,
    pub candidates_unassessable: usize,
    pub assessments_inserted: usize,
    pub lexical_edges_inserted: usize,
    pub semantic_edges_inserted: usize,
    pub compositions_examined: usize,
    pub composition_proofs_inserted: usize,
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
        "{RUN_VERSION};term={GENERATION_VERSION};operational={};candidates={CANDIDATE_VERSION};lexical-edge={};assessment={SEMANTIC_DERIVATION_VERSION};semantic-edge={};composed-support={}",
        operational_projection_derivation().version,
        lexical_affinity_derivation().version,
        semantic_edge_derivation().version,
        composed_support_derivation().version
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

pub fn lexical_affinity_derivation() -> Derivation {
    Derivation {
        method: LEXICAL_AFFINITY_METHOD.to_string(),
        version: format!(
            "{LEXICAL_AFFINITY_VERSION};term={GENERATION_VERSION};candidates={CANDIDATE_VERSION}"
        ),
    }
}

pub fn contract_projection_derivation() -> Derivation {
    Derivation {
        method: CONTRACT_PROJECTION_METHOD.to_string(),
        version: CONTRACT_PROJECTION_VERSION.to_string(),
    }
}

pub fn operational_projection_derivation() -> Derivation {
    Derivation {
        method: OPERATIONAL_PROJECTION_METHOD.to_string(),
        version: format!(
            "{OPERATIONAL_PROJECTION_VERSION};reason={}",
            so_reason::operational::OPERATIONAL_VERSION
        ),
    }
}

/// One selected version per Edge-producing method in the current graph view.
pub fn current_derivations() -> Vec<Derivation> {
    vec![
        term_derivation(),
        lexical_affinity_derivation(),
        semantic_edge_derivation(),
        crate::pairing::derivation(),
        contract_projection_derivation(),
        operational_projection_derivation(),
        contract_relation_derivation(),
        composed_support_derivation(),
        crate::contract_algebra::derivation(),
        crate::pairing::projection_derivation(),
        crate::evidence_capture::evidence_derivation(),
        crate::evidence_graph::derivation(),
    ]
}

pub fn contract_relation_derivation() -> Derivation {
    Derivation {
        method: CONTRACT_RELATION_METHOD.to_string(),
        version: format!("{CONTRACT_RELATION_VERSION};reason={CONTRACT_ASSESSMENT_VERSION}"),
    }
}

pub fn composed_support_derivation() -> Derivation {
    Derivation {
        method: COMPOSED_SUPPORT_METHOD.to_string(),
        version: format!(
            "{COMPOSED_SUPPORT_VERSION};algebra={};reason={CONTRACT_ASSESSMENT_VERSION}",
            crate::contract_algebra::DERIVATION_VERSION
        ),
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
                .pointer("/operational_projection/method")
                .and_then(Value::as_str)
                == Some(OPERATIONAL_PROJECTION_METHOD)
            && update
                .value
                .pointer("/operational_projection/version")
                .and_then(Value::as_str)
                == Some(operational_projection_derivation().version.as_str())
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
    let (term_ids, discovery_tokens) = candidate_signals(&occurrences);
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
    persist_operational_projection(added, &sentence, store, recorded_at, &mut report)?;

    // Candidate signals are only a discovery mechanism. Every returned pair
    // still goes through `assess`, and omitted pairs remain explicitly
    // unsearched—not independent and not Unknown.
    let mut cursor: Option<String> = None;
    loop {
        let page = store.list_relation_candidates(
            &term_ids,
            &discovery_tokens,
            &term_derivation(),
            &contract_projection_derivation(),
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
            if let Some(edge) = lexical_affinity_edge(
                added,
                &candidate,
                &term_ids,
                &discovery_tokens,
                &candidate_sentence,
                recorded_at,
            ) {
                report.lexical_edges_inserted += usize::from(store.append_edge(&edge)?);
            }
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

    let composition = derive_composed_support_for(added, store, recorded_at)?;
    merge_composition_report(&mut report, composition);
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
    persist_operational_projection(node, &sentence, store, recorded_at, &mut report)?;
    Ok(report)
}

fn persist_operational_projection(
    node: &Node,
    sentence: &so_lang::ast::Sentence,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    report: &mut GenerationReport,
) -> Result<(), StoreError> {
    let profile = so_reason::operational::operational_profile(sentence);
    if profile.witnesses.is_empty() && profile.engagements.is_empty() {
        return Ok(());
    }
    let derivation = operational_projection_derivation();
    let behavior = DerivedNode::behavior(&profile, so_reason::operational::OPERATIONAL_VERSION);
    let behavior_edge = Edge::projection(
        EdgeKind::HasBehavior,
        &node.id,
        behavior.id(),
        derivation.clone(),
        recorded_at,
    )
    .map_err(StoreError::InvalidEdge)?;
    let write = store.put_derived_node(&behavior, &behavior_edge)?;
    report.operational_nodes_inserted += usize::from(write.node_inserted);
    report.operational_edges_inserted += usize::from(write.edge_inserted);

    let mut roles: BTreeMap<(EdgeKind, so_reason::operational::EntityRef), (String, String)> =
        BTreeMap::new();
    for witness in &profile.witnesses {
        roles
            .entry((EdgeKind::WitnessesEntity, witness.entity.clone()))
            .or_insert_with(|| (witness.anchor.clone(), "operational_witness".into()));
    }
    for engagement in &profile.engagements {
        roles
            .entry((EdgeKind::EngagesEntity, engagement.entity.clone()))
            .or_insert_with(|| {
                (
                    engagement.anchor.clone(),
                    format!("operational_{:?}", engagement.site).to_lowercase(),
                )
            });
    }
    for ((kind, entity_ref), (anchor, role)) in roles {
        let entity = DerivedNode::entity(&entity_ref, so_reason::operational::OPERATIONAL_VERSION);
        let mut edge = Edge::operational_role(
            kind,
            behavior.id(),
            entity.id(),
            derivation.clone(),
            recorded_at,
        )
        .map_err(StoreError::InvalidEdge)?;
        edge.source_anchor = Some(TextAnchor {
            selector: "/operational".into(),
            text: anchor,
            role,
        });
        edge.basis_spec_ids = vec![node.id.clone()];
        edge.id = edge.identity_key();
        edge.validate().map_err(StoreError::InvalidEdge)?;
        let write = store.put_derived_node(&entity, &edge)?;
        report.operational_nodes_inserted += usize::from(write.node_inserted);
        report.operational_edges_inserted += usize::from(write.edge_inserted);
    }
    Ok(())
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
    persist_semantic_relations_work(added, store, recorded_at)
}

pub(crate) fn rebuild_semantic_relations_only(
    added: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    // Rebuild projection Consumers run concurrently. A Node's term projection
    // is guaranteed to exist before this function runs for that Node, but term
    // projections for lexically later Nodes are not. Searching only ids after
    // `added` can therefore permanently miss every pair: the later endpoint is
    // absent now, and its later rebuild would skip back over `added`.
    //
    // Search both directions during rebuild. Whichever endpoint is projected
    // second will discover the pair; if both relation tasks observe both
    // projections, content-derived Assessment and Edge identities make the
    // duplicate attempt idempotent.
    persist_semantic_relations_work(added, store, recorded_at)
}

fn persist_semantic_relations_work(
    added: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    let Some(sentence) = parse_current(added) else {
        return Ok(GenerationReport::default());
    };
    let occurrences = term_occurrences(added, &sentence);
    let (term_ids, discovery_tokens) = candidate_signals(&occurrences);
    let mut report = GenerationReport::default();
    let mut cursor = None;
    loop {
        let page = store.list_relation_candidates(
            &term_ids,
            &discovery_tokens,
            &term_derivation(),
            &contract_projection_derivation(),
            &added.id,
            cursor.as_deref(),
            CANDIDATE_PAGE_SIZE,
        )?;
        let mut assessments = Vec::new();
        for candidate in page.nodes {
            report.candidates_discovered += 1;
            let Some(candidate_sentence) = parse_current(&candidate) else {
                report.candidates_unassessable += 1;
                continue;
            };
            report.candidates_examined += 1;
            if let Some(edge) = lexical_affinity_edge(
                added,
                &candidate,
                &term_ids,
                &discovery_tokens,
                &candidate_sentence,
                recorded_at,
            ) {
                report.lexical_edges_inserted += usize::from(store.append_edge(&edge)?);
            }
            let verdict = assess(&sentence, &candidate_sentence);
            *report
                .verdicts
                .entry(verdict_name(verdict).to_string())
                .or_default() += 1;
            let assessment = relation_assessment(added, &candidate, verdict, recorded_at);
            assessments.push(assessment);
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
                assessments.push(formula_assessment);
            }
            if let Some(edge) = semantic_edge(added, &candidate, verdict, recorded_at) {
                report.semantic_edges_inserted += usize::from(store.append_edge(&edge)?);
            }
        }
        report.assessments_inserted += append_assessment_batches(store, &assessments)?;
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
    let mut report =
        reconcile_contract_work(changed, store, recorded_at, true, true, false, false)?;
    let composition = derive_composed_support_for(changed, store, recorded_at)?;
    merge_composition_report(&mut report, composition);
    Ok(report)
}

pub(crate) fn reconcile_contract_relations_only(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    let mut report =
        reconcile_contract_work(changed, store, recorded_at, true, false, false, false)?;
    let composition = derive_composed_support_for(changed, store, recorded_at)?;
    merge_composition_report(&mut report, composition);
    Ok(report)
}

pub(crate) fn rebuild_contract_relations_only(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    // A rebuild visits every authored Node, so assess each unordered pair from
    // only one endpoint. The relation assessment and symmetric relation Edge
    // already canonicalize their endpoints; visiting the reverse direction
    // can only repeat the same immutable writes and creates avoidable backend
    // lock contention when both endpoints are processed concurrently.
    let mut report = reconcile_contract_work(changed, store, recorded_at, true, false, true, true)?;
    let composition = derive_composed_support_for(changed, store, recorded_at)?;
    merge_composition_report(&mut report, composition);
    Ok(report)
}

pub(crate) fn reconcile_discharge_candidates_only(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    reconcile_contract_work(changed, store, recorded_at, false, true, false, false)
}

pub(crate) fn rebuild_discharge_candidates_only(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    reconcile_contract_work(changed, store, recorded_at, false, true, true, false)
}

#[derive(Clone)]
struct CompositionContract {
    specification_id: String,
    contract_node_id: String,
    contract: so_reason::contract::Contract,
    force: Option<so_reason::semantics::Force>,
}

/// Discover every candidate binary contract composition involving the changed
/// specification. A proved composition is persisted as the existing
/// algebra shape:
///
/// `operand contracts -> composed Contract -> refined target Contract`.
///
/// This is deliberately not a `Supports` Edge. The immutable algebra proof is
/// Ledger topology; selection later interprets its authored basis as one
/// multi-premise support clause.
fn derive_composed_support_for(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    let Some(changed_sentence) = parse_current(changed) else {
        return Ok(GenerationReport::default());
    };
    let occurrences = term_occurrences(changed, &changed_sentence);
    let (term_ids, discovery_tokens) = candidate_signals(&occurrences);
    let neighborhood = composition_neighborhood(changed, &term_ids, &discovery_tokens, store)?;

    let mut contracts = Vec::new();
    for node in neighborhood.into_values() {
        let Some(sentence) = parse_current(&node) else {
            continue;
        };
        let formed = match contract_for_reconciliation(store, &node)? {
            ReconciliationContract::Formed(contract) => contract,
            ReconciliationContract::NoContract | ReconciliationContract::Unassessable => continue,
        };
        let semantic = formed.semantic();
        let derived = DerivedNode::contract(&semantic, "formed", CONTRACT_PROJECTION_VERSION);
        contracts.push(CompositionContract {
            specification_id: node.id,
            contract_node_id: derived.id().to_string(),
            contract: semantic,
            force: so_reason::semantics::force(&sentence),
        });
    }
    let contract_ids: Vec<String> = contracts
        .iter()
        .map(|entry| entry.contract_node_id.clone())
        .collect();
    let persisted: BTreeSet<String> = store
        .get_derived_nodes(&contract_ids)?
        .into_iter()
        .map(|node| node.id().to_string())
        .collect();
    contracts.retain(|entry| persisted.contains(&entry.contract_node_id));
    contracts.sort_by(|left, right| left.specification_id.cmp(&right.specification_id));

    let mut report = GenerationReport::default();
    let mut persisted_compositions: BTreeMap<(String, String), String> = BTreeMap::new();
    for target_index in 0..contracts.len() {
        let target = &contracts[target_index];
        for left_index in 0..contracts.len() {
            for right_index in (left_index + 1)..contracts.len() {
                if target_index == left_index || target_index == right_index {
                    continue;
                }
                let left = &contracts[left_index];
                let right = &contracts[right_index];
                let changed_is_target = target.specification_id == changed.id;
                let changed_is_operand =
                    left.specification_id == changed.id || right.specification_id == changed.id;
                if !changed_is_target && !changed_is_operand {
                    continue;
                }
                if !force_can_support(left.force, target.force)
                    || !force_can_support(right.force, target.force)
                {
                    continue;
                }
                // Inclusion-minimal binary bases only. If either operand
                // already proves the target, materializing their composition
                // would turn a redundant path into apparent multi-source
                // support.
                if left.contract.refines(&target.contract)
                    || right.contract.refines(&target.contract)
                {
                    continue;
                }
                report.compositions_examined += 1;
                let composed = left.contract.compose(&right.contract);
                if !composed.refines(&target.contract) {
                    continue;
                }

                let pair = if left.contract_node_id <= right.contract_node_id {
                    (
                        left.contract_node_id.clone(),
                        right.contract_node_id.clone(),
                    )
                } else {
                    (
                        right.contract_node_id.clone(),
                        left.contract_node_id.clone(),
                    )
                };
                let result_id = if let Some(id) = persisted_compositions.get(&pair) {
                    id.clone()
                } else {
                    let result = crate::contract_algebra::derive(
                        store,
                        &pair.0,
                        &pair.1,
                        crate::contract_algebra::Operation::Composition,
                        vec![],
                        recorded_at,
                    )
                    .map_err(|error| StoreError::Backend(error.to_string()))?;
                    let id = result.contract.id().to_string();
                    persisted_compositions.insert(pair, id.clone());
                    id
                };
                let proof = Edge::contract_relation(
                    EdgeKind::ContractRefines,
                    &result_id,
                    &target.contract_node_id,
                    vec![
                        left.specification_id.clone(),
                        right.specification_id.clone(),
                        target.specification_id.clone(),
                    ],
                    composed_support_derivation(),
                    recorded_at,
                )
                .map_err(StoreError::InvalidEdge)?;
                let inserted = store.append_edge(&proof)?;
                report.composition_proofs_inserted += usize::from(inserted);
                report.semantic_edges_inserted += usize::from(inserted);
            }
        }
    }
    Ok(report)
}

fn composition_neighborhood(
    changed: &Node,
    term_ids: &[String],
    discovery_tokens: &[String],
    store: &(dyn GraphStore + Send + Sync),
) -> Result<BTreeMap<String, Node>, StoreError> {
    let mut neighborhood = BTreeMap::from([(changed.id.clone(), changed.clone())]);
    let mut cursor = None;
    loop {
        let page = store.list_relation_candidates(
            term_ids,
            discovery_tokens,
            &term_derivation(),
            &contract_projection_derivation(),
            &changed.id,
            cursor.as_deref(),
            CANDIDATE_PAGE_SIZE,
        )?;
        for candidate in page.nodes {
            neighborhood.insert(candidate.id.clone(), candidate);
        }
        match page.next_cursor {
            Some(next) => cursor = Some(next),
            None => return Ok(neighborhood),
        }
    }
}

fn force_can_support(
    concrete: Option<so_reason::semantics::Force>,
    abstract_: Option<so_reason::semantics::Force>,
) -> bool {
    use so_reason::semantics::Force::{Binding, Recommended};
    matches!(
        (concrete, abstract_),
        (Some(Binding), _) | (Some(Recommended), Some(Recommended)) | (None, None)
    )
}

fn merge_composition_report(target: &mut GenerationReport, source: GenerationReport) {
    target.compositions_examined += source.compositions_examined;
    target.composition_proofs_inserted += source.composition_proofs_inserted;
    target.semantic_edges_inserted += source.semantic_edges_inserted;
}

fn reconcile_contract_work(
    changed: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
    assess_relations: bool,
    assess_discharges: bool,
    unordered_pair_once: bool,
    bounded_relation_candidates: bool,
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
    let assess_discharges =
        assess_discharges && store.has_pairing_edges(&crate::pairing::derivation())?;
    if !assess_relations && !assess_discharges {
        return Ok(report);
    }
    let candidate_signals = if bounded_relation_candidates {
        let Some(sentence) = parse_current(changed) else {
            return Ok(report);
        };
        let occurrences = term_occurrences(changed, &sentence);
        Some(candidate_signals(&occurrences))
    } else {
        None
    };
    // `list_relation_candidates` uses an exclusive keyset cursor. During a
    // rebuild this skips every reverse endpoint at the database boundary,
    // avoiding both redundant reasoning and empty pages discarded in Rust.
    let mut cursor = unordered_pair_once.then(|| changed.id.clone());
    loop {
        let page = if let Some((term_ids, discovery_tokens)) = candidate_signals.as_ref() {
            store.list_relation_candidates(
                term_ids,
                discovery_tokens,
                &term_derivation(),
                &contract_projection_derivation(),
                &changed.id,
                cursor.as_deref(),
                CANDIDATE_PAGE_SIZE,
            )?
        } else {
            store.list_nodes(cursor.as_deref(), CONTRACT_RECONCILIATION_PAGE_SIZE)?
        };
        let next_cursor = page.next_cursor;
        let candidates: Vec<Node> = page
            .nodes
            .into_iter()
            .filter(|candidate| {
                candidate.id != changed.id
                    && (!unordered_pair_once || candidate.id.as_str() > changed.id.as_str())
            })
            .collect();
        let candidate_ids: Vec<String> = candidates
            .iter()
            .map(|candidate| candidate.id.clone())
            .collect();
        let pairing_edges =
            store.list_pairing_edges_for_targets(&candidate_ids, &crate::pairing::derivation())?;
        let (assessments, relation_edges) = if assess_relations && !assess_discharges {
            let batch = assess_contract_relation_candidates(
                store,
                changed,
                &changed_contract_node,
                &candidates,
                &pairing_edges,
                recorded_at,
            )?;
            report.candidates_unassessable += batch.unassessable;
            (batch.assessments, batch.edges)
        } else {
            let mut assessments = Vec::new();
            let mut relation_edges = Vec::new();
            for candidate in candidates {
                let candidate_pairings = pairing_edges
                    .get(&candidate.id)
                    .map(Vec::as_slice)
                    .unwrap_or_default();
                let candidate_contract = match contract_for_reconciliation_with_edges(
                    store,
                    &candidate,
                    candidate_pairings,
                )? {
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
                    let (assessment, edge) = contract_assessment_and_edge(
                        changed,
                        &changed_contract_node,
                        &candidate,
                        &candidate_contract_node,
                        recorded_at,
                    );
                    assessments.push(assessment);
                    relation_edges.extend(edge);
                }
                if assess_discharges {
                    persist_discharge_candidates(
                        changed,
                        &candidate,
                        store,
                        recorded_at,
                        &mut report,
                    )?;
                }
            }
            (assessments, relation_edges)
        };
        report.assessments_inserted += append_assessment_batches(store, &assessments)?;
        for edge in relation_edges {
            report.semantic_edges_inserted += usize::from(store.append_edge(&edge)?);
        }
        match next_cursor {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    Ok(report)
}

#[derive(Default)]
struct ContractRelationBatch {
    assessments: Vec<RelationAssessment>,
    edges: Vec<Edge>,
    unassessable: usize,
}

fn assess_contract_relation_candidates(
    store: &(dyn GraphStore + Send + Sync),
    changed: &Node,
    changed_contract_node: &DerivedNode,
    candidates: &[Node],
    pairing_edges: &BTreeMap<String, Vec<Edge>>,
    recorded_at: &str,
) -> Result<ContractRelationBatch, StoreError> {
    const MAX_WORKERS: usize = 8;
    const MIN_CHUNK_SIZE: usize = 250;

    if candidates.is_empty() {
        return Ok(ContractRelationBatch::default());
    }
    let available = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let workers = available
        .min(MAX_WORKERS)
        .min(candidates.len().div_ceil(MIN_CHUNK_SIZE));
    let chunk_size = candidates.len().div_ceil(workers);
    std::thread::scope(|scope| {
        let handles: Vec<_> = candidates
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(move || {
                    let mut batch = ContractRelationBatch::default();
                    for candidate in chunk {
                        let candidate_pairings = pairing_edges
                            .get(&candidate.id)
                            .map(Vec::as_slice)
                            .unwrap_or_default();
                        let candidate_contract = match contract_for_reconciliation_with_edges(
                            store,
                            candidate,
                            candidate_pairings,
                        )? {
                            ReconciliationContract::Formed(contract) => contract,
                            ReconciliationContract::NoContract => continue,
                            ReconciliationContract::Unassessable => {
                                batch.unassessable += 1;
                                continue;
                            }
                        };
                        let candidate_contract_node = DerivedNode::contract(
                            &candidate_contract.semantic(),
                            "formed",
                            CONTRACT_PROJECTION_VERSION,
                        );
                        let (assessment, edge) = contract_assessment_and_edge(
                            changed,
                            changed_contract_node,
                            candidate,
                            &candidate_contract_node,
                            recorded_at,
                        );
                        batch.assessments.push(assessment);
                        batch.edges.extend(edge);
                    }
                    Ok::<_, StoreError>(batch)
                })
            })
            .collect();
        handles
            .into_iter()
            .try_fold(ContractRelationBatch::default(), |mut merged, handle| {
                let batch = handle.join().map_err(|_| {
                    StoreError::Backend("parallel contract-assessment worker panicked".into())
                })??;
                merged.assessments.extend(batch.assessments);
                merged.edges.extend(batch.edges);
                merged.unassessable += batch.unassessable;
                Ok(merged)
            })
    })
}

fn append_assessment_batches(
    store: &(dyn GraphStore + Send + Sync),
    assessments: &[RelationAssessment],
) -> Result<usize, StoreError> {
    const MAX_WORKERS: usize = 8;
    const MIN_BATCH_SIZE: usize = 500;

    if assessments.len() <= MIN_BATCH_SIZE {
        return store.append_relation_assessments(assessments);
    }
    let available = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let workers = available
        .min(MAX_WORKERS)
        .min(assessments.len().div_ceil(MIN_BATCH_SIZE));
    let chunk_size = assessments.len().div_ceil(workers);
    std::thread::scope(|scope| {
        let handles: Vec<_> = assessments
            .chunks(chunk_size)
            .map(|chunk| scope.spawn(move || store.append_relation_assessments(chunk)))
            .collect();
        handles.into_iter().try_fold(0, |inserted, handle| {
            handle
                .join()
                .map_err(|_| {
                    StoreError::Backend(
                        "parallel relation-assessment persistence worker panicked".into(),
                    )
                })?
                .map(|count| inserted + count)
        })
    })
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

fn contract_for_reconciliation_with_edges(
    store: &(dyn GraphStore + Send + Sync),
    node: &Node,
    pairing_edges: &[Edge],
) -> Result<ReconciliationContract, StoreError> {
    match crate::pairing::formed_contract_with_pairing_edges(store, node, pairing_edges) {
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
    let (assessment, edge) = contract_assessment_and_edge(
        added,
        added_contract_node,
        candidate,
        candidate_contract_node,
        recorded_at,
    );
    report.assessments_inserted += usize::from(store.append_relation_assessment(&assessment)?);
    if let Some(edge) = edge {
        report.semantic_edges_inserted += usize::from(store.append_edge(&edge)?);
    }
    Ok(())
}

fn contract_assessment_and_edge(
    added: &Node,
    added_contract_node: &DerivedNode,
    candidate: &Node,
    candidate_contract_node: &DerivedNode,
    recorded_at: &str,
) -> (RelationAssessment, Option<Edge>) {
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
    let edge = edge.map(|edge| edge.expect("contract judgments map to valid contract edges"));
    (assessment, edge)
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

fn lexical_affinity_edge(
    added: &Node,
    candidate: &Node,
    added_term_ids: &[String],
    added_tokens: &[String],
    candidate_sentence: &so_lang::ast::Sentence,
    recorded_at: &str,
) -> Option<Edge> {
    let candidate_occurrences = term_occurrences(candidate, candidate_sentence);
    let (candidate_term_ids, candidate_tokens) = candidate_signals(&candidate_occurrences);
    let exact_term = sorted_intersects(added_term_ids, &candidate_term_ids);
    let shared_tokens = sorted_intersection_count(added_tokens, &candidate_tokens);
    if !exact_term && shared_tokens < 2 {
        return None;
    }
    let (source, target) = ordered_ids(&added.id, &candidate.id);
    Edge::lexical_relation(source, target, lexical_affinity_derivation(), recorded_at).ok()
}

fn sorted_intersects(left: &[String], right: &[String]) -> bool {
    sorted_intersection_count(left, right) > 0
}

fn sorted_intersection_count(left: &[String], right: &[String]) -> usize {
    let (mut left_index, mut right_index, mut count) = (0, 0, 0);
    while left_index < left.len() && right_index < right.len() {
        match left[left_index].cmp(&right[right_index]) {
            std::cmp::Ordering::Less => left_index += 1,
            std::cmp::Ordering::Greater => right_index += 1,
            std::cmp::Ordering::Equal => {
                count += 1;
                left_index += 1;
                right_index += 1;
            }
        }
    }
    count
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
                    let rendered = without_det.render();
                    let form = rendered.to_lowercase();
                    let head = np.head.to_lowercase();
                    let term = TermNode {
                        id: stable_id("term", &[&node.lang_version, GENERATION_VERSION, &form]),
                        form,
                        head,
                        discovery_tokens: normalize_discovery_tokens(&rendered),
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

fn candidate_signals(occurrences: &[TermOccurrence]) -> (Vec<String>, Vec<String>) {
    let mut term_ids: Vec<String> = occurrences
        .iter()
        .map(|occurrence| occurrence.term.id.clone())
        .collect();
    term_ids.sort();
    term_ids.dedup();
    let mut discovery_tokens: Vec<String> = occurrences
        .iter()
        .flat_map(|occurrence| occurrence.term.discovery_tokens.iter().cloned())
        .collect();
    discovery_tokens.sort();
    discovery_tokens.dedup();
    (term_ids, discovery_tokens)
}

fn normalize_discovery_tokens(value: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut current = String::new();
    let mut previous_lower_or_digit = false;
    for character in value.chars() {
        let boundary = character.is_uppercase() && previous_lower_or_digit && !current.is_empty();
        if boundary {
            words.push(std::mem::take(&mut current));
        }
        if character.is_alphanumeric() {
            current.extend(character.to_lowercase());
            previous_lower_or_digit = character.is_lowercase() || character.is_ascii_digit();
        } else {
            if !current.is_empty() {
                words.push(std::mem::take(&mut current));
            }
            previous_lower_or_digit = false;
        }
    }
    if !current.is_empty() {
        words.push(current);
    }
    let mut normalized: Vec<String> = words
        .into_iter()
        .map(|word| {
            if word == "spec" {
                "specification".to_string()
            } else {
                word
            }
        })
        .filter(|word| {
            word.len() >= 2
                && !matches!(
                    word.as_str(),
                    "a" | "an"
                        | "the"
                        | "of"
                        | "to"
                        | "in"
                        | "on"
                        | "at"
                        | "by"
                        | "for"
                        | "from"
                        | "with"
                        | "through"
                        | "and"
                        | "or"
                        | "one"
                        | "each"
                        | "every"
                        | "any"
                        | "no"
                )
        })
        .collect();
    normalized.sort();
    normalized.dedup();
    normalized
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
    fn term_stage_persists_typed_operational_projection() {
        let store = InMemoryNodeStore::new();
        let value = node(
            "s1",
            "an AddSpecification RPC shall submit an AddNode Command.",
        );
        store.add_node(&value).unwrap();
        let report = persist_term_projection_only(&value, &store, "2026-01-01T00:00:00Z").unwrap();
        assert_eq!(report.operational_nodes_inserted, 3);
        assert_eq!(report.operational_edges_inserted, 3);

        let edges = store
            .list_edges(&["s1".into()], &current_derivations())
            .unwrap();
        assert!(edges.iter().any(|edge| edge.kind == EdgeKind::HasBehavior));
        assert!(edges
            .iter()
            .any(|edge| edge.kind == EdgeKind::WitnessesEntity));
        assert!(edges
            .iter()
            .any(|edge| edge.kind == EdgeKind::EngagesEntity));
        let derived_ids: Vec<String> = edges
            .iter()
            .filter(|edge| matches!(edge.target_kind, VertexKind::Behavior | VertexKind::Entity))
            .map(|edge| edge.target.clone())
            .collect();
        let derived = store.get_derived_nodes(&derived_ids).unwrap();
        assert!(derived
            .iter()
            .any(|node| node.vertex_kind() == VertexKind::Behavior));
        assert!(derived
            .iter()
            .any(|node| node.vertex_kind() == VertexKind::Entity));
    }

    #[test]
    fn composition_neighborhood_reads_every_candidate_without_a_count_cutoff() {
        let store = InMemoryNodeStore::new();
        let values: Vec<Node> = (0..70)
            .map(|index| node(&format!("candidate-{index:03}"), "The pump shall stop."))
            .collect();
        for value in &values {
            store.add_node(value).unwrap();
            persist_term_projection_only(value, &store, "2026-01-01T00:00:00Z").unwrap();
        }
        let changed = &values[0];
        let sentence = parse_current(changed).unwrap();
        let occurrences = term_occurrences(changed, &sentence);
        let (term_ids, discovery_tokens) = candidate_signals(&occurrences);

        let neighborhood =
            composition_neighborhood(changed, &term_ids, &discovery_tokens, &store).unwrap();
        assert_eq!(neighborhood.len(), values.len());
        assert_eq!(
            neighborhood.keys().cloned().collect::<BTreeSet<_>>(),
            values
                .iter()
                .map(|value| value.id.clone())
                .collect::<BTreeSet<_>>()
        );
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
                    "operational_projection": {
                        "method": OPERATIONAL_PROJECTION_METHOD,
                        "version": operational_projection_derivation().version,
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
    fn stop_command_keeps_its_term_hub_and_a_separate_weak_lexical_fact() {
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
        let lexical = edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::SameLexeme)
            .collect::<Vec<_>>();
        assert_eq!(lexical.len(), 1);
        assert!(!edges.iter().any(|edge| {
            edge.source_kind == VertexKind::Specification
                && edge.target_kind == VertexKind::Specification
                && edge.family() == crate::domain::EdgeFamily::Semantic
        }));
        assert_eq!(report.candidates_examined, 1);
        assert_eq!(report.lexical_edges_inserted, 1);
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
    fn candidate_discovery_unions_normalized_lexical_atoms_without_asserting_an_edge() {
        let store = InMemoryNodeStore::new();
        let request = node(
            "request",
            "The client shall encode the Add input in an Add Specification request message.",
        );
        let rpc = node(
            "rpc",
            "An AddSpecification RPC shall submit an AddNode Command.",
        );
        store.add_node(&request).unwrap();
        store.add_node(&rpc).unwrap();
        generate_and_persist(&request, &store, "t1").unwrap();
        let report = generate_and_persist(&rpc, &store, "t2").unwrap();

        assert_eq!(report.candidates_examined, 1);
        assert_eq!(report.verdicts.get("unknown"), Some(&1));
        let specification_relations = store
            .list_edges(&["request".into(), "rpc".into()], &current_derivations())
            .unwrap()
            .into_iter()
            .filter(|edge| {
                edge.source_kind == VertexKind::Specification
                    && edge.target_kind == VertexKind::Specification
            })
            .collect::<Vec<_>>();
        assert!(
            specification_relations
                .iter()
                .all(|edge| edge.kind == EdgeKind::SameLexeme),
            "multi-signal discovery must not turn lexical affinity into semantic topology"
        );
        assert_eq!(report.lexical_edges_inserted, 1);
        assert_eq!(
            normalize_discovery_tokens("AddSpecification RPC"),
            vec!["add", "rpc", "specification"]
        );
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
    fn two_minimal_contracts_are_composed_into_support_for_one_upper_contract() {
        let store = InMemoryNodeStore::new();
        let upper = node(
            "upper",
            "The report and the invoice shall be stored in the archive.",
        );
        let report = node("report", "The report shall be stored in the archive.");
        let invoice = node("invoice", "The invoice shall be stored in the archive.");
        for value in [&upper, &report, &invoice] {
            store.add_node(value).unwrap();
        }

        generate_and_persist(&upper, &store, "t1").unwrap();
        generate_and_persist(&report, &store, "t2").unwrap();
        let before = store
            .selection_population(&["upper".into()], &current_derivations())
            .unwrap();
        let before_view = crate::selection::derive_views(&["upper".into()], &before);
        assert_eq!(before_view["upper"].structural_score, 0);

        let generated = generate_and_persist(&invoice, &store, "t3").unwrap();
        assert_eq!(generated.composition_proofs_inserted, 1);
        let edges = store
            .list_edges(
                &["upper".into(), "report".into(), "invoice".into()],
                &current_derivations(),
            )
            .unwrap();
        let operands: Vec<&Edge> = edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::CompositionOperand)
            .collect();
        assert_eq!(operands.len(), 2);
        assert_eq!(operands[0].target, operands[1].target);
        let proof = edges
            .iter()
            .find(|edge| {
                edge.kind == EdgeKind::ContractRefines
                    && edge.derivation == composed_support_derivation()
            })
            .expect("the composed contract refines the authored upper contract");
        assert_eq!(proof.source, operands[0].target);
        assert_eq!(proof.basis_spec_ids, vec!["invoice", "report", "upper"]);

        let after = store
            .selection_population(&["upper".into()], &current_derivations())
            .unwrap();
        let after_view = crate::selection::derive_views(&["upper".into()], &after);
        assert!(after_view["upper"].structural_score > 0);
        assert!(
            after_view["upper"]
                .contributions
                .iter()
                .any(|contribution| {
                    contribution.detail.contains("invoice")
                        && contribution.detail.contains("report")
                }),
            "{:?}",
            after_view["upper"].contributions
        );

        let retry = generate_and_persist(&invoice, &store, "t4").unwrap();
        assert_eq!(retry.composition_proofs_inserted, 0);
    }

    #[test]
    fn same_action_discovery_builds_a_recursive_realization_view_without_support_edges() {
        let store = InMemoryNodeStore::new();
        let rpc = node(
            "rpc",
            "The Add RPC shall accept exactly one constrained-language specification sentence.",
        );
        let operation = node(
            "operation",
            "The `spec add` operation shall accept exactly one language sentence.",
        );
        let system = node(
            "system",
            "The system shall accept a constrained natural-language specification through `spec add`.",
        );
        for value in [&rpc, &operation, &system] {
            store.add_node(value).unwrap();
            generate_and_persist(value, &store, "t").unwrap();
        }

        let population = store
            .selection_population(&["system".into()], &current_derivations())
            .unwrap();
        assert_eq!(
            population
                .nodes
                .iter()
                .map(|node| node.id.as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["operation", "rpc", "system"])
        );
        let views = crate::selection::derive_views(&["system".into()], &population);
        assert!(views["system"].contributions.iter().any(|contribution| {
            contribution.kind == crate::domain::ScoreContributionKind::RealizationSupport
                && contribution.source_node_id.as_deref() == Some("rpc")
        }));
        assert!(
            population.relation_edges.iter().all(|edge| !matches!(
                edge.kind,
                EdgeKind::Refines
                    | EdgeKind::OccurrenceReliance
                    | EdgeKind::GuaranteeDischarge
                    | EdgeKind::AdmissibilityEnvelope
            )),
            "the realization relation is derived by the view, not persisted as a support Edge"
        );
    }

    #[test]
    fn entity_role_discovery_builds_cross_action_recursive_support() {
        let store = InMemoryNodeStore::new();
        let rpc = node(
            "rpc",
            "an AddSpecification RPC shall submit an AddNode Command.",
        );
        let command = node(
            "command",
            "the AddNode Command shall cause a NodeAdded Event.",
        );
        let consumer = node(
            "consumer",
            "When a NodeAdded Event is delivered, the term projection Consumer shall submit a ProjectNodeTerms Command.",
        );
        for value in [&rpc, &command, &consumer] {
            store.add_node(value).unwrap();
            generate_and_persist(value, &store, "t").unwrap();
        }

        let population = store
            .selection_population(&["rpc".into()], &current_derivations())
            .unwrap();
        assert_eq!(
            population
                .nodes
                .iter()
                .map(|node| node.id.as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["command", "consumer", "rpc"])
        );

        let views = crate::selection::derive_views(&["rpc".into()], &population);
        let roots: BTreeSet<_> = views["rpc"]
            .contributions
            .iter()
            .filter(|contribution| {
                contribution.kind == crate::domain::ScoreContributionKind::RealizationSupport
            })
            .filter_map(|contribution| contribution.source_node_id.as_deref())
            .collect();
        assert_eq!(roots, BTreeSet::from(["command", "consumer"]));
    }

    #[test]
    fn selection_population_walks_entity_roles_only_in_support_direction() {
        let store = InMemoryNodeStore::new();
        let upper = node("upper", "The daemon shall create a report.");
        let lower = node("lower", "The report shall contain a summary.");
        let means = node("means", "The renderer shall display a page using a report.");
        for value in [&upper, &lower, &means] {
            store.add_node(value).unwrap();
            generate_and_persist(value, &store, "t").unwrap();
        }

        let upper_population = store
            .selection_population(&["upper".into()], &current_derivations())
            .unwrap();
        assert_eq!(
            upper_population
                .nodes
                .iter()
                .map(|node| node.id.as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["lower", "upper"]),
            "a binding object discovers its subject elaboration but not a Means-only incidence"
        );

        let lower_population = store
            .selection_population(&["lower".into()], &current_derivations())
            .unwrap();
        assert_eq!(
            lower_population
                .nodes
                .iter()
                .map(|node| node.id.as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["lower"]),
            "support traversal must not reverse from an engagement to specifications that witness it"
        );
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

    #[test]
    fn rebuild_multi_signal_contract_candidates_are_idempotent() {
        let store = InMemoryNodeStore::new();
        let nodes = [
            node("a", "The pump shall stop."),
            node("b", "The pump shall stop."),
            node("c", "The pump shall stop."),
        ];
        for value in &nodes {
            store.add_node(value).unwrap();
            persist_term_projection_only(value, &store, "t").unwrap();
        }

        let reports: Vec<GenerationReport> = nodes
            .iter()
            .map(|value| rebuild_contract_relations_only(value, &store, "t").unwrap())
            .collect();
        assert_eq!(
            reports
                .iter()
                .map(|report| report.assessments_inserted)
                .collect::<Vec<_>>(),
            vec![2, 1, 0]
        );
        assert_eq!(
            store
                .list_relation_assessments(&["a".into(), "b".into(), "c".into()])
                .unwrap()
                .len(),
            3
        );
    }

    #[test]
    fn rebuild_semantic_candidates_cover_pairs_when_projections_arrive_in_order() {
        let store = InMemoryNodeStore::new();
        let nodes = [
            node("a", "The pump shall stop."),
            node("b", "The pump shall stop."),
            node("c", "The pump shall stop."),
        ];
        for value in &nodes {
            store.add_node(value).unwrap();
        }

        let reports: Vec<GenerationReport> = nodes
            .iter()
            .map(|value| {
                persist_term_projection_only(value, &store, "t").unwrap();
                rebuild_semantic_relations_only(value, &store, "t").unwrap()
            })
            .collect();
        assert_eq!(
            reports
                .iter()
                .map(|report| report.candidates_examined)
                .collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
        assert_eq!(
            store
                .list_relation_assessments(&["a".into(), "b".into(), "c".into()])
                .unwrap()
                .len(),
            6,
            "each of the three covered pairs has a semantic and formula audit"
        );
    }

    #[test]
    fn discharge_rebuild_short_circuits_without_pairing_edges() {
        let store = InMemoryNodeStore::new();
        let value = node("a", "The pump shall stop.");
        store.add_node(&value).unwrap();

        let report = rebuild_discharge_candidates_only(&value, &store, "t").unwrap();
        assert!(report.subject_has_contract);
        assert_eq!(report.assessments_inserted, 0);
    }

    #[test]
    fn assessment_batches_remain_idempotent_across_parallel_chunks() {
        let store = InMemoryNodeStore::new();
        let left = node("left", "The pump shall stop.");
        let assessments: Vec<RelationAssessment> = (0..501)
            .map(|index| {
                let right = node(&format!("right-{index:03}"), "The pump shall run.");
                relation_assessment(&left, &right, RelationVerdict::Unknown, "t")
            })
            .collect();

        assert_eq!(
            append_assessment_batches(&store, &assessments).unwrap(),
            501
        );
        assert_eq!(append_assessment_batches(&store, &assessments).unwrap(), 0);
    }
}
