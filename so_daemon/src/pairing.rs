//! Proved graph-side assume-guarantee pairing.
//!
//! A pairing Edge records three authored roles separately: `source` is the
//! evidence-bearing sentence, `target` owns the guarantee being conditioned,
//! and `relied_spec_id` names exactly what the target awaits. Only a
//! well-formed proven aggregate is appended. The Ledger remains append-only;
//! each accepted aggregate also appends a content-addressed Assumption
//! projection selected by the graph read path as the target's current A.

use thiserror::Error;

use crate::domain::{Derivation, DerivedNode, Edge, EdgeKind, Node};
use crate::store::{GraphStore, StoreError};
use so_reason::formula::{
    assertion_formula, contract_formula, AssumptionSource, ContractFormula,
    EdgeKind as ReasonEdgeKind, Formula, SubjectRelation,
};
use so_reason::relate::Ternary;

pub const DERIVATION_METHOD: &str = "so-daemon.contract.pairing";
pub const DERIVATION_VERSION: &str = "contract-pairing/v1;reason=so-reason/pairing-v1";
pub const PAIRED_PROJECTION_METHOD: &str = "so-daemon.graph.paired-contract";
pub const PAIRED_PROJECTION_VERSION: &str =
    "spec-graph/paired-contract-v1;reason=so-reason/pairing-v1";

pub fn derivation() -> Derivation {
    Derivation {
        method: DERIVATION_METHOD.to_string(),
        version: DERIVATION_VERSION.to_string(),
    }
}

pub fn projection_derivation() -> Derivation {
    Derivation {
        method: PAIRED_PROJECTION_METHOD.to_string(),
        version: PAIRED_PROJECTION_VERSION.to_string(),
    }
}

#[derive(Debug, Error)]
pub enum PairingError {
    #[error("assumption relations require occurrence_reliance, guarantee_discharge, or admissibility_envelope")]
    InvalidKind,
    #[error("an assumption relation cannot connect a specification to itself")]
    SelfRelation,
    #[error("basis specification '{0}' repeats a source, target, or relied specification already intrinsic to the relation")]
    BasisRepeatsIntrinsic(String),
    #[error("specification node '{0}' does not exist")]
    MissingNode(String),
    #[error("specification node '{id}' uses language version '{actual}', but pairing requires current version '{expected}'")]
    StaleLanguage {
        id: String,
        actual: String,
        expected: &'static str,
    },
    #[error("specification node '{id}' cannot be re-parsed: {message}")]
    InvalidSentence { id: String, message: String },
    #[error("target specification '{0}' has no guarantee contract")]
    TargetHasNoContract(String),
    #[error("relied specification '{0}' has no behavioral assertion")]
    ReliedHasNoAssertion(String),
    #[error("invalid assumption source: {0}")]
    InvalidSource(String),
    #[error("the source does not prove the explicitly relied assertion; an Unknown entailment cannot become Ledger topology")]
    RelianceNotProven,
    #[error("source and target share responsible-subject keys; textual keys cannot establish distinct component identity")]
    SharedSubjectKeys,
    #[error("a recommended source is candidate evidence only and cannot relieve a guarantee")]
    RecommendedSource,
    #[error("the aggregate paired assumption is provably unsatisfiable")]
    UnsatisfiableAssumption,
    #[error("the aggregate pairing is provably incompatible with its admissibility envelope")]
    IncompatibleEnvelope,
    #[error("the aggregate pairing contains a non-contract-forming assumption source")]
    NonContractFormingSource,
    #[error(transparent)]
    Store(#[from] StoreError),
}

impl PairingError {
    pub fn is_bad_input(&self) -> bool {
        !matches!(self, Self::Store(_))
    }
}

/// Validate, append, and materialize one proved pairing. Repeating the same
/// request returns the original Ledger Edge and repairs a missing derived
/// projection if a prior attempt was interrupted after the Edge append.
pub fn append_relation(
    store: &(dyn GraphStore + Send + Sync),
    kind: EdgeKind,
    source: &str,
    target: &str,
    relied: &str,
    basis_spec_ids: Vec<String>,
    recorded_at: &str,
) -> Result<Edge, PairingError> {
    let reason_kind = reason_kind(kind).ok_or(PairingError::InvalidKind)?;
    if source == target {
        return Err(PairingError::SelfRelation);
    }
    for id in &basis_spec_ids {
        if id == source || id == target || id == relied {
            return Err(PairingError::BasisRepeatsIntrinsic(id.clone()));
        }
    }

    let mut required = vec![source.to_string(), target.to_string(), relied.to_string()];
    required.extend(basis_spec_ids.iter().cloned());
    required.sort();
    required.dedup();
    for id in &required {
        if store.get_node(id)?.is_none() {
            return Err(PairingError::MissingNode(id.clone()));
        }
    }

    let source_node = required_node(store, source)?;
    let target_node = required_node(store, target)?;
    let relied_node = required_node(store, relied)?;
    let source_sentence = parse_current(&source_node)?;
    let target_sentence = parse_current(&target_node)?;
    let relied_sentence = parse_current(&relied_node)?;
    let target_contract = contract_formula(&target_sentence)
        .ok_or_else(|| PairingError::TargetHasNoContract(target.to_string()))?;
    let relied_formula = assertion_formula(&relied_sentence)
        .ok_or_else(|| PairingError::ReliedHasNoAssertion(relied.to_string()))?;
    let candidate = AssumptionSource::for_guarantee_with_relied(
        reason_kind,
        &source_sentence,
        &target_sentence,
        relied_formula,
    )
    .map_err(|error| PairingError::InvalidSource(error.to_string()))?;
    validate_source(&candidate)?;

    let proposed = Edge::assumption_relation(
        kind,
        source,
        target,
        relied,
        basis_spec_ids,
        derivation(),
        recorded_at,
    )
    .map_err(|message| PairingError::Store(StoreError::InvalidEdge(message)))?;

    let mut edges = store.list_pairing_edges(target, &derivation())?;
    let already_present = edges.iter().any(|edge| edge.id == proposed.id);
    let mut sources = pairing_sources(store, &target_sentence, &edges)?;
    if !already_present {
        sources.push(candidate);
    }
    validate_aggregate(&target_contract, &sources)?;

    store.append_edge(&proposed)?;
    if !already_present {
        edges.push(proposed.clone());
    }
    persist_current_assumption(store, &target_node, &target_sentence, &edges, recorded_at)?;

    store.get_edge(&proposed.id)?.ok_or_else(|| {
        PairingError::Store(StoreError::Backend(format!(
            "pairing Edge '{}' existed during append but could not be read back",
            proposed.id
        )))
    })
}

fn required_node(store: &(dyn GraphStore + Send + Sync), id: &str) -> Result<Node, PairingError> {
    store
        .get_node(id)?
        .ok_or_else(|| PairingError::MissingNode(id.to_string()))
}

fn parse_current(node: &Node) -> Result<so_lang::ast::Sentence, PairingError> {
    if node.lang_version != so_lang::LANG_VERSION {
        return Err(PairingError::StaleLanguage {
            id: node.id.clone(),
            actual: node.lang_version.clone(),
            expected: so_lang::LANG_VERSION,
        });
    }
    let parsed =
        so_lang::parse::parse(&node.statement).map_err(|error| PairingError::InvalidSentence {
            id: node.id.clone(),
            message: error.to_string(),
        })?;
    parsed
        .sentences
        .into_iter()
        .next()
        .ok_or_else(|| PairingError::InvalidSentence {
            id: node.id.clone(),
            message: "no sentence".to_string(),
        })
}

fn reason_kind(kind: EdgeKind) -> Option<ReasonEdgeKind> {
    match kind {
        EdgeKind::OccurrenceReliance => Some(ReasonEdgeKind::OccurrenceReliance),
        EdgeKind::GuaranteeDischarge => Some(ReasonEdgeKind::GuaranteeDischarge),
        EdgeKind::AdmissibilityEnvelope => Some(ReasonEdgeKind::AdmissibilityEnvelope),
        _ => None,
    }
}

fn validate_source(source: &AssumptionSource) -> Result<(), PairingError> {
    if source.kind == ReasonEdgeKind::AdmissibilityEnvelope {
        if !source.proven {
            return Err(PairingError::RelianceNotProven);
        }
        return Ok(());
    }
    if !source.proven {
        return Err(PairingError::RelianceNotProven);
    }
    if source.subject_relation == SubjectRelation::SharedKeys {
        return Err(PairingError::SharedSubjectKeys);
    }
    if source.force == Some(so_reason::semantics::Force::Recommended) {
        return Err(PairingError::RecommendedSource);
    }
    if !source.contract_forming() {
        return Err(PairingError::NonContractFormingSource);
    }
    Ok(())
}

fn pairing_sources(
    store: &(dyn GraphStore + Send + Sync),
    target_sentence: &so_lang::ast::Sentence,
    edges: &[Edge],
) -> Result<Vec<AssumptionSource>, PairingError> {
    let mut sources = Vec::with_capacity(edges.len());
    for edge in edges {
        let source_node = required_node(store, &edge.source)?;
        let relied_id = edge.relied_spec_id.as_deref().ok_or_else(|| {
            PairingError::Store(StoreError::InvalidEdge(format!(
                "pairing Edge '{}' has no relied specification",
                edge.id
            )))
        })?;
        let relied_node = required_node(store, relied_id)?;
        let source_sentence = parse_current(&source_node)?;
        let relied_sentence = parse_current(&relied_node)?;
        let relied_formula = assertion_formula(&relied_sentence)
            .ok_or_else(|| PairingError::ReliedHasNoAssertion(relied_id.to_string()))?;
        let source = AssumptionSource::for_guarantee_with_relied(
            reason_kind(edge.kind).ok_or(PairingError::InvalidKind)?,
            &source_sentence,
            target_sentence,
            relied_formula,
        )
        .map_err(|error| PairingError::InvalidSource(error.to_string()))?;
        validate_source(&source)?;
        sources.push(source);
    }
    Ok(sources)
}

fn validate_aggregate(
    target_contract: &ContractFormula,
    sources: &[AssumptionSource],
) -> Result<ContractFormula, PairingError> {
    let paired = target_contract.paired(sources);
    let verdict = paired.well_formed();
    if !verdict.all_sources_contract_forming {
        return Err(PairingError::NonContractFormingSource);
    }
    if verdict.assumption_satisfiability == Ternary::No {
        return Err(PairingError::UnsatisfiableAssumption);
    }
    if verdict.envelope_compatibility == Ternary::No {
        return Err(PairingError::IncompatibleEnvelope);
    }
    Ok(paired)
}

fn persist_current_assumption(
    store: &(dyn GraphStore + Send + Sync),
    target: &Node,
    target_sentence: &so_lang::ast::Sentence,
    edges: &[Edge],
    recorded_at: &str,
) -> Result<(), PairingError> {
    let target_contract = contract_formula(target_sentence)
        .ok_or_else(|| PairingError::TargetHasNoContract(target.id.clone()))?;
    let sources = pairing_sources(store, target_sentence, edges)?;
    let paired = validate_aggregate(&target_contract, &sources)?;
    if paired.assumption == Formula::Top {
        return Ok(());
    }
    let formula_json = serde_json::to_string(&paired.assumption).map_err(StoreError::Serialize)?;
    let mut relied_words = Vec::new();
    for edge in edges
        .iter()
        .filter(|edge| edge.kind != EdgeKind::AdmissibilityEnvelope)
    {
        if let Some(relied) = edge.relied_spec_id.as_deref() {
            relied_words.push(required_node(store, relied)?.statement);
        }
    }
    relied_words.sort();
    relied_words.dedup();
    let expression = match relied_words.as_slice() {
        [one] => one.clone(),
        many => many
            .iter()
            .map(|statement| format!("({statement})"))
            .collect::<Vec<_>>()
            .join(" ∧ "),
    };
    let node =
        DerivedNode::assumption_formula(&expression, &formula_json, PAIRED_PROJECTION_VERSION);
    let mut basis = Vec::new();
    for edge in edges {
        basis.push(edge.source.clone());
        if let Some(relied) = &edge.relied_spec_id {
            basis.push(relied.clone());
        }
        basis.extend(edge.basis_spec_ids.iter().cloned());
    }
    basis.retain(|id| id != &target.id);
    let projection = Edge::paired_assumption_projection(
        &target.id,
        node.id(),
        basis,
        projection_derivation(),
        recorded_at,
    )
    .map_err(|message| PairingError::Store(StoreError::InvalidEdge(message)))?;
    store.put_derived_node(&node, &projection)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, Node, VertexKind};
    use crate::graph_generation::{current_derivations, generate_and_persist};
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
                created_at: "t".into(),
                cli: "test".into(),
                cli_version: "test".into(),
                updates: Default::default(),
            },
        }
    }

    #[test]
    fn proved_pairing_replaces_top_with_a_visible_authored_assumption() {
        let store = InMemoryNodeStore::new();
        let source = node("source", "The sensor shall report the alarm.");
        let target = node("target", "The controller shall stop the pump.");
        store.add_node(&source).unwrap();
        store.add_node(&target).unwrap();
        generate_and_persist(&target, &store, "t0").unwrap();

        let edge = append_relation(
            &store,
            EdgeKind::GuaranteeDischarge,
            &source.id,
            &target.id,
            &source.id,
            vec![],
            "t1",
        )
        .unwrap();
        assert_eq!(edge.relied_spec_id.as_deref(), Some(source.id.as_str()));

        let edges = store
            .list_edges(
                &[source.id.clone(), target.id.clone()],
                &current_derivations(),
            )
            .unwrap();
        let assumptions: Vec<&Edge> = edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::HasAssumption && edge.source == target.id)
            .collect();
        assert_eq!(assumptions.len(), 1, "paired A supersedes ingest Top");
        assert_eq!(
            assumptions[0].derivation,
            projection_derivation(),
            "the current projection is graph-paired"
        );
        assert_eq!(assumptions[0].target_kind, VertexKind::Assumption);
        let derived = store
            .get_derived_nodes(&[assumptions[0].target.clone()])
            .unwrap();
        assert!(matches!(
            derived.as_slice(),
            [DerivedNode::Assumption { expression, formula_json, .. }]
                if expression == &source.statement && !formula_json.is_empty()
        ));
    }

    #[test]
    fn unknown_entailment_and_shared_subject_never_become_topology() {
        let store = InMemoryNodeStore::new();
        for node in [
            node("source", "The sensor shall report the alarm."),
            node("unrelated", "The clock shall show the time."),
            node("same", "The sensor shall stop the pump."),
        ] {
            store.add_node(&node).unwrap();
        }
        assert!(matches!(
            append_relation(
                &store,
                EdgeKind::GuaranteeDischarge,
                "source",
                "same",
                "unrelated",
                vec![],
                "t"
            ),
            Err(PairingError::InvalidSource(_)) | Err(PairingError::RelianceNotProven)
        ));
        assert!(store
            .list_pairing_edges("same", &derivation())
            .unwrap()
            .is_empty());

        assert!(matches!(
            append_relation(
                &store,
                EdgeKind::GuaranteeDischarge,
                "source",
                "same",
                "source",
                vec![],
                "t"
            ),
            Err(PairingError::SharedSubjectKeys)
        ));
        assert!(store
            .list_pairing_edges("same", &derivation())
            .unwrap()
            .is_empty());
    }

    #[test]
    fn aggregate_contradiction_is_rejected_without_erasing_the_first_fact() {
        let store = InMemoryNodeStore::new();
        for node in [
            node("positive", "The sensor shall report the alarm."),
            node("negative", "The sensor shall not report the alarm."),
            node("target", "The controller shall stop the pump."),
        ] {
            store.add_node(&node).unwrap();
        }
        append_relation(
            &store,
            EdgeKind::GuaranteeDischarge,
            "positive",
            "target",
            "positive",
            vec![],
            "t1",
        )
        .unwrap();
        assert!(matches!(
            append_relation(
                &store,
                EdgeKind::GuaranteeDischarge,
                "negative",
                "target",
                "negative",
                vec![],
                "t2"
            ),
            Err(PairingError::UnsatisfiableAssumption)
        ));
        let pairings = store.list_pairing_edges("target", &derivation()).unwrap();
        assert_eq!(pairings.len(), 1);
        assert_eq!(pairings[0].source, "positive");
    }
}
