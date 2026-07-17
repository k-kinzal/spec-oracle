//! Explicit persistence boundary for standard A/G contract operations.
//!
//! `so-reason` owns the pure algebra. This module resolves Contract vertices,
//! recovers authored provenance, checks the operation's defining law, and
//! appends the result and operand edges to the Ledger.

use std::collections::BTreeSet;

use thiserror::Error;

use crate::domain::{Derivation, DerivedNode, Edge, EdgeKind};
use crate::store::{GraphStore, StoreError};

pub const DERIVATION_METHOD: &str = "so-daemon.contract.algebra";
pub const DERIVATION_VERSION: &str = "contract-algebra/v1;reason=so-reason/contract-algebra-v1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operation {
    Composition,
    Quotient,
    Merge,
}

impl Operation {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Composition => "composition",
            Self::Quotient => "quotient",
            Self::Merge => "merge",
        }
    }
}

#[derive(Debug, Error)]
pub enum AlgebraError {
    #[error("contract node '{0}' does not exist")]
    MissingContract(String),
    #[error("derived node '{0}' is not a semantic Contract node")]
    NotContract(String),
    #[error("basis specification node '{0}' does not exist")]
    MissingBasis(String),
    #[error("the derived contract failed its defining law: {0}")]
    LawViolation(String),
    #[error(transparent)]
    Store(#[from] StoreError),
}

impl AlgebraError {
    pub fn is_bad_input(&self) -> bool {
        matches!(
            self,
            Self::MissingContract(_) | Self::NotContract(_) | Self::MissingBasis(_)
        )
    }
}

pub struct DerivationResult {
    pub contract: DerivedNode,
    pub edges: Vec<Edge>,
}

pub fn derivation() -> Derivation {
    Derivation {
        method: DERIVATION_METHOD.to_string(),
        version: DERIVATION_VERSION.to_string(),
    }
}

pub fn derive(
    store: &(dyn GraphStore + Send + Sync),
    left_id: &str,
    right_id: &str,
    operation: Operation,
    additional_basis: Vec<String>,
    recorded_at: &str,
) -> Result<DerivationResult, AlgebraError> {
    let left_node = required_contract_node(store, left_id)?;
    let right_node = required_contract_node(store, right_id)?;
    let left = left_node
        .semantic_contract()
        .ok_or_else(|| AlgebraError::NotContract(left_id.to_string()))?;
    let right = right_node
        .semantic_contract()
        .ok_or_else(|| AlgebraError::NotContract(right_id.to_string()))?;

    for id in &additional_basis {
        if store.get_node(id)?.is_none() {
            return Err(AlgebraError::MissingBasis(id.clone()));
        }
    }
    let mut basis = recover_basis(store, &[left_id, right_id])?;
    basis.extend(additional_basis);
    basis.sort();
    basis.dedup();

    let result = match operation {
        Operation::Composition => left.compose(&right),
        Operation::Quotient => left.quotient(&right),
        Operation::Merge => left.merge(&right),
    };
    verify_defining_law(&left, &right, &result, operation)?;
    verify_interface_closure(&left, &right, &result)?;

    let result_node = DerivedNode::contract(&result, operation.as_str(), DERIVATION_VERSION);
    let kinds = match operation {
        Operation::Composition => [EdgeKind::CompositionOperand, EdgeKind::CompositionOperand],
        Operation::Quotient => [EdgeKind::QuotientDividend, EdgeKind::QuotientDivisor],
        Operation::Merge => [EdgeKind::MergeOperand, EdgeKind::MergeOperand],
    };
    let first = Edge::contract_relation(
        kinds[0],
        left_id,
        result_node.id(),
        basis.clone(),
        derivation(),
        recorded_at,
    )
    .map_err(|message| AlgebraError::Store(StoreError::InvalidEdge(message)))?;
    let second = Edge::contract_relation(
        kinds[1],
        right_id,
        result_node.id(),
        basis,
        derivation(),
        recorded_at,
    )
    .map_err(|message| AlgebraError::Store(StoreError::InvalidEdge(message)))?;
    store.put_derived_node(&result_node, &first)?;
    store.append_edge(&second)?;
    Ok(DerivationResult {
        contract: result_node,
        edges: vec![first, second],
    })
}

fn required_contract_node(
    store: &(dyn GraphStore + Send + Sync),
    id: &str,
) -> Result<DerivedNode, AlgebraError> {
    store
        .get_derived_nodes(&[id.to_string()])?
        .into_iter()
        .next()
        .ok_or_else(|| AlgebraError::MissingContract(id.to_string()))
}

fn recover_basis(
    store: &(dyn GraphStore + Send + Sync),
    contract_ids: &[&str],
) -> Result<Vec<String>, StoreError> {
    let contracts: BTreeSet<&str> = contract_ids.iter().copied().collect();
    let mut basis = BTreeSet::new();
    let mut cursor = None;
    loop {
        let page = store.list_ledger_edges(cursor.as_deref(), 500)?;
        for edge in page.edges {
            if contracts.contains(edge.target.as_str()) || contracts.contains(edge.source.as_str())
            {
                if edge.kind == EdgeKind::HasContract {
                    basis.insert(edge.source.clone());
                }
                basis.extend(edge.basis_spec_ids);
            }
        }
        match page.next_cursor {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    Ok(basis.into_iter().collect())
}

fn verify_defining_law(
    left: &so_reason::contract::Contract,
    right: &so_reason::contract::Contract,
    result: &so_reason::contract::Contract,
    operation: Operation,
) -> Result<(), AlgebraError> {
    let valid = match operation {
        Operation::Composition => result.equivalent(&left.compose(right)),
        Operation::Quotient => result.compose(right).refines(left),
        Operation::Merge => result.equivalent(&left.merge(right)),
    };
    if valid {
        Ok(())
    } else {
        Err(AlgebraError::LawViolation(match operation {
            Operation::Composition => "composition result is not algebraically equivalent".into(),
            Operation::Quotient => "quotient composed with divisor does not refine target".into(),
            Operation::Merge => "merge result is not algebraically equivalent".into(),
        }))
    }
}

fn verify_interface_closure(
    left: &so_reason::contract::Contract,
    right: &so_reason::contract::Contract,
    result: &so_reason::contract::Contract,
) -> Result<(), AlgebraError> {
    let union = left.interface().union(&right.interface());
    if result
        .interface()
        .atoms
        .iter()
        .all(|atom| union.atoms.contains(atom))
    {
        Ok(())
    } else {
        Err(AlgebraError::LawViolation(
            "operation introduced an atom outside the operand interfaces".into(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, Node};
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
    fn composition_and_quotient_materialize_proved_contract_nodes() {
        let store = InMemoryNodeStore::new();
        let sensor = node("sensor", "The sensor shall report the alarm.");
        let controller = node("controller", "The controller shall stop the pump.");
        for value in [&sensor, &controller] {
            store.add_node(value).unwrap();
            generate_and_persist(value, &store, "t0").unwrap();
        }
        let edges = store
            .list_edges(
                &[sensor.id.clone(), controller.id.clone()],
                &current_derivations(),
            )
            .unwrap();
        let contract_id = |owner: &str| {
            edges
                .iter()
                .find(|edge| edge.kind == EdgeKind::HasContract && edge.source == owner)
                .map(|edge| edge.target.clone())
                .unwrap()
        };
        let sensor_contract = contract_id(&sensor.id);
        let controller_contract = contract_id(&controller.id);

        let composition = derive(
            &store,
            &sensor_contract,
            &controller_contract,
            Operation::Composition,
            vec![],
            "t1",
        )
        .unwrap();
        assert!(matches!(
            composition.contract,
            DerivedNode::Contract { ref operation, .. } if operation == "composition"
        ));
        assert_eq!(composition.edges.len(), 2);
        assert!(composition
            .edges
            .iter()
            .all(|edge| edge.kind == EdgeKind::CompositionOperand));

        let quotient = derive(
            &store,
            composition.contract.id(),
            &sensor_contract,
            Operation::Quotient,
            vec![],
            "t2",
        )
        .unwrap();
        let quotient_contract = quotient.contract.semantic_contract().unwrap();
        let divisor = store
            .get_derived_nodes(&[sensor_contract])
            .unwrap()
            .remove(0)
            .semantic_contract()
            .unwrap();
        let target = composition.contract.semantic_contract().unwrap();
        assert!(quotient_contract.compose(&divisor).refines(&target));
        assert_eq!(quotient.edges[0].kind, EdgeKind::QuotientDividend);
        assert_eq!(quotient.edges[1].kind, EdgeKind::QuotientDivisor);
    }
}
