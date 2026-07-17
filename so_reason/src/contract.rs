//! Assume-guarantee contracts over a classical Boolean assertion domain.
//!
//! This module keeps three concepts separate:
//!
//! * [`Contract`] is the semantic A/G pair `(A, G)`. Its meaning is the
//!   standard assume-guarantee condition: an implementation assertion `M`
//!   satisfies the contract when `M ∧ A ⇒ G`, equivalently when
//!   `M ⇒ G ∨ ¬A`.
//! * [`FormedContract`] records how that semantic pair was formed from
//!   authored specification assertions. Formation provenance is deliberately
//!   not part of [`Contract`]'s semantic identity.
//! * [`contract_formula`] is the constrained-NL projection. It produces a
//!   provisional `(⊤, G)` formed contract; graph-side explicit pairing may
//!   later form a non-trivial assumption without changing the guarantee.
//!
//! [`Formula`] is not itself the contract algebra: its `Not` around a behavior
//! atom denotes predicate denial inside the subject quantifier, and therefore
//! is not generally the classical complement required by contract saturation.
//! [`Assertion`] is the dedicated classical Boolean algebra. Projection maps a
//! positive or denied behavior to a signed opaque atom and reserves
//! [`Assertion::Not`] for genuine Boolean complement. This preserves the
//! constrained-NL meaning while making saturation, composition, refinement,
//! merging, and quotient use the standard contract operations.

use serde::{Deserialize, Serialize};
use so_lang::ast::Sentence;

use crate::formula::{assertion_formula, AtomRef, Formula, Proposition};
use crate::semantics::{speech_act, ClauseSkeleton, Force, SpeechAct};

pub use crate::formula::{
    AssumptionSource, EdgeKind, PairingError, SourceIssue, SourceIssueReason, SubjectRelation,
    WellFormedness,
};

/// Polarity of an authored behavior predicate.
///
/// This is intentionally data on an atom, not [`Assertion::Not`]. For
/// example, `Every pump shall not run` denotes `∀x.¬run(x)`, not the
/// classical complement `¬∀x.run(x)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PredicatePolarity {
    Positive,
    Negative,
}

/// One opaque generator in the contract Boolean algebra.
///
/// Surface anchors are provenance and are excluded. Force and speech act are
/// retained on behavior atoms because a recommendation and an obligation do
/// not make the same contract promise even when their propositional content
/// is identical.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ContractAtom {
    Guard {
        clause: ClauseSkeleton,
        role: crate::formula::GuardRole,
    },
    Behavior {
        proposition: Proposition,
        force: Option<Force>,
        act: SpeechAct,
        polarity: PredicatePolarity,
    },
    Admissibility {
        proposition: Proposition,
        polarity: PredicatePolarity,
    },
}

/// A classical Boolean assertion used by the A/G algebra.
///
/// Constructors normalize associativity, commutativity, idempotence,
/// constants, and double negation. Consequently algebra results have stable
/// semantic identities independent of operand order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Assertion {
    Atom { atom: ContractAtom },
    And { items: Vec<Assertion> },
    Or { items: Vec<Assertion> },
    Not { inner: Box<Assertion> },
    Top,
    Bottom,
}

impl Assertion {
    pub fn and(items: impl IntoIterator<Item = Assertion>) -> Assertion {
        let mut flat = Vec::new();
        for item in items {
            match item {
                Assertion::Top => {}
                Assertion::Bottom => return Assertion::Bottom,
                Assertion::And { items } => flat.extend(items),
                other => flat.push(other),
            }
        }
        canonical_items(&mut flat);
        match flat.len() {
            0 => Assertion::Top,
            1 => flat.remove(0),
            _ => Assertion::And { items: flat },
        }
    }

    pub fn or(items: impl IntoIterator<Item = Assertion>) -> Assertion {
        let mut flat = Vec::new();
        for item in items {
            match item {
                Assertion::Bottom => {}
                Assertion::Top => return Assertion::Top,
                Assertion::Or { items } => flat.extend(items),
                other => flat.push(other),
            }
        }
        canonical_items(&mut flat);
        match flat.len() {
            0 => Assertion::Bottom,
            1 => flat.remove(0),
            _ => Assertion::Or { items: flat },
        }
    }

    pub fn complement(self) -> Assertion {
        match self {
            Assertion::Top => Assertion::Bottom,
            Assertion::Bottom => Assertion::Top,
            Assertion::Not { inner } => *inner,
            other => Assertion::Not {
                inner: Box::new(other),
            },
        }
    }

    /// Exact propositional entailment in the finite Boolean assertion
    /// domain. This is a decision, not the conservative NL relation
    /// heuristic: it searches for a model of `self ∧ ¬consequence`.
    pub fn entails(&self, consequence: &Assertion) -> bool {
        !Assertion::and([self.clone(), consequence.clone().complement()]).satisfiable()
    }

    pub fn equivalent(&self, other: &Assertion) -> bool {
        self.entails(other) && other.entails(self)
    }

    pub fn contradicts(&self, other: &Assertion) -> bool {
        !Assertion::and([self.clone(), other.clone()]).satisfiable()
    }

    pub fn satisfiable(&self) -> bool {
        let mut atoms = Vec::new();
        collect_atoms(self, &mut atoms);
        dpll(self, &atoms, &mut vec![None; atoms.len()])
    }
}

fn canonical_items(items: &mut Vec<Assertion>) {
    items.sort_by_cached_key(|item| {
        serde_json::to_string(item).expect("contract assertion serialization is infallible")
    });
    items.dedup();
}

fn collect_atoms(assertion: &Assertion, atoms: &mut Vec<ContractAtom>) {
    match assertion {
        Assertion::Atom { atom } => {
            if !atoms.contains(atom) {
                atoms.push(atom.clone());
            }
        }
        Assertion::And { items } | Assertion::Or { items } => {
            for item in items {
                collect_atoms(item, atoms);
            }
        }
        Assertion::Not { inner } => collect_atoms(inner, atoms),
        Assertion::Top | Assertion::Bottom => {}
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PartialTruth {
    True,
    False,
    Unknown,
}

fn partial_eval(
    assertion: &Assertion,
    atoms: &[ContractAtom],
    values: &[Option<bool>],
) -> PartialTruth {
    match assertion {
        Assertion::Atom { atom } => match values[atoms
            .iter()
            .position(|candidate| candidate == atom)
            .expect("collected atom must be present")]
        {
            Some(true) => PartialTruth::True,
            Some(false) => PartialTruth::False,
            None => PartialTruth::Unknown,
        },
        Assertion::And { items } => {
            let mut unknown = false;
            for item in items {
                match partial_eval(item, atoms, values) {
                    PartialTruth::False => return PartialTruth::False,
                    PartialTruth::Unknown => unknown = true,
                    PartialTruth::True => {}
                }
            }
            if unknown {
                PartialTruth::Unknown
            } else {
                PartialTruth::True
            }
        }
        Assertion::Or { items } => {
            let mut unknown = false;
            for item in items {
                match partial_eval(item, atoms, values) {
                    PartialTruth::True => return PartialTruth::True,
                    PartialTruth::Unknown => unknown = true,
                    PartialTruth::False => {}
                }
            }
            if unknown {
                PartialTruth::Unknown
            } else {
                PartialTruth::False
            }
        }
        Assertion::Not { inner } => match partial_eval(inner, atoms, values) {
            PartialTruth::True => PartialTruth::False,
            PartialTruth::False => PartialTruth::True,
            PartialTruth::Unknown => PartialTruth::Unknown,
        },
        Assertion::Top => PartialTruth::True,
        Assertion::Bottom => PartialTruth::False,
    }
}

fn dpll(assertion: &Assertion, atoms: &[ContractAtom], values: &mut [Option<bool>]) -> bool {
    match partial_eval(assertion, atoms, values) {
        PartialTruth::True => return true,
        PartialTruth::False => return false,
        PartialTruth::Unknown => {}
    }
    let index = values
        .iter()
        .position(Option::is_none)
        .expect("unknown formula has an unassigned atom");
    values[index] = Some(false);
    if dpll(assertion, atoms, values) {
        values[index] = None;
        return true;
    }
    values[index] = Some(true);
    let result = dpll(assertion, atoms, values);
    values[index] = None;
    result
}

impl From<&Formula> for Assertion {
    fn from(formula: &Formula) -> Self {
        match formula {
            Formula::Atom { atom } => assertion_atom(atom, PredicatePolarity::Positive),
            Formula::And { items } => Assertion::and(items.iter().map(Assertion::from)),
            Formula::Or { items } => Assertion::or(items.iter().map(Assertion::from)),
            Formula::Not { inner } => match &**inner {
                Formula::Atom {
                    atom: AtomRef::Behavior { .. } | AtomRef::Admissibility { .. },
                } => assertion_atom(
                    match &**inner {
                        Formula::Atom { atom } => atom,
                        _ => unreachable!(),
                    },
                    PredicatePolarity::Negative,
                ),
                _ => Assertion::from(&**inner).complement(),
            },
            Formula::Top => Assertion::Top,
            Formula::Bottom => Assertion::Bottom,
        }
    }
}

impl From<Formula> for Assertion {
    fn from(formula: Formula) -> Self {
        Assertion::from(&formula)
    }
}

fn assertion_atom(atom: &AtomRef, polarity: PredicatePolarity) -> Assertion {
    let atom = match atom {
        AtomRef::Guard { clause, role, .. } => ContractAtom::Guard {
            clause: clause.clone(),
            role: *role,
        },
        AtomRef::Behavior { behavior } => ContractAtom::Behavior {
            proposition: behavior.proposition(),
            force: behavior.force,
            act: behavior.act,
            polarity,
        },
        AtomRef::Admissibility { behavior } => ContractAtom::Admissibility {
            proposition: behavior.proposition(),
            polarity,
        },
    };
    Assertion::Atom { atom }
}

/// The behavior alphabet over which a contract is interpreted.
///
/// This is an interface in the algebraic sense: the set of Boolean
/// generators mentioned by `A` or `G`. It deliberately does not invent port
/// directions or component ownership that constrained NL has not stated.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContractInterface {
    pub atoms: Vec<ContractAtom>,
}

impl ContractInterface {
    pub fn of(contract: &Contract) -> Self {
        let mut atoms = Vec::new();
        collect_atoms(&contract.assumption, &mut atoms);
        collect_atoms(&contract.guarantee, &mut atoms);
        atoms.sort_by_cached_key(|atom| {
            serde_json::to_string(atom).expect("contract atom serialization is infallible")
        });
        Self { atoms }
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut atoms = self.atoms.clone();
        atoms.extend(other.atoms.clone());
        atoms.sort_by_cached_key(|atom| {
            serde_json::to_string(atom).expect("contract atom serialization is infallible")
        });
        atoms.dedup();
        Self { atoms }
    }
}

/// A semantic assume-guarantee contract `(A, G)` over one assertion domain.
///
/// `A` denotes the environments for which the component promises `G`.
/// The contract accepts an implementation assertion `M` exactly when
/// `M ∧ A ⇒ G`, equivalently `M ⇒ G ∨ ¬A`.
///
/// Both formulas must be interpreted over the same behavior universe. The
/// current formula projection has no first-class port/interface profile, so
/// interface compatibility is intentionally not claimed or guessed here.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Contract {
    pub assumption: Assertion,
    pub guarantee: Assertion,
}

impl Contract {
    pub fn new(assumption: Assertion, guarantee: Assertion) -> Self {
        Self {
            assumption,
            guarantee,
        }
    }

    pub fn from_formulas(assumption: &Formula, guarantee: &Formula) -> Self {
        Self::new(assumption.into(), guarantee.into())
    }

    /// A contract with no environment restriction.
    pub fn unconditional(guarantee: Assertion) -> Self {
        Self::new(Assertion::Top, guarantee)
    }

    /// The saturated guarantee `G ∨ ¬A`.
    ///
    /// This is the assertion against which implementation inclusion and the
    /// guarantee half of refinement are checked. The assumption remains a
    /// separate part of the contract; saturation never replaces it with `⊤`.
    pub fn saturated_guarantee(&self) -> Assertion {
        if self.assumption == Assertion::Top {
            return self.guarantee.clone();
        }
        Assertion::or([self.guarantee.clone(), self.assumption.clone().complement()])
    }

    /// A saturated representation `(A, G ∨ ¬A)`.
    pub fn saturate(&self) -> Contract {
        Contract {
            assumption: self.assumption.clone(),
            guarantee: self.saturated_guarantee(),
        }
    }

    /// Does an implementation assertion satisfy this contract?
    ///
    /// `Yes` and `No` have the conservative proof meaning of
    /// [`crate::relate::implies`]; `Unknown` means the current structural
    /// calculus cannot decide the standard inclusion check.
    pub fn satisfied_by(&self, implementation: &Assertion) -> bool {
        implementation.entails(&self.saturated_guarantee())
    }

    /// Does this contract refine `abstract_`?
    ///
    /// Standard A/G refinement accepts more environments and promises at
    /// least as much behavior: `A_abstract ⇒ A_self` and
    /// `sat(G_self) ⇒ sat(G_abstract)`.
    pub fn refines(&self, abstract_: &Contract) -> bool {
        abstract_.assumption.entails(&self.assumption)
            && self
                .saturated_guarantee()
                .entails(&abstract_.saturated_guarantee())
    }

    pub fn equivalent(&self, other: &Contract) -> bool {
        self.refines(other) && other.refines(self)
    }

    pub fn interface(&self) -> ContractInterface {
        ContractInterface::of(self)
    }

    /// Parallel composition in the saturated contract algebra:
    /// `((A₁∧A₂)∨¬(G₁∧G₂), G₁∧G₂)`.
    pub fn compose(&self, other: &Contract) -> Contract {
        let left = self.saturate();
        let right = other.saturate();
        let guarantee = Assertion::and([left.guarantee, right.guarantee]);
        let assumption = Assertion::or([
            Assertion::and([left.assumption, right.assumption]),
            guarantee.clone().complement(),
        ]);
        Contract::new(assumption, guarantee)
    }

    /// Quotient (residual) `self / divisor`, characterized by
    /// `X ≤ self/divisor` iff `X ∥ divisor ≤ self`.
    pub fn quotient(&self, divisor: &Contract) -> Contract {
        let target = self.saturate();
        let known = divisor.saturate();
        let assumption = Assertion::and([target.assumption, known.guarantee]);
        let guarantee = Assertion::or([
            Assertion::and([known.assumption, target.guarantee]),
            assumption.clone().complement(),
        ]);
        Contract::new(assumption, guarantee)
    }

    /// Viewpoint merge: both viewpoints apply where both assumptions hold,
    /// and both guarantees are required there.
    pub fn merge(&self, other: &Contract) -> Contract {
        let left = self.saturate();
        let right = other.saturate();
        let assumption = Assertion::and([left.assumption, right.assumption]);
        let guarantee = Assertion::or([
            Assertion::and([left.guarantee, right.guarantee]),
            assumption.clone().complement(),
        ]);
        Contract::new(assumption, guarantee)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ContractRelation {
    Refines,
    RefinedBy,
    Equivalent,
    Incomparable,
}

pub fn assess_contracts(left: &Contract, right: &Contract) -> ContractRelation {
    match (left.refines(right), right.refines(left)) {
        (true, true) => ContractRelation::Equivalent,
        (true, false) => ContractRelation::Refines,
        (false, true) => ContractRelation::RefinedBy,
        (false, false) => ContractRelation::Incomparable,
    }
}

/// A semantic contract together with its assumption-formation provenance.
///
/// Sources explain and validate how `A` was selected; they are not part of the
/// semantic A/G pair. The flat fields preserve the historic serialized shape
/// `{ assumption, guarantee, sources }`; [`Self::semantic`] projects the
/// provenance-free [`Contract`] used for A/G semantics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FormedContract {
    pub assumption: Formula,
    pub guarantee: Formula,
    #[serde(default)]
    pub sources: Vec<AssumptionSource>,
}

/// Compatibility name for callers of the former formula-owned API.
pub type ContractFormula = FormedContract;

impl FormedContract {
    pub fn from_formulas(assumption: Formula, guarantee: Formula) -> Self {
        Self {
            assumption,
            guarantee,
            sources: Vec::new(),
        }
    }

    pub fn semantic(&self) -> Contract {
        Contract::from_formulas(&self.assumption, &self.guarantee)
    }

    pub fn into_semantic(self) -> Contract {
        Contract::from_formulas(&self.assumption, &self.guarantee)
    }
}

/// Project one constrained-NL sentence to a provisional formed contract.
///
/// Definitions and permissions have no lone contract. Descriptions,
/// obligations, prohibitions, and recommendations produce `(⊤, G)`, where
/// `G` is the sentence's complete guarded assertion.
pub fn contract_formula(sentence: &Sentence) -> Option<FormedContract> {
    if matches!(
        speech_act(sentence),
        SpeechAct::Definition | SpeechAct::Permission
    ) {
        return None;
    }
    let guarantee = assertion_formula(sentence)?;
    Some(FormedContract::from_formulas(Formula::Top, guarantee))
}

/// Preferred name for the constrained-NL formation projection.
pub fn formed_contract(sentence: &Sentence) -> Option<FormedContract> {
    contract_formula(sentence)
}

#[cfg(test)]
mod tests {
    use super::*;
    use so_lang::parse::parse;

    fn one(input: &str) -> Sentence {
        parse(input).unwrap().sentences.remove(0)
    }

    #[test]
    fn semantic_contract_is_distinct_from_formation_provenance() {
        let formed = contract_formula(&one("The pump shall stop.")).unwrap();
        assert_eq!(formed.semantic().assumption, Assertion::Top);
        assert!(formed.sources.is_empty());
        assert_eq!(
            formed.semantic().saturated_guarantee(),
            formed.semantic().guarantee
        );
    }

    #[test]
    fn saturation_preserves_the_assumption_as_a_contract_side() {
        let assumption = assertion_formula(&one("The sensor shall report the alarm.")).unwrap();
        let guarantee = assertion_formula(&one("The controller shall stop the pump.")).unwrap();
        let contract = Contract::from_formulas(&assumption, &guarantee);
        let saturated = contract.saturate();

        assert_eq!(saturated.assumption, Assertion::from(&assumption));
        assert_eq!(
            saturated.guarantee,
            Assertion::or([
                Assertion::from(&guarantee),
                contract.assumption.complement(),
            ])
        );
    }

    #[test]
    fn satisfaction_uses_the_standard_saturated_inclusion() {
        let formed = contract_formula(&one("The pump shall stop.")).unwrap();
        assert!(formed
            .semantic()
            .satisfied_by(&Assertion::from(&formed.guarantee)));
    }

    #[test]
    fn saturation_is_idempotent() {
        let assumption = assertion_formula(&one("The sensor shall report the alarm.")).unwrap();
        let guarantee = assertion_formula(&one("The controller shall stop the pump.")).unwrap();
        let contract = Contract::from_formulas(&assumption, &guarantee);
        let once = contract.saturate();
        let twice = once.saturate();

        assert!(once.guarantee.equivalent(&twice.guarantee));
    }

    #[test]
    fn refinement_weakens_assumptions_and_strengthens_saturated_guarantees() {
        let environment = assertion_formula(&one("The sensor shall report the alarm.")).unwrap();
        let guarantee = assertion_formula(&one("The controller shall stop the pump.")).unwrap();
        let abstract_ = Contract::from_formulas(&environment, &guarantee);
        let concrete = Contract::unconditional(guarantee.into());

        assert!(concrete.refines(&abstract_));
        assert!(!abstract_.refines(&concrete));
    }

    #[test]
    fn behavior_denial_is_not_mistaken_for_classical_complement() {
        let positive = assertion_formula(&one("Every pump shall run.")).expect("behavior formula");
        let denied =
            assertion_formula(&one("Every pump shall not run.")).expect("behavior formula");
        let positive = Assertion::from(&positive);
        let denied = Assertion::from(&denied);

        assert_ne!(denied, positive.clone().complement());
        assert!(Assertion::and([positive, denied]).satisfiable());
    }

    #[test]
    fn composition_is_commutative_and_associative_up_to_contract_equivalence() {
        let a = contract_formula(&one("The sensor shall report the alarm."))
            .unwrap()
            .semantic();
        let b = contract_formula(&one("The controller shall stop the pump."))
            .unwrap()
            .semantic();
        let c = contract_formula(&one("The logger shall record the event."))
            .unwrap()
            .semantic();

        assert!(a.compose(&b).equivalent(&b.compose(&a)));
        assert!(a
            .compose(&b)
            .compose(&c)
            .equivalent(&a.compose(&b.compose(&c))));
    }

    #[test]
    fn quotient_satisfies_the_residuation_law() {
        let p = Assertion::from(
            &assertion_formula(&one("The sensor shall report the alarm.")).unwrap(),
        );
        let q = Assertion::from(
            &assertion_formula(&one("The controller shall stop the pump.")).unwrap(),
        );
        let contracts = vec![
            Contract::new(Assertion::Top, p.clone()),
            Contract::new(p.clone(), q.clone()),
            Contract::new(q.clone(), Assertion::and([p.clone(), q.clone()])),
            Contract::new(Assertion::or([p.clone(), q.clone()]), p),
        ];

        for target in &contracts {
            for divisor in &contracts {
                let quotient = target.quotient(divisor);
                for candidate in &contracts {
                    assert_eq!(
                        candidate.refines(&quotient),
                        candidate.compose(divisor).refines(target),
                        "X ≤ C/C1 iff X ∥ C1 ≤ C"
                    );
                }
            }
        }
    }

    #[test]
    fn quotient_composed_with_divisor_refines_the_target() {
        let target = contract_formula(&one("The controller shall stop the pump."))
            .unwrap()
            .semantic();
        let divisor = contract_formula(&one("The sensor shall report the alarm."))
            .unwrap()
            .semantic();

        assert!(target.quotient(&divisor).compose(&divisor).refines(&target));
    }

    #[test]
    fn formula_equivalence_does_not_erase_sentence_force() {
        let recommended = one("The pump should stop.");
        let binding = one("The pump shall stop.");
        let recommended_formula = assertion_formula(&recommended).unwrap();
        let binding_formula = assertion_formula(&binding).unwrap();

        assert_eq!(
            crate::relate::assess_formulas(&recommended_formula, &binding_formula),
            crate::relate::FormulaRelation::Equivalent
        );
        assert_ne!(
            crate::relate::assess(&recommended, &binding),
            crate::relate::Outcome::Equivalent
        );
        assert_eq!(
            assess_contracts(
                &formed_contract(&recommended).unwrap().semantic(),
                &formed_contract(&binding).unwrap().semantic(),
            ),
            ContractRelation::Incomparable
        );
    }

    #[test]
    fn formed_contract_keeps_the_legacy_flat_json_shape() {
        let formed = contract_formula(&one("The pump shall stop.")).unwrap();
        let json = serde_json::to_value(&formed).unwrap();
        assert!(json.get("contract").is_none());
        assert!(json.get("assumption").is_some());
        assert!(json.get("guarantee").is_some());
        assert!(json.get("sources").is_some());
        assert_eq!(
            serde_json::from_value::<FormedContract>(json).unwrap(),
            formed
        );
    }
}
