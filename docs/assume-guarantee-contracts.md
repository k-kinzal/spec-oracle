# Assume-guarantee contracts

spec-oracle uses the saturated assume-guarantee contract algebra, not a
project-local relation merely named “A/G”. A contract is `(A,G)` over one
Boolean algebra of behaviors. Its implementation semantics is

```text
M satisfies (A,G)  iff  M ∧ A ⇒ G
                     iff  M ⇒ G ∨ ¬A
```

The implementation follows the canonical/saturated presentation and operations
in Benveniste et al., *Contracts for System Design* (2018), and the explicit
algebraic definitions and quotient theorem in Iñigo Incer,
[*The Algebra of Contracts*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2022/EECS-2022-99.pdf)
(EECS-2022-99, 2022).

## Assertion boundary

`so-lang` remains the source language and `so-reason::formula::Formula` remains
its lossless semantic projection. The A/G algebra uses
`so-reason::contract::Assertion`, a separate classical Boolean algebra.

This separation is required: a behavior-level `Formula::Not` denotes predicate
denial under the subject quantifier, so it cannot universally serve as the
set complement in `G ∨ ¬A`. Projection records a positive or denied predicate
as a signed opaque `ContractAtom`; algebraic `Assertion::Not` is then available
only for genuine classical complement. The abstraction is intentionally
conservative: it adds no unstated relation between distinct atoms.

The interface is the finite behavior alphabet used by `A` and `G`. It is a
legitimate contract interface over a free Boolean algebra, but it is not
presented as an input/output port interface. Port direction and component
ownership require additional authored semantics.

## Standard operations

All operands are saturated before applying the operations.

```text
saturate(A,G) = (A, G ∨ ¬A)

(A₁,G₁) ≤ (A₂,G₂)
  iff A₂ ⇒ A₁ and (G₁ ∨ ¬A₁) ⇒ (G₂ ∨ ¬A₂)

(A₁,G₁) ∥ (A₂,G₂)
  = ((A₁ ∧ A₂) ∨ ¬(G₁ ∧ G₂), G₁ ∧ G₂)

(A,G) / (A₁,G₁)
  = (A ∧ G₁, (A₁ ∧ G) ∨ ¬(A ∧ G₁))

merge((A₁,G₁),(A₂,G₂))
  = (A₁ ∧ A₂, (G₁ ∧ G₂) ∨ ¬(A₁ ∧ A₂))
```

The quotient is characterized by the residual law:

```text
X ≤ C/C₁  iff  X ∥ C₁ ≤ C
```

`Assertion::entails` is an exact finite propositional decision procedure, not
the constrained-NL relation heuristic. Tests enumerate contract combinations
for the quotient residual law and also check saturation idempotence and
composition commutativity/associativity.

## Graph meaning

The current graph separates four levels:

```text
Specification ──HasAssumption──▶ Assumption
              ├─HasGuarantee───▶ Guarantee
              └─HasContract────▶ Contract(A,G)

Contract ──ContractRefines─────▶ Contract
Contract ──ContractEquivalent── Contract

Contract ──CompositionOperand──▶ Derived Contract
Contract ──QuotientDividend────▶ Derived Contract
Contract ──QuotientDivisor─────▶ Derived Contract
Contract ──MergeOperand────────▶ Derived Contract
```

Contract Nodes are content-addressed. When explicit pairing changes `A`, the
new `HasContract` projection selects a new Contract Node. Old relationships
remain correct Ledger facts about the old Contract rather than becoming stale
Specification-to-Specification claims.

Formula relation, sentence relation, and contract relation Assessments are
separate:

- formula relations are force/speech-act blind logical facts;
- sentence relations decide graph meaning for authored specifications;
- contract relations apply standard refinement to current `(A,G)` values.

An entailed discharge is intentionally two-stage. Discovery records
`DischargeCandidate(source,target,relied)` when a binding source guarantee
entails an explicit target assumption. It is not topology. Explicit acceptance
re-runs the complete pairing validator and only then appends the existing
`GuaranteeDischarge` Edge.

## Hypotheses and expected-outcome checks

| Hypothesis | Expected graph/reasoning outcome | Verification |
|---|---|---|
| Formula truth is not sentence force | `should P` and `shall P` may be FormulaEquivalent without becoming sentence Equivalent or the same Contract | unit test separates all three judgments |
| A change must not stale a contract relation | pairing creates a new content-addressed Contract and current HasContract projection; old Contract Edges remain historical facts | pairing/reconciliation tests and projection selection |
| Candidate discovery must not assert topology | an alternative `G ⇒ A` appears in RelationAssessments while no second GuaranteeDischarge exists | candidate/acceptance integration test |
| Explicit acceptance must be safe | acceptance revalidates and then appends exactly the ordinary GuaranteeDischarge | candidate/acceptance integration test |
| Composition is algebraic, not a grouping label | result satisfies standard formula and is commutative/associative up to contract equivalence | exhaustive finite-assertion tests |
| Quotient represents a missing contract | `X ≤ C/C₁ ⇔ X∥C₁ ≤ C`, and `(C/C₁)∥C₁ ≤ C` | residual-law enumeration plus persisted-operation test |
| Operations cannot invent interface vocabulary | every result atom belongs to the union of operand interfaces | daemon pre-persistence law check |

These checks target spec-oracle’s expected outcome: more independently
checkable relationships and derived specifications in the specification graph,
without converting uncertainty, heuristics, or a merely shared label into an
Edge.
