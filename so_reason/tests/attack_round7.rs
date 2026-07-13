//! Adversarial conformance attack on the ROUND-7 changes: guard-aware
//! relations, relied formulas, count-quantifier entailment, content
//! complements (`<verb> that <clause>`), role-bearing relatives, envelope
//! conflicts, and role-measure exclusion.
//!
//! The code is the object under test. Passing tests pin sound behavior
//! permanently. The four findings below were reported by this attack and
//! FIXED in the same round: their tests (formerly `#[ignore]`) now assert
//! the sound expectation against the fixed code and pass.
//!
//! Findings (all fixed; details on each test):
//!
//! * FINDING 1 (count-negation unsoundness, false Yes): the relation engine
//!   treats the claim-level `Not` as classical outer negation
//!   (contraposition, double-negation collapse, mixed-polarity rules) while
//!   `formula.rs` legislates that the subject quantifier OUT-SCOPES `Not`
//!   (per-individual denial). Sound for Definite/Universal subjects,
//!   unsound for Count quantifiers, which round 7 newly grounds.
//! * FINDING 2 (vacuous guard witnesses overlap, false Yes): a sentence
//!   whose trigger equals its own `unless` clause has the empty
//!   applicability region `g ∧ ¬g`, yet `Top` on the other side still
//!   "witnesses" the overlap and a HardContradiction is reported for a
//!   jointly satisfiable pair.
//! * FINDING 3 (determiner accepted as relative verb, wrong parse): the
//!   round-7 relative verbal tail accepts `the` as its VERB, so object-gap
//!   relatives (`each request that the gateway forwards`) silently parse
//!   into a nonsense tree (verb `the`, object head `forwards`) instead of
//!   being rejected as round 6's `DeterminerAsVerb` rule does in verb
//!   position.
//! * FINDING 4 (position-dependent relative tails): `before`/`after`/
//!   `until` roles inside a relative parse in OBJECT position but are
//!   rejected in SUBJECT position, against change 5's full-tail promise.

use so_lang::ast::{ClauseBody, Core, Measure, NpGroup, Predicate, RelativeBody, RolePp, Sentence};
use so_lang::parse::{parse, ParseError};
use so_reason::formula::{
    claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula, PairingError,
};
use so_reason::relate::{assess, contradicts, implies, refines, Outcome, Ternary};
use so_reason::semantics::skeleton;

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("parse {input:?}: {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn claim(input: &str) -> Formula {
    claim_formula(&one(input)).expect("behavioral sentence")
}

fn guarantee(input: &str) -> Formula {
    contract_formula(&one(input))
        .expect("contract-bearing sentence")
        .guarantee
}

// =====================================================================================
// 1 — guard-aware relations
// =====================================================================================

/// SUPERSEDED PIN (round 9, recorded): reordered `and`-conjuncts used to
/// stay Unknown because guard equality was literal. Round 9 canonicalizes
/// guards before comparison — conjunction is commutative, so sorting the
/// operand lists loses nothing — and the reordered pair now witnesses the
/// one region it always denoted: HardContradiction.
#[test]
fn reordered_frame_conjuncts_now_ground() {
    assert_eq!(
        assess(
            &one("While the store is open and the till is active, the system shall issue the receipt."),
            &one("While the till is active and the store is open, the system shall not issue the receipt."),
        ),
        Outcome::HardContradiction
    );
}

/// SUPERSEDED PIN (round 9, recorded): reordered `or`-disjuncts ground
/// now too — disjunction is commutative, so the canonicalized alternation
/// guards are one region (the union of the two occurrences' regions).
/// The same-order or-group contradicted before and still does.
#[test]
fn or_group_guards_reordered_unknown_same_order_yes() {
    assert_eq!(
        assess(
            &one("When the order ships or the payment clears, the system shall issue the receipt."),
            &one("When the payment clears or the order ships, the system shall not issue the receipt."),
        ),
        Outcome::HardContradiction
    );
    assert_eq!(
        assess(
            &one("When the order ships or the payment clears, the system shall issue the receipt."),
            &one("When the order ships or the payment clears, the system shall not issue the receipt."),
        ),
        Outcome::HardContradiction
    );
}

/// An or-group guard against an and-group guard over the same clauses is
/// no shared region: Unknown, never Yes.
#[test]
fn or_group_vs_and_group_guards_stay_unknown() {
    assert_eq!(
        assess(
            &one("While the store is open or the till is active, the system shall issue the receipt."),
            &one("While the store is open and the till is active, the system shall not issue the receipt."),
        ),
        Outcome::Unknown
    );
}

/// Two `While` frames and one conjoined `While` group simplify to the same
/// `And`: a genuinely shared guard, so the conditional contradiction fires.
#[test]
fn stacked_frames_equal_conjoined_group() {
    assert_eq!(
        assess(
            &one("While the store is open, While the till is active, the system shall issue the receipt."),
            &one("While the store is open and the till is active, the system shall not issue the receipt."),
        ),
        Outcome::HardContradiction
    );
}

/// Idempotence in simplification: `While A and A` dedupes to `While A`, so
/// guard equality sees through the duplication.
#[test]
fn duplicate_conjunct_dedupes_into_guard_equality() {
    assert_eq!(
        assess(
            &one("While the store is open and the store is open, the system shall issue the receipt."),
            &one("While the store is open, the system shall not issue the receipt."),
        ),
        Outcome::HardContradiction
    );
}

/// SIMILAR but not EQUAL guard clauses must never witness overlap. The
/// clause skeleton drops a verbal body's object (`exceeds the limit` vs
/// `exceeds the threshold` digest alike); the guard atom's source anchor
/// is what keeps them apart — pin that it does.
#[test]
fn similar_guard_clauses_differing_in_object_stay_unknown() {
    assert_eq!(
        assess(
            &one("When the reading exceeds the limit, the pump shall stop."),
            &one("When the reading exceeds the threshold, the pump shall not stop."),
        ),
        Outcome::Unknown
    );
    // Different subject casing renders differently: also Unknown — the
    // guard identity is the render, conservative both ways.
    assert_eq!(
        assess(
            &one("When the Order ships, the system shall issue the receipt."),
            &one("When the order ships, the system shall not issue the receipt."),
        ),
        Outcome::Unknown
    );
}

/// SUPERSEDED (round 10, change 4 — this was the conscious change the
/// round-7 pin awaited): the frame FAMILY and the trigger KIND are now
/// part of guard-atom identity ([`so_reason::formula::GuardRole`]). `When
/// X` / `If X, then` / `While X` / `Where X` over the same clause words
/// are DIFFERENT conditions — a span the condition holds throughout vs
/// the instant it becomes true vs a spatial scope — and the round-7
/// "the state holds at the trigger instant" argument was a
/// temporal-semantics claim the engine does not model, so the cross-role
/// witness is retired in the conservative direction: `Unknown`, never a
/// manufactured HardContradiction. Same-role pairs still fire (pinned in
/// the surrounding tests and in round10.rs).
#[test]
fn frame_family_and_trigger_kind_are_guard_identity_round10() {
    // When vs If: same clause words, contradicting claims — Unknown now.
    assert_eq!(
        assess(
            &one("When the order ships, the system shall issue the receipt."),
            &one("If the order ships, then the system shall not issue the receipt."),
        ),
        Outcome::Unknown
    );
    // The guarantee formulas now DIFFER across the two trigger kinds: the
    // guard atom carries `Trigger { kind }`.
    assert_ne!(
        guarantee("When the order ships, the system shall issue the receipt."),
        guarantee("If the order ships, then the system shall issue the receipt."),
    );
    // Where vs While, While vs When: cross-role, Unknown.
    assert_eq!(
        assess(
            &one("Where the store is open, the system shall issue the receipt."),
            &one("While the store is open, the system shall not issue the receipt."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("While the store is open, the system shall issue the receipt."),
            &one("When the store is open, the system shall not issue the receipt."),
        ),
        Outcome::Unknown
    );
}

/// Exceptions are guard structure: equal trigger AND equal exception on
/// both sides is a shared region (contradiction); an exception on one side
/// only breaks guard equality (Unknown — the carved regions differ).
#[test]
fn exception_presence_is_guard_identity() {
    assert_eq!(
        assess(
            &one("When the order ships, the system shall issue the receipt, unless the customer cancels."),
            &one("When the order ships, the system shall not issue the receipt, unless the customer cancels."),
        ),
        Outcome::HardContradiction
    );
    assert_eq!(
        assess(
            &one("When the order ships, the system shall issue the receipt."),
            &one("When the order ships, the system shall not issue the receipt, unless the customer cancels."),
        ),
        Outcome::Unknown
    );
}

/// An unconditional obligation refines its When-guarded counterpart
/// (assumptions equal at Top; the unconditional guarantee is stronger).
#[test]
fn unconditional_refines_conditional() {
    let unframed = one("The system shall issue the receipt.");
    let framed = one("When the order ships, the system shall issue the receipt.");
    assert_eq!(
        refines(
            &contract_formula(&unframed).unwrap(),
            &contract_formula(&framed).unwrap()
        ),
        Ternary::Yes
    );
    assert_eq!(
        assess(&unframed, &framed),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
}

/// Guard equality survives render → reparse: the canonical form of a
/// framed pair keeps the same outcome, `If … , then` rendering included.
#[test]
fn guard_outcomes_survive_render_reparse() {
    let pairs = [
        (
            "When the order ships, the system shall issue the receipt.",
            "When the order ships, the system shall not issue the receipt.",
            Outcome::HardContradiction,
        ),
        (
            "If the disk fails, then the system shall alert the operator.",
            "If the disk fails, then the system shall not alert the operator.",
            Outcome::HardContradiction,
        ),
        (
            "When the order ships, the system shall issue the receipt, unless the customer cancels.",
            "When the order ships, the system shall not issue the receipt, unless the customer cancels.",
            Outcome::HardContradiction,
        ),
    ];
    for (a, b, expected) in pairs {
        let a2 = one(&one(a).render());
        let b2 = one(&one(b).render());
        assert_eq!(
            assess(&a2, &b2),
            expected,
            "outcome drifts through render for {a:?}"
        );
    }
}

/// FINDING 2 — a syntactically EMPTY applicability region (`When X …
/// unless X` conjoins a guard atom with its own negation) still counts as
/// overlap under a `Top` witness, and even under guard EQUALITY: assess
/// reports HardContradiction for jointly satisfiable pairs (the vacuous
/// sentence never applies). The legislated Top-witness rationale — "a
/// sentence asserts under its own guard, so its own region is what its
/// claim is in force over" — fails when that region is provably empty by
/// the same syntactic means the engine already trusts (`g ∧ ¬g` over one
/// guard atom). Sound expectation: Unknown, never Yes.
#[test]
fn vacuous_guard_must_not_witness_overlap() {
    let vacuous =
        one("When the order ships, the system shall issue the receipt, unless the order ships.");
    let top = one("The system shall not issue the receipt.");
    assert_eq!(assess(&vacuous, &top), Outcome::Unknown);
    // Equal vacuous guards on both sides: the shared region is still empty.
    let vacuous_not = one(
        "When the order ships, the system shall not issue the receipt, unless the order ships.",
    );
    assert_eq!(assess(&vacuous, &vacuous_not), Outcome::Unknown);
}

// =====================================================================================
// 2 — relied formulas on pairing edges
// =====================================================================================

/// Envelope sources stay out of the paired assumption even when they carry
/// an explicit relied formula: reliance never turns compatibility data
/// into an assumption conjunct.
#[test]
fn envelope_with_explicit_relied_stays_out_of_assumption() {
    let target = one("The daemon shall process the event.");
    let envelope_source = one("The client may retry.");
    let relied = claim_formula(&envelope_source).unwrap();
    let envelope = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::AdmissibilityEnvelope,
        &envelope_source,
        &target,
        relied,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(
        paired.assumption,
        Formula::Top,
        "envelope reliance must not enter A"
    );
    assert_eq!(
        paired.sources.len(),
        1,
        "the envelope is retained as compatibility data"
    );
    // Saturation therefore never negates the permission.
    assert_eq!(paired.saturated(), paired.guarantee);
}

/// Validation ORDER is pinned: the act × kind matrix gates before the
/// relied entailment check. SUPERSEDED IN PART (round 10, change 6): the
/// round-6 same-subject REJECTION is removed — a shared responsible
/// subject is now recorded as `SubjectRelation::SharedKeys` (candidate
/// data), so the same-subject source below constructs far enough for the
/// relied entailment check to fire and reports
/// SourceDoesNotSupportRelied.
#[test]
fn relied_validation_runs_after_subject_and_act_gates() {
    let target = one("The daemon shall process the event.");
    // The negation of the source's own claim: implies() proves No, so the
    // reliance is provably unsupported.
    let bad_relied = guarantee("The daemon shall not emit the event.");
    let err = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &one("The daemon shall emit the event."),
        &target,
        bad_relied.clone(),
    )
    .unwrap_err();
    assert_eq!(err, PairingError::SourceDoesNotSupportRelied);
    // Recommendation as discharge: act gate fires before relied.
    let err = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::GuaranteeDischarge,
        &one("The gateway should deliver the event."),
        &target,
        bad_relied,
    )
    .unwrap_err();
    assert_eq!(err, PairingError::RecommendationOnlyReliance);
}

/// `relied: Top` is provably entailed (accepted) and pairs to a `Top`
/// assumption — relying on nothing at all is expressible.
/// `relied: Bottom` — SUPERSEDED PIN (round 8, change 2): round 7 accepted
/// it under the Unknown-is-accepted conservatism, but A = ⊥ makes the
/// saturated form `G ∨ ¬A` a tautology, erasing the guarantee — an erasure
/// provable from the shape alone, so accepting it was never conservative.
/// It is now `PairingError::VacuousRelied`.
#[test]
fn relied_top_and_bottom_pin_the_documented_conservatism() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    let top = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        Formula::Top,
    )
    .unwrap();
    assert_eq!(
        contract_formula(&target)
            .unwrap()
            .paired(std::slice::from_ref(&top))
            .assumption,
        Formula::Top
    );
    let bottom = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        Formula::Bottom,
    );
    assert_eq!(
        bottom.unwrap_err(),
        PairingError::VacuousRelied,
        "round 8: a ⊥ reliance erases the guarantee and is rejected"
    );
}

/// Serde: an explicit JSON `null` for `relied` behaves exactly like the
/// missing pre-round-7 field — the reliance defaults to the source
/// formula, not to an error.
#[test]
fn relied_null_json_defaults_to_source_formula() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    let s =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let mut json = serde_json::to_value(&s).unwrap();
    json.as_object_mut()
        .unwrap()
        .insert("relied".into(), serde_json::Value::Null);
    let back: AssumptionSource = serde_json::from_value(json).unwrap();
    assert_eq!(back.relied, back.formula);
    assert_eq!(back, s);
}

// =====================================================================================
// 3 — count-quantifier entailment
// =====================================================================================

/// The at-most side of the triangle: `at most 3` implies `at most 7`,
/// never the reverse; `at least 4` vs `at most 3` is a strict exclusion
/// (no touching bound).
#[test]
fn at_most_containment_and_strict_exclusion() {
    assert_eq!(
        implies(
            &claim("At most 3 replicas shall run."),
            &claim("At most 7 replicas shall run.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &claim("At most 7 replicas shall run."),
            &claim("At most 3 replicas shall run.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &claim("At least 4 replicas shall run."),
            &claim("At most 3 replicas shall run.")
        ),
        Ternary::Yes
    );
}

/// Two different point intervals exclude each other: `exactly 5` vs
/// `exactly 3` contradict; the same point is one claim (No, not Yes).
#[test]
fn exactly_points_exclude_and_self_compare_no() {
    assert_eq!(
        contradicts(
            &claim("Exactly 5 replicas shall run."),
            &claim("Exactly 3 replicas shall run.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &claim("Exactly 3 replicas shall run."),
            &claim("Exactly 3 replicas shall run.")
        ),
        Ternary::No
    );
}

/// Object-position triangle: `exactly 4` bridges to `at most 7`;
/// coordinated objects ground when exactly ONE pair differs by Count; an
/// `or`-group never meets an `and`-group (the conjunction is identity).
#[test]
fn object_count_triangle_and_coordination() {
    assert_eq!(
        implies(
            &claim("The daemon shall keep exactly 4 replicas."),
            &claim("The daemon shall keep at most 7 replicas."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &claim("The daemon shall keep at least 5 replicas and the index."),
            &claim("The daemon shall keep at least 3 replicas and the index."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &claim("The daemon shall keep at least 5 replicas or the index."),
            &claim("The daemon shall keep at least 3 replicas and the index."),
        ),
        Ternary::Unknown
    );
}

/// A bare-plural object (Quantifier::None — objects are NOT generic-
/// normalized) never grounds against a Count object: Unknown.
#[test]
fn bare_plural_object_vs_count_stays_unknown() {
    assert_eq!(
        implies(
            &claim("The daemon shall keep replicas."),
            &claim("The daemon shall keep at least 3 replicas."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        implies(
            &claim("The daemon shall keep at least 3 replicas."),
            &claim("The daemon shall keep replicas."),
        ),
        Ternary::Unknown
    );
}

/// A restrictor difference blocks the subject-count rule: `at least 5
/// healthy replicas` vs `at least 3 replicas` share head but not
/// restrictor/full — Unknown.
#[test]
fn count_subjects_with_differing_restrictors_stay_unknown() {
    assert_eq!(
        implies(
            &claim("At least 5 healthy replicas shall run."),
            &claim("At least 3 replicas shall run."),
        ),
        Ternary::Unknown
    );
}

/// Counted subjects carrying RELATIVE clauses: the full identity includes
/// the relative (round 5/7 interaction), so equal relatives ground the
/// count rule and differing relatives block it.
#[test]
fn count_subjects_with_relatives_use_full_identity() {
    assert_eq!(
        implies(
            &claim("At least 5 requests that arrive from the gateway shall be logged."),
            &claim("At least 3 requests that arrive from the gateway shall be logged."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &claim("At least 5 requests that arrive from the gateway shall be logged."),
            &claim("At least 3 requests that arrive from the proxy shall be logged."),
        ),
        Ternary::Unknown
    );
}

/// Count outcomes survive render → reparse.
#[test]
fn count_outcomes_survive_render_reparse() {
    let a = one(&one("At least 5 replicas shall run.").render());
    let b = one(&one("At most 3 replicas shall run.").render());
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
}

/// Counts under a shared guard: the guard-aware rule and the count
/// exclusion compose end to end.
#[test]
fn guarded_count_exclusion_is_a_conditional_contradiction() {
    assert_eq!(
        assess(
            &one("When the order ships, at least 5 replicas shall run."),
            &one("When the order ships, at most 3 replicas shall run."),
        ),
        Outcome::HardContradiction
    );
    assert_eq!(
        assess(
            &one("When the order ships, at least 5 replicas shall run."),
            &one("When the payment clears, at most 3 replicas shall run."),
        ),
        Outcome::Unknown
    );
}

/// Object-position negation contraposes SOUNDLY (the `Not` is predicate-
/// level over one definite subject): not-keeping ≥3 implies not-keeping
/// ≥5. This pins the sound half of the contraposition rule so FINDING 1
/// stays sharply scoped to subject counts.
#[test]
fn object_count_contraposition_is_sound() {
    assert_eq!(
        implies(
            &claim("The daemon shall not keep at least 3 replicas."),
            &claim("The daemon shall not keep at least 5 replicas."),
        ),
        Ternary::Yes
    );
}

/// FINDING 1a — subject-count entailment under negation is REVERSED. Per
/// the formula layer's own scope convention (`Not` is per-individual; the
/// subject quantifier out-scopes it), `At least 3 replicas shall not run.`
/// denotes "≥3 replicas refrain", which does NOT entail "≥5 replicas
/// refrain" — counter-model: ten replicas, exactly three refrain. The
/// engine answers Yes by contraposing through the `Not` wrapper as if it
/// were classical outer negation. Sound expectation: Unknown.
#[test]
fn negated_count_subjects_must_not_contrapose() {
    assert_eq!(
        implies(
            &claim("At least 3 replicas shall not run."),
            &claim("At least 5 replicas shall not run."),
        ),
        Ternary::Unknown
    );
}

/// FINDING 1b — `At least 5 replicas shall run.` and `At least 3 replicas
/// shall not run.` are jointly satisfiable (eight replicas: five run,
/// three refrain), yet the double-negation collapse turns the second
/// claim's `¬` into set-complement and reports a contradiction — end to
/// end a false HardContradiction. Sound expectation: Unknown.
#[test]
fn count_obligation_and_count_prohibition_are_satisfiable_together() {
    assert_eq!(
        contradicts(
            &claim("At least 5 replicas shall run."),
            &claim("At least 3 replicas shall not run."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        assess(
            &one("At least 5 replicas shall run."),
            &one("At least 3 replicas shall not run."),
        ),
        Outcome::Unknown
    );
}

/// FINDING 1c — the same-proposition mixed-polarity rule misfires on
/// counted subjects: `Exactly 3 replicas shall run.` (three run) and
/// `Exactly 3 replicas shall not run.` (three refrain) coexist in any
/// six-replica system, yet assess reports HardContradiction. Sound
/// expectation: Unknown.
#[test]
fn exact_count_with_opposite_polarity_is_not_a_contradiction() {
    assert_eq!(
        assess(
            &one("Exactly 3 replicas shall run."),
            &one("Exactly 3 replicas shall not run."),
        ),
        Outcome::Unknown
    );
}

// =====================================================================================
// 4 — content complements
// =====================================================================================

/// Shapes: ensure/verify/record with a content clause parse, render
/// canonically, and re-parse stably.
#[test]
fn content_shapes_render_round_trip() {
    for input in [
        "The daemon shall record that the token is valid.",
        "The monitor shall ensure that the daemon retains the log for 30 days.",
        "The system shall verify within 5 seconds that the token is valid.",
        "The server shall either ensure that the token is valid or reject the request.",
        "When the order ships, the auditor shall verify that the receipt is issued.",
    ] {
        let s = one(input);
        let rendered = s.render();
        let re = one(&rendered);
        assert_eq!(re.render(), rendered, "canonical form re-parses: {input}");
        assert_eq!(
            re,
            one(&re.render()),
            "second round trip is a fixpoint: {input}"
        );
    }
}

/// Relative-`that` vs content-`that` at every position: directly after
/// the verb it is content; directly after an object NOUN or a role NOUN
/// the relative machinery claims it (and a clause-shaped body is then a
/// parse error, never silently re-read as content).
#[test]
fn relative_that_wins_after_object_and_role_nouns() {
    // After the verb: content.
    let s = one("The daemon shall record that the token is valid.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("deontic")
    };
    let vp = vp.single().unwrap();
    assert!(vp.object.is_none());
    assert!(vp.content.is_some());
    // After an object noun: the relative claims it and rejects the
    // determiner at verb position. (Superseded pin, recorded: before the
    // FINDING 3 fix the relative accepted verb `the` and failed later, on
    // `is`, as UnexpectedTokens; the DeterminerAsVerb diagnosis now fires
    // at the true fault site.)
    assert!(matches!(
        parse("The daemon shall notify the admin that the token is valid."),
        Err(ParseError::DeterminerAsVerb { .. })
    ));
    // After a recipient role's noun: same — the role NP claims the `that`.
    assert!(matches!(
        parse("The daemon shall report to the auditor that the token is valid."),
        Err(ParseError::DeterminerAsVerb { .. })
    ));
    // A WELL-FORMED relative in the role NP stays a relative — no content.
    let s = one("The daemon shall report to the auditor that holds the seal.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("deontic")
    };
    let vp = vp.single().unwrap();
    assert!(vp.content.is_none());
    let RolePp::Recipient(NpGroup::Single(np)) = &vp.roles[0] else {
        panic!("recipient")
    };
    assert!(np.relative.is_some(), "the role noun claimed the `that`");
}

/// Content inside `either … or …` alternatives (legislated ALLOWED): the
/// content clause stays inside ITS alternative — it does not absorb the
/// `or` tail, and only the first item carries it.
#[test]
fn content_stays_inside_its_alternative() {
    let s = one("The server shall either ensure that the token is valid or reject the request.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("deontic")
    };
    let items = vp.items();
    assert_eq!(items.len(), 2, "the or-split survives the content clause");
    assert_eq!(items[0].verb, "ensure");
    assert_eq!(
        items[0].content.as_ref().map(|c| c.render()),
        Some("the token is valid".to_string())
    );
    assert_eq!(items[1].verb, "reject");
    assert!(items[1].content.is_none());
}

/// Content after a `be`-complement (legislated allowed: the slot sits
/// after the shared role tail, uniform across verb-phrase positions).
#[test]
fn content_after_be_complement_is_legislated() {
    let s = one("The status shall be valid that the token is valid.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("deontic")
    };
    let vp = vp.single().unwrap();
    assert!(matches!(vp.complement, Some(Predicate::Words { .. })));
    assert!(vp.content.is_some());
    let rendered = s.render();
    assert_eq!(one(&rendered).render(), rendered);
}

/// SUPERSEDED PIN (round 8, change 4): the content clause still consumes
/// the REST of the verb phrase, so a deadline written AFTER the content
/// stays INSIDE the content clause (attachment stays inner, legislated) —
/// but copular clause bodies now carry a thematic-role tail, so the inner
/// deadline is a STRUCTURED Deadline role on the content clause, not
/// opaque predicate words. The round-7 gap — the same words carrying
/// interval structure in one position and none in the other — is closed.
#[test]
fn deadline_after_content_is_structured_inside_the_content_clause() {
    let s = one("The system shall verify that the token is valid within 5 seconds.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("deontic")
    };
    let vp = vp.single().unwrap();
    assert!(
        vp.roles.is_empty(),
        "no outer deadline role: attachment stays inner"
    );
    let content = vp.content.as_ref().expect("content");
    let ClauseBody::Copular {
        predicate: Predicate::Words { words },
        roles,
        ..
    } = &content.body
    else {
        panic!("copular content, got {:?}", content.body);
    };
    assert_eq!(words, &["valid"]);
    assert!(
        matches!(roles.as_slice(), [RolePp::Deadline(Measure::Quantity { number, unit })]
            if number == "5" && unit.as_deref() == Some("seconds")),
        "the inner deadline is structured, got {roles:?}"
    );
    // Still pinned: inner and outer attachment are DIFFERENT claims —
    // the contents differ (identity includes the full render), so the
    // two forms relate only as Unknown.
    assert_eq!(
        implies(
            &claim("The system shall verify within 5 seconds that the token is valid."),
            &claim("The system shall verify that the token is valid within 5 seconds."),
        ),
        Ternary::Unknown
    );
}

/// Content is identity; everything around it still grounds. Equal
/// contents let the outer deadline containment fire; differing NESTED
/// role measures inside the content block Yes (full-fidelity guard).
#[test]
fn content_identity_gates_outer_measure_hooks() {
    assert_eq!(
        implies(
            &claim("The auditor shall verify within 5 seconds that the token is valid."),
            &claim("The auditor shall verify within 10 seconds that the token is valid."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &claim("The auditor shall verify within 10 seconds that the token is valid."),
            &claim("The auditor shall verify within 5 seconds that the token is valid."),
        ),
        Ternary::Unknown
    );
    // Nested measure differences are content differences: Unknown, both
    // directions, and no contradiction either.
    assert_eq!(
        implies(
            &claim("The monitor shall ensure that the daemon retains the log for 30 days."),
            &claim("The monitor shall ensure that the daemon retains the log for 10 days."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &claim("The monitor shall ensure that the daemon retains the log for 30 days."),
            &claim("The monitor shall ensure that the daemon retains the log for 10 days."),
        ),
        Ternary::Unknown
    );
    // Content-bearing vs content-free: contradicts is Unknown too.
    assert_eq!(
        contradicts(
            &claim("The monitor shall ensure that the reading exceeds the limit."),
            &claim("The monitor shall not ensure the reading."),
        ),
        Ternary::Unknown
    );
}

/// Depth: the shared budget flows through the content clause — a deep
/// `of`-chain inside content is PhraseTooDeep, not a stack overflow.
#[test]
fn content_depth_stays_bounded() {
    let deep = format!(
        "The monitor shall ensure that the owner {} is active.",
        "of the owner ".repeat(70)
    );
    assert!(matches!(
        parse(&deep),
        Err(ParseError::PhraseTooDeep { .. })
    ));
}

// =====================================================================================
// 5 — role-bearing relatives
// =====================================================================================

/// Relatives with particles, manner, sources, means, and locations render
/// round-trip, in subject and object position, `who` included.
#[test]
fn relative_tail_combinations_round_trip() {
    for input in [
        "Each request that arrives from the gateway via the tunnel shall be logged.",
        "The daemon shall archive each job that completes successfully on the primary node.",
        "The daemon shall close each session that times out in the vault.",
        "Each user who logs out from the portal shall be notified via email.",
        "The daemon shall inspect each packet that arrives before the window closes.",
    ] {
        let s = one(input);
        let rendered = s.render();
        let re = one(&rendered);
        assert_eq!(re.render(), rendered, "canonical form re-parses: {input}");
    }
}

/// The relative's roles are part of `np_full` in OBJECT position too:
/// `close each session that times out` never meets `close each session`
/// (Unknown), and the skeleton's object identity carries the tail.
#[test]
fn object_relative_roles_are_identity() {
    assert_eq!(
        implies(
            &claim("The daemon shall close each session that times out."),
            &claim("The daemon shall close each session."),
        ),
        Ternary::Unknown
    );
    let sk = skeleton(&one("The daemon shall close each session that times out.")).unwrap();
    assert_eq!(sk.atoms[0].objects[0].full, "session that times out");
    let sk = skeleton(&one(
        "At least 5 requests that arrive from the gateway shall be logged.",
    ))
    .unwrap();
    assert_eq!(sk.subject.full, "requests that arrive from the gateway");
}

/// The subject-relative gateway pair from the round docs, attacked with a
/// prohibition: same relative + opposite polarity is a contradiction;
/// differing relative roles keep it Unknown.
#[test]
fn subject_relative_contradiction_and_lossiness() {
    assert_eq!(
        assess(
            &one("Each request that arrives from the gateway shall be logged."),
            &one("Each request that arrives from the gateway shall not be logged."),
        ),
        Outcome::HardContradiction
    );
    assert_eq!(
        assess(
            &one("Each request that arrives from the gateway shall be logged."),
            &one("Each request that arrives from the proxy shall not be logged."),
        ),
        Outcome::Unknown
    );
}

/// Depth: a deep `of`-chain inside a relative's ROLE noun phrase lands on
/// PhraseTooDeep.
#[test]
fn relative_role_depth_stays_bounded() {
    let deep = format!(
        "Each request that arrives from the owner {} shall be logged.",
        "of the owner ".repeat(70)
    );
    assert!(matches!(
        parse(&deep),
        Err(ParseError::PhraseTooDeep { .. })
    ));
}

/// FINDING 4 — relative-tail acceptance is POSITION-DEPENDENT for clausal
/// roles: `each packet that arrives before the window closes` parses in
/// OBJECT position (pinned in `relative_tail_combinations_round_trip`)
/// but the identical relative in SUBJECT position is rejected with
/// `unexpected shall` — the subject/pivot split machinery does not carry
/// the round-7 clausal-role tail. Change 5 promises the FULL verbal tail
/// (mirroring `ClauseBody::Verbal`) with no position caveat, and the
/// rejection message ("the sentence was complete before it") misdiagnoses
/// the input. Sound expectation: the subject-position sentence parses and
/// round-trips like its object-position twin. (Drift, not unsoundness:
/// the failure is a precise error, never a wrong tree.)
#[test]
fn subject_relative_clausal_roles_must_parse() {
    for input in [
        "Each packet that arrives before the window closes shall be inspected.",
        "Each packet that arrives on the public interface before the window closes shall be inspected.",
        "Each packet that arrives until the window closes shall be inspected.",
    ] {
        let s = one(input);
        let rendered = s.render();
        assert_eq!(one(&rendered).render(), rendered, "round trip: {input}");
    }
}

/// FINDING 3, SUPERSEDED (round 9, recorded): object-gap relatives are
/// SUPPORTED now — `Each request that the gateway forwards shall be
/// logged.` parses into a correct gap tree (round 9, change 3), so the
/// round-7 must-reject pin no longer holds for well-formed gaps. What
/// remains pinned: a det-led relative with NO verb after any subject
/// split is still rejected (never the round-6 nonsense tree with the
/// determiner as verb).
#[test]
fn object_gap_relatives_must_be_rejected() {
    for input in [
        "Each request that the gateway forwards shall be logged.",
        "The daemon shall close each session that the scheduler owns.",
    ] {
        assert!(
            parse(input).is_ok(),
            "a well-formed object-gap relative parses now: {input}"
        );
    }
    assert!(
        parse("Each request that the gateway shall be logged.").is_err(),
        "a det-led relative with no verb stays rejected"
    );
}

/// FINDING 3 (companion pin — superseded again in round 9, recorded): the
/// round-7 fix rejected the motivating sentence as DeterminerAsVerb; the
/// round-9 object-gap reading parses it. The diagnosis still stands
/// exactly where the gap reading refuses: an explicit determiner-led
/// object after the gap verb (not a gap — the head is not the missing
/// object).
#[test]
fn object_gap_relative_rejection_is_determiner_as_verb() {
    assert!(parse("Each request that the gateway forwards shall be logged.").is_ok());
    assert!(matches!(
        parse("Each request that the gateway forwards the packet shall be logged."),
        Err(ParseError::DeterminerAsVerb { .. })
    ));
    // The subject-gap twin stays accepted: the gate rejects determiners at
    // VERB position only, never a verb-led relative body.
    let s = one("Each request that arrives shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!("single")
    };
    let RelativeBody::Verbal { verb, .. } = &np.relative.as_ref().unwrap().body else {
        panic!("verbal relative")
    };
    assert_eq!(verb, "arrives");
}

// =====================================================================================
// 6 — envelope conflicts
// =====================================================================================

/// A universal permission against a subject-`no` prohibition: `Each
/// client may retry.` vs `No client shall retry.` normalize to one
/// proposition — a genuine envelope conflict.
#[test]
fn universal_permission_vs_no_subject_prohibition_conflicts() {
    assert_eq!(
        assess(
            &one("Each client may retry."),
            &one("No client shall retry.")
        ),
        Outcome::EnvelopeConflict
    );
    assert_eq!(
        assess(
            &one("No client shall retry."),
            &one("Each client may retry.")
        ),
        Outcome::EnvelopeConflict
    );
}

/// Full identity gates the conflict: an `of`-chain difference on the
/// subject blocks it, a role on the prohibited behavior blocks it — never
/// a conflict between different propositions.
#[test]
fn envelope_conflict_requires_full_proposition_identity() {
    assert_eq!(
        assess(
            &one("The client of the gateway may retry."),
            &one("The client of the proxy shall not retry."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("The client may retry."),
            &one("The client shall not retry within 5 seconds."),
        ),
        Outcome::Unknown
    );
}

/// The description side: `may be active` vs `is never active` (a negative
/// state description bounds the same way a prohibition does).
#[test]
fn permission_vs_negative_state_description_conflicts() {
    assert_eq!(
        assess(
            &one("The client may be active."),
            &one("The client is never active.")
        ),
        Outcome::EnvelopeConflict
    );
}

/// Guard interaction: equal While-guards conflict; a While-guard against
/// a When-guard with different words does not; a `Top`-guarded permission
/// against an exception-carved prohibition conflicts (the permission's
/// `Top` witnesses the prohibition's own carved region).
#[test]
fn envelope_conflict_guard_matrix() {
    assert_eq!(
        assess(
            &one("While the store is open, the client may retry."),
            &one("While the store is open, the client shall not retry."),
        ),
        Outcome::EnvelopeConflict
    );
    assert_eq!(
        assess(
            &one("When the queue drains, the client may retry."),
            &one("While the store is open, the client shall not retry."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("The client may retry."),
            &one("The client shall not retry, unless the link fails."),
        ),
        Outcome::EnvelopeConflict
    );
}

/// Per the legislation: permission × obligation stays Unknown (also with
/// count subjects), recommendations never bound, permission alternatives
/// (an `Or` of admissibility atoms) stay out entirely.
#[test]
fn envelope_conflict_scope_pins() {
    assert_eq!(
        assess(
            &one("At least 3 clients may retry."),
            &one("At least 3 clients shall retry.")
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("The client may retry."),
            &one("The client should not retry.")
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("The client may either retry or reconnect."),
            &one("The client shall not retry."),
        ),
        Outcome::Unknown
    );
    // Coordinated permission subjects: conservative Unknown (the claim is
    // an And over per-item atoms, not a single admissibility atom).
    assert_eq!(
        assess(
            &one("The client and the proxy may retry."),
            &one("The client shall not retry."),
        ),
        Outcome::Unknown
    );
}

/// FINDING 1d — envelope conflicts inherit the count-quantifier
/// out-scoping problem: `At least 3 clients may retry.` and `At least 3
/// clients shall not retry.` can pick DIFFERENT witness sets (six
/// clients: three tolerated retriers, three refraining), so the
/// prohibition does not forbid exactly what the permission admits; only
/// Definite/Universal subjects make the two atoms co-referential. Sound
/// expectation: Unknown.
#[test]
fn count_subject_envelope_pair_is_not_a_conflict() {
    assert_eq!(
        assess(
            &one("At least 3 clients may retry."),
            &one("At least 3 clients shall not retry."),
        ),
        Outcome::Unknown
    );
}

// =====================================================================================
// 7 — role-measure exclusion
// =====================================================================================

/// Bounded `between` durations: disjoint from a lower bound above them;
/// overlapping bounded pairs stay Unknown; the touching-point pair
/// (`at least 10` vs `at most 10`) intersects at 10 — Unknown; the open
/// touching pair (`at least 10` vs `less than 10`) is empty — Yes.
#[test]
fn duration_interval_boundary_matrix() {
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for between 5 and 10 days."),
            &claim("The daemon shall retain the log for at least 30 days."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for between 5 and 10 days."),
            &claim("The daemon shall retain the log for between 8 and 12 days."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for at least 10 days."),
            &claim("The daemon shall retain the log for at most 10 days."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for at least 10 days."),
            &claim("The daemon shall retain the log for less than 10 days."),
        ),
        Ternary::Yes
    );
}

/// Number WORDS ground the same intervals as numerals.
#[test]
fn number_words_ground_role_exclusion() {
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for at least ten days."),
            &claim("The daemon shall retain the log for less than two days."),
        ),
        Ternary::Yes
    );
}

/// Everything-else-matches is load-bearing: perturb ONE other field —
/// manner, a recipient role, or an object count — and the exclusion must
/// not fire.
#[test]
fn role_exclusion_blocked_by_any_second_difference() {
    // Manner difference.
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain quickly the log for at least 30 days."),
            &claim("The daemon shall retain the log for less than 10 days."),
        ),
        Ternary::Unknown
    );
    // A differing recipient role next to the differing measure.
    assert_eq!(
        contradicts(
            &claim("The daemon shall send the report to the admin for at least 30 days."),
            &claim("The daemon shall send the report to the owner for less than 10 days."),
        ),
        Ternary::Unknown
    );
    // A differing object count next to the differing deadline.
    assert_eq!(
        contradicts(
            &claim("The daemon shall keep at least 5 replicas within 5 seconds."),
            &claim("The daemon shall keep at most 3 replicas within 10 seconds."),
        ),
        Ternary::Unknown
    );
}

/// Guard-equal duration exclusion composes with change 1: the disjoint
/// durations under one shared guard are a conditional contradiction.
#[test]
fn guarded_duration_exclusion_is_a_conditional_contradiction() {
    assert_eq!(
        assess(
            &one("When the order ships, the daemon shall retain the log for at least 30 days."),
            &one("When the order ships, the daemon shall retain the log for less than 10 days."),
        ),
        Outcome::HardContradiction
    );
    assert_eq!(
        assess(
            &one("When the order ships, the daemon shall retain the log for at least 30 days."),
            &one("When the payment clears, the daemon shall retain the log for less than 10 days."),
        ),
        Outcome::Unknown
    );
}

// =====================================================================================
// 8 — totality: seeded fuzz over round-7 constructs
// =====================================================================================

/// A deterministic LCG so the fuzz corpus is reproducible.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn pick<'a>(&mut self, items: &'a [&'a str]) -> &'a str {
        items[(self.next() as usize) % items.len()]
    }
}

/// Seeded fuzz mixing frames, that-clauses, relatives with roles, counts,
/// exceptions, and purposes: parse must never panic; every accepted
/// sentence must render to a canonical form that re-parses to a fixpoint;
/// skeleton/claim/contract derivation and pairwise assess must be total.
#[test]
fn seeded_fuzz_over_round7_constructs_is_total() {
    let frames = [
        "",
        "When the order ships, ",
        "While the store is open, ",
        "If the disk fails, then ",
        "Where the feature is enabled, ",
        "While the store is open and the till is active, ",
        "When the order ships or the payment clears, ",
    ];
    let subjects = [
        "the daemon",
        "each request that arrives from the gateway",
        "at least 3 replicas",
        "no client",
        "the owner of the file",
        "each user who logs out",
        "exactly 4 workers",
        "at most 7 sessions that time out",
        "requests",
    ];
    let modals = ["shall", "shall not", "should", "may", "must"];
    let vps = [
        "stop",
        "keep at least 5 replicas",
        "retain the log for at least 30 days",
        "ensure that the token is valid",
        "notify the admin via email",
        "be logged by the daemon",
        "verify within 5 seconds that the token is valid",
        "either accept the request or reject the request",
        "close each session that the scheduler owns",
        "record that the daemon retains the log for 30 days",
        "time out",
        "be at most 3",
    ];
    let tails = [
        "",
        ", unless the override is active",
        ", so that the operator retains control",
        ", unless the order ships",
    ];
    let mut rng = Lcg(0x5eed_2026_0707);
    let mut accepted: Vec<Sentence> = Vec::new();
    for _ in 0..400 {
        let input = format!(
            "{}{} {} {}{}.",
            rng.pick(&frames),
            rng.pick(&subjects),
            rng.pick(&modals),
            rng.pick(&vps),
            rng.pick(&tails),
        );
        let Ok(spec) = parse(&input) else { continue };
        for s in spec.sentences {
            // Canonical form re-parses to a fixpoint.
            let rendered = s.render();
            let re = parse(&rendered)
                .unwrap_or_else(|e| panic!("canonical form must re-parse: {rendered:?}: {e}"));
            assert_eq!(
                re.sentences[0].render(),
                rendered,
                "render is a fixpoint for {input:?}"
            );
            // Derivations are total.
            let _ = skeleton(&s);
            let _ = claim_formula(&s);
            let _ = contract_formula(&s);
            let _ = so_reason::semantics::subject_keys(&s);
            accepted.push(s);
        }
    }
    assert!(
        accepted.len() > 100,
        "the fuzz corpus must exercise accepted sentences"
    );
    // Pairwise relation totality over a sliding window.
    for pair in accepted.windows(2) {
        let _ = assess(&pair[0], &pair[1]);
        let _ = assess(&pair[1], &pair[0]);
        if let (Some(a), Some(b)) = (claim_formula(&pair[0]), claim_formula(&pair[1])) {
            let _ = implies(&a, &b);
            let _ = contradicts(&a, &b);
        }
    }
}
