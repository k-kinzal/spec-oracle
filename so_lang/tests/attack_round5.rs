//! Adversarial conformance attack on the round-5 changes (IMPROVE-SPEC-5):
//! validated typed pairing, generic behavioral subjects, the minimal relation
//! engine, modifier-bearing subject keys, the legislated `for`/`with`/`by`,
//! `who`/`that` relative attachment, adverbial capability, and totality under
//! seeded fuzz over the new constructs.
//!
//! Every passing test is a permanent pin of round-5 behavior. Expectations
//! the implementation does not meet are `#[ignore]`d and carry their finding
//! title, per the attack protocol. The round-5 fixer resolved the suite's
//! findings in src (predicate noun phrases now stop at `by`; the passive
//! site requires a complemented `be`), so every test now runs un-ignored;
//! the fixed findings keep their FINDING doc comments as history.

use so_lang::ast::*;
use so_lang::formula::{
    claim_formula, contract_formula, AssumptionSource, AtomRef, ContractFormula, EdgeKind,
    Formula, PairingError,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{contradicts, implies, refines, Ternary};
use so_lang::semantics::{
    denote, skeleton, speech_act, subject_keys, Claim, Denotation, Polarity, Quantifier,
    RoleKind, RoleValue, SpeechAct,
};
use std::panic::{catch_unwind, AssertUnwindSafe};

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got {e:?}"));
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

fn claim(input: &str) -> Formula {
    claim_formula(&one(input)).expect("claim formula")
}

fn contract(input: &str) -> ContractFormula {
    contract_formula(&one(input)).expect("contract formula")
}

/// Round 11 (change 3): pairing pins build their sources with an EXPLICIT
/// reliance (the whole source conditional, explicitly selected through the
/// graph-edge entry point) — a default reliance is a permanent candidate
/// now and never forms A.
fn explicit_source(kind: EdgeKind, source: &str, target: &str) -> AssumptionSource {
    let source = one(source);
    let relied = AssumptionSource::from_sentence(kind, &source).unwrap().formula;
    AssumptionSource::for_guarantee_with_relied(kind, &source, &one(target), relied).unwrap()
}

/// Render must re-parse to the same tree (source aside) and be a fixpoint.
fn render_round_trips(s: &Sentence) {
    let rendered = s.render();
    let r = one(&rendered);
    assert_eq!(
        (&s.frames, &s.core, &s.exception, &s.purpose),
        (&r.frames, &r.core, &r.exception, &r.purpose),
        "render {rendered:?} must re-parse to the same tree"
    );
    assert_eq!(r.render(), rendered, "render must be a fixpoint for {rendered:?}");
}

// ====================================================================================
// 1. Typed pairing: the full act × EdgeKind matrix
// ====================================================================================

#[test]
fn pairing_matrix_every_act_times_every_kind() {
    use EdgeKind::*;
    let all = [OccurrenceReliance, GuaranteeDischarge, AdmissibilityEnvelope];
    // Every speech-act shape round 5 distinguishes, including the negated
    // recommendation (still a recommendation), `must not` (a prohibition),
    // the never-capability, and the plural/adverbed descriptions.
    let cases: &[(&str, SpeechAct, &[EdgeKind], PairingError)] = &[
        (
            "The client may retry.",
            SpeechAct::Permission,
            &[AdmissibilityEnvelope],
            PairingError::PermissionOnlyEnvelope,
        ),
        (
            "The library should install propagators.",
            SpeechAct::Recommendation,
            &[OccurrenceReliance],
            PairingError::RecommendationOnlyReliance,
        ),
        (
            "The library should not block.",
            SpeechAct::Recommendation,
            &[OccurrenceReliance],
            PairingError::RecommendationOnlyReliance,
        ),
        (
            "The sensor shall send the signal.",
            SpeechAct::Obligation,
            &[GuaranteeDischarge, OccurrenceReliance],
            PairingError::BindingNoEnvelope,
        ),
        (
            "The daemon must not sleep.",
            SpeechAct::Prohibition,
            &[GuaranteeDischarge, OccurrenceReliance],
            PairingError::BindingNoEnvelope,
        ),
        (
            "The buffer is empty.",
            SpeechAct::Description,
            &[OccurrenceReliance],
            PairingError::DescriptionOnlyReliance,
        ),
        (
            "The peers are never silent.",
            SpeechAct::Description,
            &[OccurrenceReliance],
            PairingError::DescriptionOnlyReliance,
        ),
        (
            "The client is able to retry.",
            SpeechAct::Description,
            &[OccurrenceReliance],
            PairingError::DescriptionOnlyReliance,
        ),
        (
            "The client is never able to retry.",
            SpeechAct::Description,
            &[OccurrenceReliance],
            PairingError::DescriptionOnlyReliance,
        ),
    ];
    for (input, act, allowed, denial) in cases {
        let sentence = one(input);
        assert_eq!(speech_act(&sentence), *act, "{input:?}");
        for kind in all {
            let result = AssumptionSource::from_sentence(kind, &sentence);
            if allowed.contains(&kind) {
                let source = result.unwrap_or_else(|e| panic!("{input:?} × {kind:?}: {e}"));
                assert_eq!(source.kind, kind);
                assert_eq!(source.act, *act);
                assert_eq!(source.force, so_lang::semantics::force(&sentence));
            } else {
                assert_eq!(result.unwrap_err(), *denial, "{input:?} × {kind:?}");
            }
        }
    }
    // Definitions are denied under EVERY kind, with the same error.
    let definition = one("A session means a sequence of requests.");
    for kind in all {
        assert_eq!(
            AssumptionSource::from_sentence(kind, &definition).unwrap_err(),
            PairingError::NotBehavioral,
            "definition × {kind:?}"
        );
    }
}

#[test]
fn pairing_error_kinds_and_messages_are_stable() {
    let pins: &[(PairingError, &str, &str)] = &[
        (
            PairingError::PermissionOnlyEnvelope,
            "permission_only_envelope",
            "a permission only widens the admissibility envelope: it never witnesses occurrence and never discharges, so pair it as an admissibility envelope or not at all",
        ),
        (
            PairingError::RecommendationOnlyReliance,
            "recommendation_only_reliance",
            "a recommendation is not binding: it can be relied on as an occurrence, but it can never discharge an assumption and it is no admissibility envelope",
        ),
        (
            PairingError::BindingNoEnvelope,
            "binding_no_envelope",
            "a binding sentence asserts behavior: pair it as a guarantee discharge or an occurrence reliance, never as an admissibility envelope",
        ),
        (
            PairingError::DescriptionOnlyReliance,
            "description_only_reliance",
            "a description states how the system is: it can be relied on as state, but it carries no normative force to discharge an assumption and it is no admissibility envelope",
        ),
        (
            PairingError::NotBehavioral,
            "not_behavioral",
            "a definition establishes vocabulary: it has no behavioral content to serve as an assumption source",
        ),
    ];
    for (error, kind, message) in pins {
        assert_eq!(error.kind(), *kind);
        assert_eq!(error.to_string(), *message);
    }
}

#[test]
fn pairing_source_formulas_take_the_guarantee_shape() {
    // A permission source's formula is its admissibility atom — visibly an
    // envelope, never a behavior atom.
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
    )
    .unwrap();
    assert!(
        matches!(envelope.formula, Formula::Atom { atom: AtomRef::Admissibility { .. } }),
        "a permission source is an admissibility atom, got {:?}",
        envelope.formula
    );
    // A conditional source contributes its own conditional (its guarantee
    // shape), not its bare claim.
    let conditional = one("When the order ships, the sensor shall send the signal.");
    let source =
        AssumptionSource::from_sentence(EdgeKind::OccurrenceReliance, &conditional).unwrap();
    assert_eq!(source.formula, contract_formula(&conditional).unwrap().guarantee);
    assert!(matches!(source.formula, Formula::Or { .. }));
    // A coordinated-subject source neither panics nor loses items.
    let coordinated = one("The pump and the valve shall stop.");
    let source =
        AssumptionSource::from_sentence(EdgeKind::GuaranteeDischarge, &coordinated).unwrap();
    match source.formula {
        Formula::And { items } => assert_eq!(items.len(), 2),
        other => panic!("expected And over per-item atoms, got {other:?}"),
    }
}

#[test]
fn paired_retains_sources_and_repairing_supersedes() {
    let base = contract("The daemon shall respond.");
    assert!(base.sources.is_empty());
    let a = explicit_source(
        EdgeKind::GuaranteeDischarge,
        "The sensor shall send the signal.",
        "The daemon shall respond.",
    );
    let b = explicit_source(
        EdgeKind::OccurrenceReliance,
        "The clock is monotonic.",
        "The daemon shall respond.",
    );
    // One source: the assumption stands alone (no 1-ary And).
    let p1 = base.paired(std::slice::from_ref(&a));
    assert_eq!(p1.assumption, a.formula);
    assert_eq!(p1.sources, vec![a.clone()]);
    assert_eq!(p1.guarantee, base.guarantee, "the guarantee is untouched");
    // Saturation over the paired form is G ∨ ¬A.
    assert_eq!(
        p1.saturated(),
        Formula::Or {
            items: vec![
                base.guarantee.clone(),
                Formula::Not { inner: Box::new(a.formula.clone()) },
            ],
        }
    );
    // Two sources: derived conjunction, sources kept in order.
    let p2 = base.paired(&[a.clone(), b.clone()]);
    assert_eq!(
        p2.assumption,
        Formula::And { items: vec![a.formula.clone(), b.formula.clone()] }
    );
    assert_eq!(p2.sources.len(), 2);
    assert_eq!(p2.sources[0].kind, EdgeKind::GuaranteeDischarge);
    assert_eq!(p2.sources[1].kind, EdgeKind::OccurrenceReliance);
    // Re-pairing REPLACES (supersession doctrine): sources and assumption
    // both switch to the new selection; nothing is conjoined across calls.
    let repaired = p1.paired(std::slice::from_ref(&b));
    assert_eq!(repaired.assumption, b.formula);
    assert_eq!(repaired.sources, vec![b.clone()]);
    // Empty pairing is the identity — the existing sources stay.
    assert_eq!(p1.paired(&[]), p1);
    // The ingest saturation of the unpaired contract is the guarantee itself.
    assert_eq!(base.saturated(), base.guarantee);
}

#[test]
fn pairing_serde_round_trips_and_defaults() {
    let source = AssumptionSource::from_sentence(
        EdgeKind::GuaranteeDischarge,
        &one("The sensor shall send the signal."),
    )
    .unwrap();
    let v = serde_json::to_value(&source).unwrap();
    assert_eq!(v["kind"], "guarantee_discharge");
    assert_eq!(v["act"], "obligation");
    assert_eq!(v["force"], "binding");
    assert!(v["formula"].is_object());
    assert_eq!(serde_json::from_value::<AssumptionSource>(v).unwrap(), source);
    // A permission source: null force, envelope kind.
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
    )
    .unwrap();
    let v = serde_json::to_value(&envelope).unwrap();
    assert_eq!(v["kind"], "admissibility_envelope");
    assert_eq!(v["act"], "permission");
    assert_eq!(v["force"], serde_json::Value::Null);
    // A paired contract keeps its sources through serde.
    let paired = contract("The daemon shall respond.").paired(&[source, envelope]);
    let v = serde_json::to_value(&paired).unwrap();
    assert_eq!(v["sources"].as_array().unwrap().len(), 2);
    assert_eq!(serde_json::from_value::<ContractFormula>(v).unwrap(), paired);
    // Pre-round-5 contracts (no `sources` field) still deserialize, empty.
    let old = serde_json::json!({
        "assumption": { "kind": "top" },
        "guarantee": { "kind": "bottom" },
    });
    let back: ContractFormula = serde_json::from_value(old).unwrap();
    assert!(back.sources.is_empty());
}

// ====================================================================================
// 2. Generic subjects are universal in ALL behavioral kinds
// ====================================================================================

#[test]
fn generic_subjects_are_universal_in_every_behavioral_act() {
    let quantifier = |input: &str| skeleton(&one(input)).unwrap().subject.quantifier;
    // a/an and bare (singular and plural) subjects, across obligation,
    // prohibition, recommendation, description, capability, permission.
    for input in [
        // obligation
        "A request shall be logged.",
        "An event shall be recorded.",
        "Requests shall be logged.",
        // prohibition
        "A request shall not be dropped.",
        "Requests must not be dropped.",
        // recommendation
        "A client should retry.",
        "Clients should retry.",
        // description
        "An error is logged.",
        "Errors are logged.",
        "Data is encrypted.",
        // capability
        "A client is able to retry.",
        "Clients are able to retry.",
        "A client is never able to bypass the audit.",
        // permission (admissible behavior is behavioral too)
        "A client may retry.",
    ] {
        assert_eq!(quantifier(input), Quantifier::Universal, "{input:?}");
    }
    // The trio the round legislated now meets at Universal.
    assert_eq!(quantifier("A request shall be logged."), quantifier("Each request shall be logged."));
    assert_eq!(quantifier("Requests are logged."), quantifier("Each request shall be logged."));
    // Non-generic subject quantifiers are untouched.
    assert_eq!(quantifier("The request shall be logged."), Quantifier::Definite);
    assert_eq!(quantifier("No request is logged."), Quantifier::Negative);
    assert_eq!(
        quantifier("At least 3 pumps shall run."),
        Quantifier::Count { op: so_lang::semantics::CountOp::AtLeast, n: 3 }
    );
}

#[test]
fn generic_normalization_is_a_derived_view_only() {
    // The AST keeps the surface determiner: normalization lives in the
    // skeleton/formula layers, never in the words.
    let s = one("A request shall be logged.");
    match &s.core {
        Core::Deontic { subject: NpGroup::Single(np), .. } => {
            assert_eq!(np.det, Some(Det::A));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
    // Coreference still sees the indefinite introduction (`a request`), so
    // the generic reading did not eat the discourse layer.
    let spec = parse("A request shall be logged. The request is archived.").unwrap();
    let refs = so_lang::semantics::references(&spec);
    assert_eq!(refs.len(), 1);
    assert_eq!(
        refs[0].resolution,
        so_lang::semantics::Resolution::Unique { antecedent_sentence: 0 }
    );
}

#[test]
fn object_and_role_generics_are_untouched() {
    // `shall create a session` is one session per occasion: Existential.
    let sk = skeleton(&one("A daemon shall create a session.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Universal);
    assert_eq!(sk.atoms[0].objects[0].quantifier, Quantifier::Existential);
    // Bare objects stay quantifier-less.
    let sk = skeleton(&one("Daemons shall log requests.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Universal);
    assert_eq!(sk.atoms[0].objects[0].quantifier, Quantifier::None);
    // Role noun phrases keep a/an existential and bare None.
    let sk = skeleton(&one("A daemon shall send the alert to an operator.")).unwrap();
    match &sk.atoms[0].roles[0].value {
        RoleValue::Heads { items, .. } => assert_eq!(items[0].quantifier, Quantifier::Existential),
        other => panic!("expected heads, got {other:?}"),
    }
    let sk = skeleton(&one("A daemon shall send the alert to operators.")).unwrap();
    match &sk.atoms[0].roles[0].value {
        RoleValue::Heads { items, .. } => assert_eq!(items[0].quantifier, Quantifier::None),
        other => panic!("expected heads, got {other:?}"),
    }
    // Definitions are untouched: no skeleton, surface determiner kept.
    let s = one("A session means a sequence of requests.");
    assert!(skeleton(&s).is_none());
    match &s.core {
        Core::Definition { term, .. } => assert_eq!(term.det, Some(Det::A)),
        other => panic!("expected definition, got {other:?}"),
    }
}

#[test]
fn generic_interacts_with_subject_no_and_coordination() {
    // Subject-`no` is untouched by the generic rule: the skeleton INDEX keeps
    // Negative; the formula layer keeps its round-4 normalization (Universal
    // under a Not wrapper).
    let sk = skeleton(&one("No request is logged.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Negative);
    match claim("No request is logged.") {
        Formula::Not { inner } => match *inner {
            Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
                assert_eq!(behavior.subject.quantifier, Quantifier::Universal);
            }
            other => panic!("expected behavior atom, got {other:?}"),
        },
        other => panic!("expected negated atom, got {other:?}"),
    }
    // A generic subject builds a bare (un-negated) Universal atom.
    match claim("A request is logged.") {
        Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
            assert_eq!(behavior.subject.quantifier, Quantifier::Universal);
        }
        other => panic!("expected bare behavior atom, got {other:?}"),
    }
    // Mixed coordination: each item digests its own determiner — generic
    // `a` → Universal, definite `the` → Definite, in one And.
    match claim("A pump and the valve shall stop.") {
        Formula::And { items } => {
            let q = |f: &Formula| match f {
                Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
                    behavior.subject.quantifier
                }
                other => panic!("expected behavior atom, got {other:?}"),
            };
            assert_eq!(q(&items[0]), Quantifier::Universal);
            assert_eq!(q(&items[1]), Quantifier::Definite);
        }
        other => panic!("expected And, got {other:?}"),
    }
    // Mixed generic + `no`: the sibling `no` never leaks onto the generic
    // item; each atom is Universal, negation only on the `no` item.
    match claim("A pump and no valve shall run.") {
        Formula::And { items } => {
            assert!(matches!(items[0], Formula::Atom { .. }), "generic item stays affirmative");
            assert!(matches!(items[1], Formula::Not { .. }), "`no` item carries the Not");
        }
        other => panic!("expected And, got {other:?}"),
    }
}

// ====================================================================================
// 3. The relation engine
// ====================================================================================

#[test]
fn implies_truth_table_over_parsed_sentences() {
    // Reflexive Yes; act/force-blind proposition equality (documented: the
    // proposition is the logical key WITHOUT act and force).
    let a = claim("The pump shall stop.");
    assert_eq!(implies(&a, &a), Ternary::Yes);
    let described = claim("The request is logged.");
    let obliged = claim("The request shall be logged.");
    assert_eq!(implies(&described, &obliged), Ternary::Yes);
    assert_eq!(implies(&obliged, &described), Ternary::Yes);
    // Documented sharp edge, pinned: force is NOT part of the proposition,
    // so a recommendation's claim and an obligation's claim meet at Yes.
    let should = claim("The pump should stop.");
    let shall = claim("The pump shall stop.");
    assert_eq!(implies(&should, &shall), Ternary::Yes);
    // The generic trio (same head) meets as computed equivalence.
    let generic = claim("A request shall be logged.");
    let each = claim("Each request shall be logged.");
    assert_eq!(implies(&generic, &each), Ternary::Yes);
    assert_eq!(implies(&each, &generic), Ternary::Yes);
    // Unrelated claims: Unknown, never No.
    let b = claim("The valve shall open.");
    assert_eq!(implies(&a, &b), Ternary::Unknown);
    assert_eq!(implies(&b, &a), Ternary::Unknown);
}

#[test]
fn deadline_and_duration_orderings_with_decimals() {
    let c = |i: &str| claim(i);
    // Deadline: tighter implies looser; decimals and number words parse.
    assert_eq!(
        implies(
            &c("The daemon shall respond within 2.5 seconds."),
            &c("The daemon shall respond within 10 seconds."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The daemon shall respond within 10 seconds."),
            &c("The daemon shall respond within 2.5 seconds."),
        ),
        Ternary::Unknown,
        "the loose deadline never implies the tight one"
    );
    assert_eq!(
        implies(
            &c("The daemon shall respond within 0.5 seconds."),
            &c("The daemon shall respond within 2.5 seconds."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The daemon shall respond within five seconds."),
            &c("The daemon shall respond within 10 seconds."),
        ),
        Ternary::Yes,
        "number words are numeric"
    );
    // Duration: LONGER covers shorter (legislated direction).
    assert_eq!(
        implies(
            &c("The pump shall run for 10 seconds."),
            &c("The pump shall run for 5 seconds."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The pump shall run for 5 seconds."),
            &c("The pump shall run for 10 seconds."),
        ),
        Ternary::Unknown
    );
    // Deadline vs Duration is a kind mismatch: Unknown.
    assert_eq!(
        implies(
            &c("The pump shall run within 5 seconds."),
            &c("The pump shall run for 10 seconds."),
        ),
        Ternary::Unknown
    );
    // Unit matching is case-insensitive (measures are kept as written, so
    // the propositions differ; the numeric hook still meets).
    assert_eq!(
        implies(
            &c("The daemon shall respond within 5 Seconds."),
            &c("The daemon shall respond within 5 seconds."),
        ),
        Ternary::Yes
    );
}

#[test]
fn same_number_different_unit_is_unknown() {
    let c = |i: &str| claim(i);
    let seconds = c("The daemon shall respond within 5 seconds.");
    let ms = c("The daemon shall respond within 5 ms.");
    assert_eq!(implies(&seconds, &ms), Ternary::Unknown);
    assert_eq!(implies(&ms, &seconds), Ternary::Unknown);
    // A present unit vs a missing one is Unknown territory too.
    let bare = c("The daemon shall respond within 5.");
    assert_eq!(implies(&bare, &seconds), Ternary::Unknown);
    assert_eq!(implies(&seconds, &bare), Ternary::Unknown);
    // No normalization table: `5 seconds` vs `5000 milliseconds` stays
    // Unknown even though they are physically equal.
    let milli = c("The daemon shall respond within 5000 milliseconds.");
    assert_eq!(implies(&seconds, &milli), Ternary::Unknown);
}

#[test]
fn comparison_orderings_with_decimals_and_units() {
    let c = |i: &str| claim(i);
    // Upper bounds refine downward.
    assert_eq!(
        implies(&c("The retry count is at most 2.5."), &c("The retry count is at most 3.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&c("The retry count is at most 3."), &c("The retry count is at most 2.5.")),
        Ternary::Unknown
    );
    assert_eq!(
        implies(&c("The depth is less than 3."), &c("The depth is less than 5.")),
        Ternary::Yes
    );
    // Lower bounds refine upward.
    assert_eq!(
        implies(&c("The replica count is at least 5."), &c("The replica count is at least 3.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&c("The depth is greater than 5."), &c("The depth is greater than 3.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&c("The depth is greater than 3."), &c("The depth is greater than 5.")),
        Ternary::Unknown
    );
    // `equal to` needs numeric equality — spelled differently still meets.
    assert_eq!(
        implies(&c("The count is equal to 5."), &c("The count is equal to 5.0.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&c("The count is equal to 5."), &c("The count is equal to 6.")),
        Ternary::Unknown
    );
    // Round 6 (supersedes the round-5 same-operator-only pin): comparisons
    // are judged as intervals, so cross-operator entailment holds where
    // containment does — `less than 3` (an open upper bound) is contained
    // in `at most 5` (a closed one).
    assert_eq!(
        implies(&c("The count is less than 3."), &c("The count is at most 5.")),
        Ternary::Yes
    );
    // With units: same unit orders, different unit is Unknown.
    assert_eq!(
        implies(&c("The latency is at most 3 seconds."), &c("The latency is at most 5 seconds.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&c("The latency is at most 3 seconds."), &c("The latency is at most 5 ms.")),
        Ternary::Unknown
    );
    // Round 6 (supersedes the round-5 out-of-scope pin): `between` is a
    // closed interval, and [1, 3] ⊆ [1, 5] is containment.
    assert_eq!(
        implies(
            &c("The latency is between 1 and 3 seconds."),
            &c("The latency is between 1 and 5 seconds."),
        ),
        Ternary::Yes
    );
}

#[test]
fn ternary_judgments_are_conservative_never_unjustified() {
    let c = |i: &str| claim(i);
    // Pairs that differ in ways the rules cannot see must ALL be Unknown for
    // implies (both directions) and contradicts — Unknown is never collapsed
    // to No, and Yes needs a structural proof.
    let pairs: &[(&str, &str)] = &[
        // subject differs
        ("The pump shall stop.", "The valve shall stop."),
        // subject modifier differs (restrictor is part of the digest)
        ("The backup daemon shall run.", "The daemon shall run."),
        // singular vs plural head: no lemmatization
        ("Requests shall be logged.", "Each request shall be logged."),
        // manner differs
        ("The pump shall stop.", "The pump shall stop immediately."),
        // object differs alongside an ordered measure: two differences
        (
            "The daemon shall send the alert within 5 seconds.",
            "The daemon shall send the report within 10 seconds.",
        ),
        // same roles in a different surface order (role lists are ordered)
        (
            "The daemon shall send the alert to the operator within 5 seconds.",
            "The daemon shall send the alert within 10 seconds to the operator.",
        ),
        // requirement vs tolerance: behavior and admissibility never compare
        ("The client shall retry.", "The client may retry."),
        // different verbs
        ("The pump shall stop.", "The pump shall halt."),
    ];
    for (x, y) in pairs {
        let a = c(x);
        let b = c(y);
        assert_eq!(implies(&a, &b), Ternary::Unknown, "implies({x:?}, {y:?})");
        assert_eq!(implies(&b, &a), Ternary::Unknown, "implies({y:?}, {x:?})");
        assert_eq!(contradicts(&a, &b), Ternary::Unknown, "contradicts({x:?}, {y:?})");
    }
    // Admissibility atoms DO compare among themselves: the numeric hook
    // works inside the envelope modality.
    assert_eq!(
        implies(
            &c("The client may retry within 5 seconds."),
            &c("The client may retry within 10 seconds."),
        ),
        Ternary::Yes
    );
    // Ternary serializes stably for telemetry.
    assert_eq!(serde_json::to_value(Ternary::Unknown).unwrap(), "unknown");
    assert_eq!(serde_json::to_value(Ternary::Yes).unwrap(), "yes");
}

#[test]
fn prohibition_contradicts_obligation_and_negation_composes() {
    let c = |i: &str| claim(i);
    // The direct shape of a contradiction, across surface spellings.
    let obliged = c("The pump shall stop.");
    let forbidden = c("The pump shall not stop.");
    assert_eq!(contradicts(&obliged, &forbidden), Ternary::Yes);
    assert_eq!(contradicts(&forbidden, &obliged), Ternary::Yes);
    // Generic subject against the explicit universal (round-5 payoff).
    assert_eq!(
        contradicts(&c("A request shall not be logged."), &c("Each request shall be logged.")),
        Ternary::Yes
    );
    // Description `never` against the described state.
    assert_eq!(
        contradicts(&c("The pump is never stopped."), &c("The pump is stopped.")),
        Ternary::Yes
    );
    // A claim never contradicts itself: syntactic equality is a No.
    assert_eq!(contradicts(&obliged, &obliged), Ternary::No);
    // implies over mixed polarity of ONE proposition is a proven No.
    let not_obliged = Formula::Not { inner: Box::new(obliged.clone()) };
    assert_eq!(implies(&obliged, &not_obliged), Ternary::No);
    assert_eq!(implies(&not_obliged, &obliged), Ternary::No);
}

#[test]
fn no_subject_normalized_equivalence_is_computed() {
    let no = claim("No request shall be logged.");
    let each_not = claim("Each request shall not be logged.");
    assert_eq!(implies(&no, &each_not), Ternary::Yes);
    assert_eq!(implies(&each_not, &no), Ternary::Yes);
    // Both contradict the positive universal AND the generic positive.
    let each = claim("Each request shall be logged.");
    let generic = claim("A request shall be logged.");
    assert_eq!(contradicts(&no, &each), Ternary::Yes);
    assert_eq!(contradicts(&no, &generic), Ternary::Yes);
    assert_eq!(contradicts(&each_not, &generic), Ternary::Yes);
    // Conservative honesty: the two equivalent formulas are NOT syntactically
    // equal (anchors differ), so contradicts(no, each_not) is Unknown — not
    // No. Unknown stays the honest answer where only equality would prove No.
    assert_eq!(contradicts(&no, &each_not), Ternary::Unknown);
}

#[test]
fn refines_direction_cannot_be_inverted() {
    // Guarantee strengthening: the tight deadline refines the loose one and
    // NEVER the other way around.
    let tight = contract("When the order ships, the daemon shall respond within 5 seconds.");
    let loose = contract("When the order ships, the daemon shall respond within 10 seconds.");
    assert_eq!(refines(&tight, &loose), Ternary::Yes);
    assert_ne!(refines(&loose, &tight), Ternary::Yes, "direction must not invert");
    assert_eq!(refines(&loose, &tight), Ternary::Unknown);
    // Assumption weakening, on PAIRED (saturated) forms: the contract that
    // assumes LESS (A alone) refines the one that assumes MORE (A ∧ B) —
    // and the inversion is not Yes.
    let base = contract("The daemon shall respond.");
    let a = explicit_source(
        EdgeKind::GuaranteeDischarge,
        "The sensor shall send the signal.",
        "The daemon shall respond.",
    );
    let b = explicit_source(
        EdgeKind::OccurrenceReliance,
        "The clock is monotonic.",
        "The daemon shall respond.",
    );
    let assumes_less = base.paired(std::slice::from_ref(&a));
    let assumes_more = base.paired(&[a.clone(), b.clone()]);
    assert_eq!(refines(&assumes_less, &assumes_more), Ternary::Yes);
    assert_ne!(refines(&assumes_more, &assumes_less), Ternary::Yes);
    assert_eq!(refines(&assumes_more, &assumes_less), Ternary::Unknown);
    // A No is proven where the saturated guarantees are opposite atoms.
    let stop = contract("The pump shall stop.");
    let dont = contract("The pump shall not stop.");
    assert_eq!(refines(&dont, &stop), Ternary::No);
    assert_eq!(refines(&stop, &dont), Ternary::No);
    // Reflexivity: every contract refines itself.
    assert_eq!(refines(&tight, &tight), Ternary::Yes);
    // The comparison flagship end-to-end (description comparisons).
    let concrete = contract("The retry count is at most 3.");
    let abstract_ = contract("The retry count is at most 5.");
    assert_eq!(refines(&concrete, &abstract_), Ternary::Yes);
    assert_eq!(refines(&abstract_, &concrete), Ternary::Unknown);
}

// ====================================================================================
// 4. subject_keys carry modifiers
// ====================================================================================

#[test]
fn subject_keys_with_modifiers_casing_ofchains_coordination_relatives() {
    // Distinctness: the round-5 point.
    assert_ne!(
        subject_keys(&one("The backup daemon shall run.")),
        subject_keys(&one("The daemon shall run."))
    );
    assert_eq!(subject_keys(&one("The backup daemon shall run.")), vec!["backup.daemon"]);
    // Casing is normalized.
    assert_eq!(subject_keys(&one("The BACKUP Daemon shall run.")), vec!["backup.daemon"]);
    // Multiple modifiers keep surface order.
    assert_eq!(
        subject_keys(&one("The primary backup daemon shall run.")),
        vec!["primary.backup.daemon"]
    );
    // Of-chain links contribute modifiers + head, root first.
    assert_eq!(
        subject_keys(&one("The senior owner of the shared backup file shall approve the change.")),
        vec!["senior.owner.shared.backup.file"]
    );
    // Deep chains flatten in chain order.
    assert_eq!(
        subject_keys(&one("The owner of the log of the backup daemon shall rotate the log.")),
        vec!["owner.log.backup.daemon"]
    );
    // Coordination: one key per item, each with its own modifiers.
    assert_eq!(
        subject_keys(&one("The backup pump and the main valve shall stop.")),
        vec!["backup.pump", "main.valve"]
    );
    // Relatives are excluded — both attachments, copular and verbal bodies;
    // a relative's object never leaks into the key.
    assert_eq!(
        subject_keys(&one("The user of the workspace who is active shall confirm the change.")),
        vec!["user.workspace"]
    );
    assert_eq!(
        subject_keys(&one("The user of the workspace that is active shall confirm the change.")),
        vec!["user.workspace"]
    );
    assert_eq!(
        subject_keys(&one("The user who owns the backup file shall confirm the change.")),
        vec!["user"]
    );
    // Descriptions and definitions.
    assert_eq!(subject_keys(&one("The backup daemon is idle.")), vec!["backup.daemon"]);
    assert!(subject_keys(&one("A backup daemon means a standby process.")).is_empty());
}

// ====================================================================================
// 5. Legislated for / with / by
// ====================================================================================

#[test]
fn for_accepts_quantities_including_decimals_and_zero() {
    let duration = |input: &str| {
        let s = one(input);
        render_round_trips(&s);
        match &s.core {
            Core::Deontic { vp, .. } => match &vp.single().unwrap().roles[0] {
                RolePp::Duration(Measure::Quantity { number, unit }) => {
                    (number.clone(), unit.clone())
                }
                other => panic!("expected quantity duration in {input:?}, got {other:?}"),
            },
            other => panic!("expected deontic, got {other:?}"),
        }
    };
    assert_eq!(
        duration("The pump shall run for 5 seconds."),
        ("5".to_string(), Some("seconds".to_string()))
    );
    assert_eq!(
        duration("The pump shall run for 2.5 seconds."),
        ("2.5".to_string(), Some("seconds".to_string()))
    );
    assert_eq!(duration("The pump shall run for zero."), ("zero".to_string(), None));
    assert_eq!(
        duration("The pump shall run for five seconds."),
        ("five".to_string(), Some("seconds".to_string()))
    );
    assert_eq!(duration("The pump shall run for 5."), ("5".to_string(), None));
    // The digest keeps the number as written.
    let sk = skeleton(&one("The pump shall run for 2.5 seconds.")).unwrap();
    assert_eq!(
        sk.atoms[0].roles[0],
        so_lang::semantics::RoleSkeleton {
            kind: RoleKind::Duration,
            value: RoleValue::Measure { number: "2.5".into(), unit: Some("seconds".into()) },
            marker: None,
        }
    );
}

#[test]
fn for_without_a_quantity_is_rejected_with_the_exact_kind() {
    // Round 6 (supersedes the round-5 no-bounded-duration pin): `for at
    // least 5 seconds` now HAS a legislated duration reading —
    // `Measure::Bounded` — so it is no longer in this rejection set (see
    // tests/round6.rs).
    assert_eq!(ParseError::ForRequiresMeasure.kind(), "for_requires_measure");
    for input in [
        "The daemon shall listen for requests.",
        "The daemon shall wait for the grace period.",
        // frame clauses (verbal bodies share the role loop)
        "While the pump runs for the shift, the valve shall stay open.",
        // definiens role phrases share it too
        "A backup means a copy for the archive.",
    ] {
        assert_eq!(parse(input), Err(ParseError::ForRequiresMeasure), "{input:?}");
    }
    // `within` (Deadline) still admits noun-phrase measures — the
    // legislation covers `for` alone.
    let s = one("The daemon shall respond within the grace period.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Deadline(Measure::Np { .. })));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
}

#[test]
fn with_is_rejected_at_role_positions_and_folds_in_plain_nps() {
    assert_eq!(ParseError::WithIsAmbiguous.kind(), "with_is_ambiguous");
    for input in [
        // where a role phrase could start, after an object
        "The daemon shall notify the user with the report.",
        // bare after the verb
        "The daemon shall sign with the key.",
        // at the object boundary inside a det-led VP noun phrase: the
        // reserve applies because a role phrase could start there
        "The daemon shall archive the file with the flag.",
        // verbal frame clause bodies
        "When the daemon signs with the key, the log shall grow.",
        // definiens role positions
        "A backup means a copy with the flag.",
    ] {
        assert_eq!(parse(input), Err(ParseError::WithIsAmbiguous), "{input:?}");
    }
    // The rewrite stays accepted.
    let s = one("The daemon shall sign the report using the key.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Means { marker: MeansMarker::Using, .. }));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    // Round 6 (supersedes the round-5 leave-alone): a PLAIN (subject)
    // noun phrase rejects bare `with` too — folding it into the modifiers
    // pinned the subject head to `flag`, an accepted-but-wrong tree. The
    // ambiguity discipline is now uniform across NP contexts; of-chains
    // and relatives are the supported restriction forms.
    assert_eq!(
        parse("The file with the flag shall be archived."),
        Err(ParseError::WithIsAmbiguous)
    );
    // Description predicates are not role positions: `with` stays an
    // ordinary predicate word (documented plain-context behavior).
    let s = one("The pump is compatible with the valve.");
    match &s.core {
        Core::Description { predicate: Predicate::Words { words }, .. } => {
            assert_eq!(words, &["compatible", "with", "the", "valve"]);
        }
        other => panic!("expected words predicate, got {other:?}"),
    }
}

#[test]
fn by_agent_in_passive_vp_description_and_copular_guard() {
    // Passive verb phrase.
    let s = one("The request shall be logged by the daemon.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "be");
            assert!(
                matches!(&vp.single().unwrap().complement, Some(Predicate::Words { words }) if words == &["logged"])
            );
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Agent(np) if np.heads() == vec!["daemon"]));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
    // Copular description: predicate stays, agent recorded beside it.
    let d = one("The request is logged by the daemon.");
    match &d.core {
        Core::Description { predicate, agent, .. } => {
            assert!(matches!(predicate, Predicate::Words { words } if words == &["logged"]));
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["daemon"]);
        }
        other => panic!("expected description, got {other:?}"),
    }
    render_round_trips(&d);
    // The two digest to ONE atom, with the agent under RoleKind::Agent.
    let obliged = skeleton(&s).unwrap();
    let described = skeleton(&d).unwrap();
    assert_eq!(obliged.atoms[0], described.atoms[0]);
    assert_eq!(obliged.atoms[0].roles.len(), 1);
    assert_eq!(obliged.atoms[0].roles[0].kind, RoleKind::Agent);
    // A different agent is a different atom, and relate keeps them apart.
    let gateway = claim("The request is logged by the gateway.");
    assert_eq!(implies(&claim("The request is logged by the daemon."), &gateway), Ternary::Unknown);
    assert_eq!(
        implies(&claim("The request shall be logged by the daemon."), &claim("The request is logged by the daemon.")),
        Ternary::Yes
    );
    // Copular guard clauses record and digest the agent too.
    let g = one("When the request is submitted by the user, the daemon shall log the request.");
    let item = &g.frames.trigger.as_ref().unwrap().clause.items[0];
    match &item.body {
        ClauseBody::Copular { agent, .. } => {
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["user"]);
        }
        other => panic!("expected copular body, got {other:?}"),
    }
    render_round_trips(&g);
    let sk = skeleton(&g).unwrap();
    let trigger = sk.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.clauses[0].roles[0].kind, RoleKind::Agent);
    match &trigger.clauses[0].roles[0].value {
        RoleValue::Heads { items, .. } => assert_eq!(items[0].head, "user"),
        other => panic!("expected heads, got {other:?}"),
    }
    // The passive site extends through `able to be …` and `in order to be …`.
    let s = one("The client is always able to be paged by the operator.");
    render_round_trips(&s);
    let s = one("The daemon shall stop, in order to be seen by the operator.");
    match &s.purpose {
        Some(Purpose::InOrderTo(vp)) => {
            assert!(matches!(&vp.roles[0], RolePp::Agent(np) if np.heads() == vec!["operator"]));
        }
        other => panic!("expected purpose, got {other:?}"),
    }
}

#[test]
fn by_outside_a_passive_site_is_rejected_with_the_exact_kind() {
    assert_eq!(ParseError::ByOutsidePassive.kind(), "by_outside_passive");
    for input in [
        "The daemon shall notify the user by email.",
        "The daemon shall respond by Friday.",
        // verbal clause bodies are active voice
        "When the daemon runs by the dock, the valve shall open.",
        // definiens role positions
        "A record means a note by the clerk.",
        // active purpose verb phrases
        "The daemon shall stop, in order to comply by Friday.",
        // active vp under a capability
        "The client is able to comply by Friday.",
    ] {
        assert_eq!(parse(input), Err(ParseError::ByOutsidePassive), "{input:?}");
    }
    // DOCUMENTED LEAVE-ALONE: a plain (subject) det-led noun phrase folds
    // `by` into modifiers, mirroring `with`.
    let s = one("The book by the author shall be archived.");
    match &s.core {
        Core::Deontic { subject: NpGroup::Single(np), .. } => {
            assert_eq!(np.head, "author");
            assert_eq!(np.modifiers, vec!["book", "by", "the"]);
        }
        other => panic!("expected single subject, got {other:?}"),
    }
}

/// FINDING (round-5 attack), FIXED by the round-5 fixer: `by` after a `Pp`
/// or noun-phrase-comparison predicate used to be silently swallowed into
/// the predicate's noun phrase (`The tank is below the limit by the
/// sensor.` yielded Pp over head `sensor` with modifiers `["limit", "by",
/// "the"]` and agent `None`), because those inner noun phrases were parsed
/// in plain context where `by` stayed open-class — unlike `Predicate::Words`
/// and quantity comparisons, which already stopped at `by`. Predicate
/// positions now collect noun phrases in a dedicated context (`NpCtx::
/// Predicate`) where `by` is closed, so the agent is recorded uniformly
/// across all predicate shapes, in descriptions and copular guard clauses
/// alike.
#[test]
fn by_after_pp_or_comparison_predicates_must_not_be_swallowed() {
    // Contrast pins (these two DO record the agent today):
    let s = one("The latency is at most 5 seconds by the monitor.");
    match &s.core {
        Core::Description { agent, .. } => {
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["monitor"]);
        }
        other => panic!("expected description, got {other:?}"),
    }
    // The Pp predicate must record its agent the same way.
    let s = one("The tank is below the limit by the sensor.");
    match &s.core {
        Core::Description { predicate: Predicate::Pp { np, .. }, agent, .. } => {
            assert_eq!(np.heads(), vec!["limit"], "the by-phrase must not fold into the Pp");
            assert_eq!(
                agent.as_ref().map(|a| a.heads()),
                Some(vec!["sensor"]),
                "the agent must be recorded after a Pp predicate"
            );
        }
        other => panic!("expected pp description, got {other:?}"),
    }
    // And the noun-phrase comparison measure likewise.
    let s = one("The total is equal to the limit by the auditor.");
    match &s.core {
        Core::Description { predicate: Predicate::Comparison(c), agent, .. } => {
            match &c.value {
                Measure::Np { np } => assert_eq!(np.heads(), vec!["limit"]),
                other => panic!("expected np measure, got {other:?}"),
            }
            assert_eq!(agent.as_ref().map(|a| a.heads()), Some(vec!["auditor"]));
        }
        other => panic!("expected comparison description, got {other:?}"),
    }
    // Copular guard clauses with a Pp predicate swallow it the same way.
    let s = one("When the pump is in the tank by the operator, the valve shall open.");
    let item = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    match &item.body {
        ClauseBody::Copular { predicate: Predicate::Pp { np, .. }, agent, .. } => {
            assert_eq!(np.heads(), vec!["tank"]);
            assert_eq!(agent.as_ref().map(|a| a.heads()), Some(vec!["operator"]));
        }
        other => panic!("expected pp copular body, got {other:?}"),
    }
}

#[test]
fn bare_be_admits_an_agent_without_a_complement() {
    // FINDING (round-5 attack), FIXED by the round-5 fixer: this pin
    // originally recorded that `be` was the passive site even with NO
    // complement, so a locative `be by <np>` read as an agent (`The daemon
    // shall be by the dock.` — Agent `dock`, complement None): a passive
    // agent asserted for a sentence with nothing passive in it. The passive
    // site is now `be <predicate>` exactly as the docs' Agent row says — a
    // bare `be` followed by `by` is rejected like any other active `by`.
    assert_eq!(
        parse("The daemon shall be by the dock."),
        Err(ParseError::ByOutsidePassive)
    );
    // The complemented site is untouched.
    let s = one("The daemon shall be moored by the operator.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "be");
            assert!(vp.single().unwrap().complement.is_some());
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Agent(np) if np.heads() == vec!["operator"]));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
}

// ====================================================================================
// 6. Relative attachment: who → chain root, that → nearest head
// ====================================================================================

#[test]
fn who_attaches_to_the_chain_root_and_that_to_the_nearest() {
    let subject_np = |input: &str| {
        let s = one(input);
        match &s.core {
            Core::Deontic { subject: NpGroup::Single(np), .. } => np.clone(),
            other => panic!("expected single deontic subject, got {other:?}"),
        }
    };
    // who → ROOT.
    let np = subject_np("The user of the workspace who is active shall confirm the change.");
    assert_eq!(np.head, "user");
    assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
    assert!(np.of.as_ref().unwrap().relative.is_none());
    // that → NEAREST.
    let np = subject_np("The user of the workspace that is active shall confirm the change.");
    assert!(np.relative.is_none());
    assert_eq!(np.of.as_ref().unwrap().relative.as_ref().unwrap().marker, RelMarker::That);
    // The rule is deterministic, not animacy-inferring: `who` climbs even
    // when the inner link is the animate one.
    let np = subject_np("The workspace of the user who is active shall be locked.");
    assert_eq!(np.head, "workspace");
    assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
    assert!(np.of.as_ref().unwrap().relative.is_none());
    // Deep chains: `who` climbs to the outermost head, every link clean.
    let np =
        subject_np("The owner of the log of the daemon who is active shall rotate the log.");
    assert_eq!(np.head, "owner");
    assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
    let mid = np.of.as_ref().unwrap();
    assert_eq!(mid.head, "log");
    assert!(mid.relative.is_none());
    let inner = mid.of.as_ref().unwrap();
    assert_eq!(inner.head, "daemon");
    assert!(inner.relative.is_none());
    // No of-chain: `who` stays where it always was.
    let np = subject_np("The user who is active shall confirm the change.");
    assert_eq!(np.head, "user");
    assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
    // Both markers in one chain: `that` inner, `who` outer.
    let np = subject_np(
        "The user of the workspace that is shared who is active shall confirm the change.",
    );
    assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
    assert_eq!(np.of.as_ref().unwrap().relative.as_ref().unwrap().marker, RelMarker::That);
}

#[test]
fn who_attachment_holds_in_object_and_guard_positions() {
    // Object position (verb-phrase context).
    let s = one("The daemon shall notify the owner of the file who is active.");
    match &s.core {
        Core::Deontic { vp, .. } => match vp.single().unwrap().object.as_ref().unwrap() {
            NpGroup::Single(np) => {
                assert_eq!(np.head, "owner");
                assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
                assert!(np.of.as_ref().unwrap().relative.is_none());
            }
            other => panic!("expected single object, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
    // Guard-clause subject position (verbal body behind an of-chain).
    let s = one(
        "When the user of the workspace who is active logs out, the daemon shall lock the workspace.",
    );
    let item = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    match &item.subject {
        NpGroup::Single(np) => {
            assert_eq!(np.head, "user");
            assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
            assert!(np.of.as_ref().unwrap().relative.is_none());
        }
        other => panic!("expected single subject, got {other:?}"),
    }
    assert!(matches!(&item.body, ClauseBody::Verbal { verb, particle: Some(p), .. }
        if verb == "logs" && p == "out"));
    render_round_trips(&s);
}

#[test]
fn relative_attachment_render_round_trips_and_keys_are_unaffected() {
    for input in [
        "The user of the workspace who is active shall confirm the change.",
        "The user of the workspace that is active shall confirm the change.",
        "The user who is active shall confirm the change.",
        "The user of the workspace that is shared who is active shall confirm the change.",
        "The owner of the log of the daemon who is active shall rotate the log.",
        "The daemon shall notify the owner of the file who is active.",
        "The user who owns the backup file shall confirm the change.",
    ] {
        render_round_trips(&one(input));
    }
    // subject_keys are identical across attachments and relative bodies.
    for (a, b) in [
        (
            "The user of the workspace who is active shall confirm the change.",
            "The user of the workspace that is active shall confirm the change.",
        ),
        (
            "The user of the workspace shall confirm the change.",
            "The user of the workspace who is active shall confirm the change.",
        ),
    ] {
        assert_eq!(subject_keys(&one(a)), subject_keys(&one(b)));
    }
}

// ====================================================================================
// 7. `is always/never able to` is capability
// ====================================================================================

#[test]
fn adverb_capability_shapes_polarity_and_round_trips() {
    let capability = |input: &str| match denote(&one(input)) {
        Denotation::Behavior(assertion) => match assertion.claim {
            Claim::Capability { polarity, vp } => (polarity, vp),
            other => panic!("expected capability in {input:?}, got {other:?}"),
        },
        other => panic!("expected behavior in {input:?}, got {other:?}"),
    };
    // AST shape: adverb kept between copula and AbleTo.
    let s = one("The client is always able to retry.");
    match &s.core {
        Core::Description {
            adverb: Some(DescriptionAdverb::Always),
            predicate: Predicate::AbleTo { vp },
            agent: None,
            ..
        } => assert_eq!(vp.verb, "retry"),
        other => panic!("expected always + AbleTo, got {other:?}"),
    }
    // Polarity composition table: adverb `never` XOR subject `no`.
    assert_eq!(capability("The client is able to retry.").0, Polarity::Affirmative);
    assert_eq!(capability("The client is always able to retry.").0, Polarity::Affirmative);
    assert_eq!(capability("The client is never able to retry.").0, Polarity::Negative);
    assert_eq!(capability("No client is able to retry.").0, Polarity::Negative);
    assert_eq!(capability("No client is always able to retry.").0, Polarity::Negative);
    assert_eq!(capability("No client is never able to retry.").0, Polarity::Affirmative);
    // Plural copula takes the adverb too.
    assert_eq!(capability("Clients are never able to retry.").0, Polarity::Negative);
    // The vp survives with its roles.
    let (_, vp) = capability("The client is always able to retry within 5 seconds.");
    assert_eq!(vp.verb, "retry");
    assert!(matches!(&vp.roles[0], RolePp::Deadline(_)));
    // Render round-trips for every shape.
    for input in [
        "The client is always able to retry.",
        "The client is never able to retry.",
        "Clients are never able to retry.",
        "No client is never able to retry.",
        "The client is always able to retry within 5 seconds.",
    ] {
        render_round_trips(&one(input));
    }
    // Skeleton: still a Description act with no force; polarity mirrors the
    // composed claim; the atom is the capability's verb kernel.
    let sk = skeleton(&one("The client is never able to retry.")).unwrap();
    assert_eq!(sk.act, SpeechAct::Description);
    assert_eq!(sk.force, None);
    assert_eq!(sk.polarity, Polarity::Negative);
    assert_eq!(sk.atoms[0].words, vec!["retry"]);
    // Generic subject composes with the capability reading.
    let sk = skeleton(&one("A client is never able to retry.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Universal);
    assert_eq!(sk.polarity, Polarity::Negative);
}

#[test]
fn capability_polarity_feeds_the_relation_engine() {
    // Same (definite) subject: `never able to` denies exactly what `able
    // to` asserts.
    let can = claim("The client is able to retry.");
    let never = claim("The client is never able to retry.");
    assert_eq!(contradicts(&can, &never), Ternary::Yes);
    assert_eq!(contradicts(&never, &can), Ternary::Yes);
    // Generic + `no`: both normalize to Universal `client`, so the denial
    // meets the generic capability head-on.
    let generic_can = claim("A client is able to retry.");
    let no_subject = claim("No client is able to retry.");
    assert_eq!(contradicts(&generic_can, &no_subject), Ternary::Yes);
    // `never able to` (Universal via `no`) and the same denial spelled with
    // `no` are mutually implying when the subjects meet at Universal.
    let never_generic = claim("A client is never able to retry.");
    assert_eq!(implies(&never_generic, &no_subject), Ternary::Yes);
    assert_eq!(implies(&no_subject, &never_generic), Ternary::Yes);
    // But a DEFINITE subject never bridges to the universal denial: the
    // engine does not instantiate quantifiers — conservative Unknown.
    assert_eq!(implies(&never, &no_subject), Ternary::Unknown);
    assert_eq!(contradicts(&can, &no_subject), Ternary::Unknown);
}

// ====================================================================================
// 8. Totality: seeded fuzz over the new constructs
// ====================================================================================

/// xorshift64* — deterministic, seedable, no dependencies.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn pick<'a>(&mut self, pool: &[&'a str]) -> &'a str {
        pool[(self.next() % pool.len() as u64) as usize]
    }
}

fn total(input: &str) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let _ = parse(input);
    }));
    assert!(outcome.is_ok(), "parse panicked on {input:?}");
}

#[test]
fn seeded_fuzz_over_round5_constructs_never_panics() {
    // The pool leans hard on the round-5 material: by/with/for, who/that
    // over of-chains, able-to with adverbs, generic subjects, measures with
    // decimals, pairing-relevant modals.
    const POOL: &[&str] = &[
        "the", "a", "an", "no", "each", "every", "at", "least", "most", "exactly", "request",
        "requests", "daemon", "backup", "user", "workspace", "owner", "file", "of", "who",
        "that", "is", "are", "was", "able", "to", "always", "never", "shall", "should", "may",
        "must", "not", "be", "logged", "by", "with", "for", "within", "5", "2.5", "0.5",
        "zero", "five", "seconds", "ms", "and", "or", "both", "either", "retry", "stop",
        "runs", "out", "when", "while", "where", "if", "unless", "so", "in", "order", "means",
        "between", "greater", "than", "equal", "until", "before", "after", "per", "using",
        ",", ".", "`by`", "`for`", "`who`",
    ];
    let mut rng = Rng(0x5EED_0005_D00D_F00D);
    for _ in 0..600 {
        let len = 1 + (rng.next() % 14) as usize;
        let words: Vec<&str> = (0..len).map(|_| rng.pick(POOL)).collect();
        let mut input = words.join(" ");
        if rng.next().is_multiple_of(2) {
            input.push('.');
        }
        total(&input);
    }
    // Structured mutations: drop one token from valid round-5 sentences.
    let seeds = [
        "The user of the workspace who is active shall confirm the change.",
        "The request shall be logged by the daemon within 2.5 seconds.",
        "The client is never able to retry for 5 seconds.",
        "When the request is submitted by the user, a daemon shall log the request.",
        "No client is always able to be paged by the operator.",
        "The pump shall run for five seconds, unless the override is active.",
    ];
    for seed in seeds {
        let tokens: Vec<&str> = seed.split_whitespace().collect();
        for skip in 0..tokens.len() {
            let mutant: Vec<&str> = tokens
                .iter()
                .enumerate()
                .filter_map(|(i, w)| (i != skip).then_some(*w))
                .collect();
            total(&mutant.join(" "));
        }
        // And every adjacent transposition.
        for i in 0..tokens.len() - 1 {
            let mut t = tokens.clone();
            t.swap(i, i + 1);
            total(&t.join(" "));
        }
    }
}
