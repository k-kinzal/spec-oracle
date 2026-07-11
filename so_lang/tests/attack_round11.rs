//! Adversarial conformance attack on the round-11 changes: the fail-closed
//! verb-boundary frontier, verbal-object guard digests, the explicit-relied
//! contract-forming gate, the refuted-assumption verification guard, the
//! envelope branch calculus, and proposal-only normalization candidates.
//!
//! Passing tests are permanent pins. The round-11 review findings that
//! were pinned here as `#[ignore]`d failing expectations (pre-verbal
//! `ly`, trailing particle/number at 3+ runs, the np-first re-read of a
//! nested content ambiguity, negated-passive candidates) are FIXED and
//! their tests now run un-ignored; each carries its history in its doc
//! comment.

use so_lang::ast::ClauseBody;
use so_lang::formula::{
    claim_formula, contract_formula, AssumptionSource, ContractFormula, EdgeKind, Formula,
    SourceIssueReason,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{assumption_satisfiable, envelope_compatible, refines, Ternary};
use so_lang::semantics::{
    normalization_candidates, skeleton, ClauseSkeleton, NormalizationKind, Quantifier,
};

fn one(input: &str) -> so_lang::ast::Sentence {
    parse(input).unwrap().sentences.remove(0)
}

fn explicit_source(
    kind: EdgeKind,
    source: &so_lang::ast::Sentence,
    target: &so_lang::ast::Sentence,
) -> AssumptionSource {
    let default = AssumptionSource::for_guarantee(kind, source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(kind, source, target, default.formula.clone())
        .unwrap()
}

/// A paired contract whose FORMED assumption is refuted: two explicit,
/// proven reliances over provably disjoint intervals of one subject.
fn refuted_contract() -> ContractFormula {
    let target = one("The daemon shall flush the buffer.");
    let lo = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at most 3."),
        &target,
    );
    let hi = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at least 5."),
        &target,
    );
    contract_formula(&target).unwrap().paired(&[lo, hi])
}

// =====================================================================
// Change 1 — the fail-closed ambiguity frontier
// =====================================================================

/// The frontier, enumerated exactly. Efficient-subject side: a det-led
/// clause whose run after the minimal subject is ONE word parses with the
/// final word as the verb; TWO or more bare words reject. Bare-subject
/// side: a two-word clause (subject + verb) parses; three or more bare
/// words reject. Count determiners (multi-token) shift the minimal
/// subject, not the rule.
#[test]
fn frontier_is_exactly_two_or_more_after_the_minimal_subject() {
    // Accepted: run of one after the det-led minimal subject.
    for (text, verb) in [
        (
            "When a session expires, the system shall close the session.",
            "expires",
        ),
        ("When the pump runs, the fan shall run.", "runs"),
        // A count determiner is part of the minimal subject.
        ("When at least 3 pumps run, the fan shall run.", "run"),
        ("When exactly 2 pumps run, the fan shall run.", "run"),
        // Bare subject + verb: the two-word clause.
        ("When clients send, the fan shall run.", "send"),
        // Post-verbal manner strips BEFORE the frontier is measured.
        ("When the client sends quickly, the fan shall run.", "sends"),
    ] {
        let s = one(text);
        let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
        assert!(
            matches!(&clause.body, ClauseBody::Verbal { verb: v, .. } if v == verb),
            "{text}"
        );
    }
    // Rejected: runs of two or more bare words after the minimal subject.
    for text in [
        // Det-led, run of two (the round-10 flagship).
        "When the client sends telemetry, the fan shall run.",
        // Det-led, run of three (the round-10 scramble shape).
        "When the backup daemon sends telemetry, the fan shall run.",
        // Det-led, run of four.
        "When the old backup daemon sends telemetry, the fan shall run.",
        // Bare subject, run of two (three bare words).
        "When clients send telemetry, the fan shall run.",
        // Bare subject, run of three.
        "When backup clients send telemetry, the fan shall run.",
        // Count-determiner-led, run of two after the counted head.
        "When at least 3 clients send telemetry, the fan shall run.",
        // The round-3 o03 modifier-heavy shape.
        "When the temperature sensor fails, the pump shall stop.",
        // Trailing manner strips and the residue is STILL ambiguous.
        "When the client sends telemetry quickly, the fan shall run.",
        "When the client sends telemetry quickly promptly, the fan shall run.",
    ] {
        assert_eq!(
            parse(text),
            Err(ParseError::AmbiguousVerbBoundary),
            "{text}"
        );
    }
}

/// Every clause site fails closed, not just `When`: frames, exceptions,
/// clausal roles, content complements, and the definiens content clause.
#[test]
fn frontier_rejects_at_every_clause_site() {
    for text in [
        "When the client sends telemetry, the fan shall run.",
        "While the client sends telemetry, the fan shall run.",
        "Where the client sends telemetry, the fan shall run.",
        "If the client sends telemetry, then the fan shall run.",
        "The pump shall stop, unless the client sends telemetry.",
        "The pump shall stop after the client sends telemetry.",
        "The pump shall stop before the client sends telemetry.",
        "The pump shall run until the client sends telemetry.",
        // Content complement of a response verb phrase.
        "The monitor shall ensure that the client sends telemetry.",
        // Definiens content clause.
        "An upload means that the client sends telemetry.",
    ] {
        assert_eq!(
            parse(text),
            Err(ParseError::AmbiguousVerbBoundary),
            "{text}"
        );
    }
}

/// Shapes with a provable boundary are untouched: structured (np-first)
/// subjects, role/locative boundaries, determiner-led objects, particle
/// and number finals at the two-word run, non-verb-capable run openers,
/// and verbal relative bodies (whose verb position is fixed by `that`).
#[test]
fn boundaried_shapes_are_unaffected() {
    for (text, verb) in [
        // Determiner on the object (the first rewrite).
        (
            "When the client sends the telemetry, the fan shall run.",
            "sends",
        ),
        // Of-chain subject (the second rewrite).
        (
            "When the sensor of the temperature fails, the pump shall stop.",
            "fails",
        ),
        // Role boundary (the third rewrite).
        (
            "When the temperature sensor fails at the depot, the pump shall stop.",
            "fails",
        ),
        // Np-first structured subject with a bare object.
        (
            "When the owner of the file sends telemetry, the fan shall run.",
            "sends",
        ),
        // Relative-structured subject, particle final.
        (
            "When the user who is authenticated logs out, the session shall end.",
            "logs",
        ),
        // Particle final at the two-word run.
        ("When the user logs out, the session shall end.", "logs"),
        // Bare-number final at the two-word run.
        (
            "When the counter reaches zero, the system shall reset.",
            "reaches",
        ),
        // A particle word never opens an SVO run.
        ("When the power up fails, the fan shall run.", "fails"),
        // A reserved word never opens an SVO run (`of` is never a verb).
        ("When the owner of files logs, the fan shall run.", "logs"),
        // `that` is a boundary: content verb found immediately before it.
        (
            "When the monitor confirms that the queue holds the message, the fan shall run.",
            "confirms",
        ),
    ] {
        let s = one(text);
        let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
        assert!(
            matches!(&clause.body, ClauseBody::Verbal { verb: v, .. } if v == verb),
            "{text}"
        );
    }
    // A verbal RELATIVE body has its verb fixed right after `that` — a bare
    // object there is not ambiguous and stays accepted.
    let s = one("Each client that sends telemetry shall register.");
    match &s.core {
        so_lang::ast::Core::Deontic { subject, .. } => {
            let np = match subject {
                so_lang::ast::NpGroup::Single(np) => np,
                _ => panic!("single subject"),
            };
            let rel = np.relative.as_ref().expect("relative");
            assert!(matches!(
                &rel.body,
                so_lang::ast::RelativeBody::Verbal { verb, .. } if verb == "sends"
            ));
        }
        _ => panic!("deontic"),
    }
}

/// The error is one identity: stable kind, and a message that names BOTH
/// readings and ALL THREE legislated rewrites.
#[test]
fn ambiguity_error_identity_and_rewrites() {
    let err = parse("When the client sends telemetry, the fan shall run.").unwrap_err();
    assert_eq!(err, ParseError::AmbiguousVerbBoundary);
    assert_eq!(err.kind(), "ambiguous_verb_boundary");
    let message = err.to_string();
    // Both readings, named.
    assert!(message.contains("subject-verb-object"), "{message}");
    assert!(message.contains("verb-last"), "{message}");
    // Rewrite 1: a determiner on the object.
    assert!(message.contains("determiner on the object"), "{message}");
    assert!(message.contains("sends the telemetry"), "{message}");
    // Rewrite 2: of-chain or relative for a long subject.
    assert!(
        message.contains("of-chain or a relative clause"),
        "{message}"
    );
    // Rewrite 3: a role boundary.
    assert!(message.contains("role boundary"), "{message}");
}

/// Class membership is decided by SHAPE: the run rejects even when one of
/// the two readings would not parse on its own (`both` cannot be an
/// object noun phrase, yet the shape still fails closed).
#[test]
fn class_membership_is_shape_not_parse_attempts() {
    assert_eq!(
        parse("When the client sends both, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
}

/// FIXED (was FINDING 5, accepted-known-wrong tree, the worst of the
/// four): a CONTENT COMPLEMENT inside a guard clause whose nested clause
/// is ambiguous now REJECTS instead of being silently re-read. The
/// boundary reading (`confirms | that …`) propagates
/// [`ParseError::AmbiguousVerbBoundary`] from the nested clause, and the
/// rejection is FINAL: the np-first fallback must not re-attach the
/// content `that`-clause as an object-gap relative of a longer subject
/// (`the monitor confirms that the client sends` with clause verb
/// `telemetry`). The nested ambiguity condemns the sentence only when
/// the boundary split's own subject region parses — `the request that
/// the gateway forwards fails` still reads as the object-gap relative,
/// because its boundary split's subject is the bare determiner `the`.
#[test]
fn nested_content_ambiguity_must_not_be_reread_as_object_gap_relative() {
    assert_eq!(
        parse("When the monitor confirms that the client sends telemetry, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    assert_eq!(
        parse("While the monitor confirms that the client sends telemetry, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
}

/// FIXED (was FINDING 1, accepted-known-wrong tree): a pre-verbal `ly`
/// word no longer defeats the frontier. `svo_verb_at` SKIPS the manner
/// prefix after the minimal subject before measuring the run — `quickly`
/// is never the verb itself, but it does not disambiguate the split
/// either, so `the client quickly sends telemetry` fails closed exactly
/// like its manner-less twin.
#[test]
fn ly_before_the_verb_must_not_reopen_the_frontier() {
    assert_eq!(
        parse("When the client quickly sends telemetry, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
}

/// FIXED (was FINDING 2, accepted-known-wrong tree): a trailing PARTICLE
/// no longer reopens the frontier for runs of three or more. Popping the
/// final particle now re-measures the run before it: `the user logs out`
/// keeps its round-3 reading (the popped run is one word), while `the
/// client sends telemetry out` fails closed exactly like its
/// particle-less twin.
#[test]
fn particle_final_must_not_reopen_the_frontier_at_three_or_more() {
    assert_eq!(
        parse("When the client sends telemetry out, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
}

/// FIXED (was FINDING 3, accepted-known-wrong tree): a trailing BARE
/// NUMBER no longer defeats the frontier — same pop-and-re-measure as
/// the particle case. `the counter reaches zero` keeps its round-4
/// reading; `the counter reaches stage zero` fails closed.
#[test]
fn number_final_must_not_reopen_the_frontier_at_three_or_more() {
    assert_eq!(
        parse("When the counter reaches stage zero, the system shall reset."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
}

// =====================================================================
// Change 2 — guard object digests
// =====================================================================

/// The INDEX now separates verbal guard objects at every digest site:
/// trigger clauses, exceptions, and content complements. Coordinated
/// object items each get a digest; the group conjunction is legislated
/// OUT of the digest (and/or twins share it — anchors separate them).
#[test]
fn object_digests_at_every_guard_site() {
    // Trigger: `no message` vs `the message` split the skeleton.
    let no = skeleton(&one(
        "When the queue holds no message, the daemon shall idle.",
    ))
    .unwrap();
    let the = skeleton(&one(
        "When the queue holds the message, the daemon shall idle.",
    ))
    .unwrap();
    assert_ne!(no.guards, the.guards);
    let clause = &no.guards.trigger.as_ref().unwrap().clauses[0];
    assert_eq!(clause.words, vec!["holds"]);
    assert_eq!(clause.objects.len(), 1);
    assert_eq!(clause.objects[0].quantifier, Quantifier::Negative);
    assert_eq!(clause.objects[0].head, "message");
    // Exception: same pair, same split.
    let no = skeleton(&one(
        "The daemon shall idle, unless the queue holds no message.",
    ))
    .unwrap();
    let the = skeleton(&one(
        "The daemon shall idle, unless the queue holds the message.",
    ))
    .unwrap();
    let no_x = no.exception.as_ref().unwrap();
    let the_x = the.exception.as_ref().unwrap();
    assert_ne!(no_x, the_x);
    assert_eq!(no_x.objects[0].quantifier, Quantifier::Negative);
    assert_eq!(the_x.objects[0].quantifier, Quantifier::Definite);
    // Content complement inside a guard clause.
    let no = skeleton(&one(
        "When the monitor confirms that the queue holds no message, the daemon shall idle.",
    ))
    .unwrap();
    let the = skeleton(&one(
        "When the monitor confirms that the queue holds the message, the daemon shall idle.",
    ))
    .unwrap();
    assert_ne!(no.guards, the.guards);
    let content = no.guards.trigger.as_ref().unwrap().clauses[0]
        .content
        .as_ref()
        .expect("content");
    assert_eq!(content.clause.objects.len(), 1);
    assert_eq!(content.clause.objects[0].quantifier, Quantifier::Negative);
    // Coordinated objects: one digest per item, in surface order …
    let and = skeleton(&one(
        "When the queue holds the message and the receipt, the daemon shall idle.",
    ))
    .unwrap();
    let clause = &and.guards.trigger.as_ref().unwrap().clauses[0];
    assert_eq!(clause.objects.len(), 2);
    assert_eq!(clause.objects[0].head, "message");
    assert_eq!(clause.objects[1].head, "receipt");
    // … and the group conjunction is NOT carried (LEGISLATED, round 11):
    // the and-guard and its or-twin share the digest; anchors separate.
    let or = skeleton(&one(
        "When the queue holds the message or the receipt, the daemon shall idle.",
    ))
    .unwrap();
    assert_eq!(
        and.guards.trigger.as_ref().unwrap().clauses,
        or.guards.trigger.as_ref().unwrap().clauses
    );
}

/// Plain copular guard bodies stay object-free — round 11 touched verbal
/// bodies only. UPDATED (round 12, change 6 — supersedes the round-11
/// capability leg): CAPABILITY bodies now digest their verb phrase's
/// object group too, so the round-11 "stays out" pin is retired for them
/// (the anchor kept fidelity all along; the index now agrees).
#[test]
fn copular_and_capability_guards_unchanged() {
    let cop = skeleton(&one("While the pump is active, the fan shall run.")).unwrap();
    assert!(cop.guards.states[0].objects.is_empty());
    // A comparison predicate keeps its structured digest and no objects.
    let cmp = skeleton(&one("While the depth is at most 3, the fan shall run.")).unwrap();
    assert!(cmp.guards.states[0].objects.is_empty());
    assert!(cmp.guards.states[0].comparison.is_some());
    // A capability clause body carries its verb phrase's object digests
    // (round 12, change 6).
    let cap = skeleton(&one(
        "While the daemon is able to flush the queue, the fan shall run.",
    ))
    .unwrap();
    assert_eq!(cap.guards.states[0].objects.len(), 1);
    assert_eq!(cap.guards.states[0].objects[0].head, "queue");
}

/// Serde: `objects` rides on the wire when present, is skipped when
/// empty, and a pre-round-11 digest without the field loads as empty.
#[test]
fn clause_skeleton_objects_serde() {
    let k = skeleton(&one(
        "When the queue holds no message, the daemon shall idle.",
    ))
    .unwrap();
    let clause = &k.guards.trigger.as_ref().unwrap().clauses[0];
    let json = serde_json::to_value(clause).unwrap();
    assert!(json.get("objects").is_some());
    let back: ClauseSkeleton = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(&back, clause);
    // Legacy digest: no `objects` field loads as empty.
    let mut legacy = json;
    legacy.as_object_mut().unwrap().remove("objects");
    let back: ClauseSkeleton = serde_json::from_value(legacy).unwrap();
    assert!(back.objects.is_empty());
    // Empty objects never serialize.
    let cop = skeleton(&one("While the pump is active, the fan shall run.")).unwrap();
    let json = serde_json::to_value(&cop.guards.states[0]).unwrap();
    assert!(json.get("objects").is_none());
}

// =====================================================================
// Change 3 — the explicit-relied gate
// =====================================================================

/// Neither default constructor can form a contract, however proven its
/// (self-entailed) reliance is; only the explicit entry point flips the
/// gate; an explicit-but-unproven reliance still does not form.
#[test]
fn default_constructors_never_form_even_when_proven() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    for default in [
        AssumptionSource::from_sentence(EdgeKind::OccurrenceReliance, &source).unwrap(),
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap(),
    ] {
        assert!(default.proven, "the default reliance is self-entailment");
        assert!(!default.explicit_relied);
        assert!(!default.contract_forming());
        let paired = contract_formula(&target)
            .unwrap()
            .paired(std::slice::from_ref(&default));
        assert_eq!(
            paired.assumption,
            Formula::Top,
            "a candidate never relieves the guarantee"
        );
        assert_eq!(paired.sources.len(), 1, "but stays visible as evidence");
    }
    // The explicit path forms.
    let explicit = explicit_source(EdgeKind::OccurrenceReliance, &source, &target);
    assert!(explicit.explicit_relied && explicit.proven && explicit.contract_forming());
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&explicit));
    assert_eq!(paired.assumption, explicit.relied);
    // Explicit but UNPROVEN (entailment Unknown): selected, not forming.
    let unproven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&one("The queue is empty.")).unwrap(),
    )
    .unwrap();
    assert!(unproven.explicit_relied);
    assert!(!unproven.proven);
    assert!(!unproven.contract_forming());
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&unproven));
    assert_eq!(paired.assumption, Formula::Top);
}

/// Serde: the flag rides on the wire in BOTH states (no skip — an
/// explicit edge must not degrade on rewrite), round-trips, and a
/// pre-round-11 source without the field loads as `false` — the
/// conservative direction.
#[test]
fn explicit_relied_serde() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let json = serde_json::to_value(&default).unwrap();
    assert_eq!(
        json["explicit_relied"],
        serde_json::json!(false),
        "false still serializes"
    );
    let explicit = explicit_source(EdgeKind::OccurrenceReliance, &source, &target);
    let json = serde_json::to_value(&explicit).unwrap();
    assert_eq!(json["explicit_relied"], serde_json::json!(true));
    let back: AssumptionSource = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(back, explicit);
    // Legacy JSON: the field absent loads as a candidate.
    let mut legacy = json;
    legacy.as_object_mut().unwrap().remove("explicit_relied");
    let back: AssumptionSource = serde_json::from_value(legacy).unwrap();
    assert!(!back.explicit_relied);
    assert!(
        !back.contract_forming(),
        "an old proven edge must not silently keep the power"
    );
}

/// The `well_formed()` truth table. (The spec offered `verification()` as
/// an alternative name; the shipped API folds both into `well_formed()` —
/// one call, all four fields.)
#[test]
fn well_formed_truth_table() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let bare = contract_formula(&target).unwrap();
    // Row 1: no sources — vacuously explicit and proven, nothing refuted.
    let w = bare.well_formed();
    assert!(w.all_contract_forming_explicit && w.all_proven);
    assert_eq!(w.assumption_satisfiability, Ternary::Unknown);
    assert_eq!(w.envelope_compatibility, Ternary::Unknown);
    // Row 2: a default-relied source — proven, not explicit.
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let w = bare.paired(std::slice::from_ref(&default)).well_formed();
    assert!(!w.all_contract_forming_explicit);
    assert!(w.all_proven);
    // Row 3: an explicit-but-unproven source — explicit, not proven.
    let unproven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&one("The queue is empty.")).unwrap(),
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&unproven)).well_formed();
    assert!(w.all_contract_forming_explicit);
    assert!(!w.all_proven);
    // Row 4: an envelope source never counts against the booleans, and its
    // own judgment shows up in `envelope_compatibility`.
    let prohibition = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &prohibition,
    )
    .unwrap();
    let w = contract_formula(&prohibition)
        .unwrap()
        .paired(std::slice::from_ref(&envelope))
        .well_formed();
    assert!(
        w.all_contract_forming_explicit && w.all_proven,
        "envelopes are out of scope"
    );
    assert_eq!(
        w.envelope_compatibility,
        Ternary::No,
        "the violation is re-exposed"
    );
    assert_eq!(w.assumption_satisfiability, Ternary::Unknown);
    // Row 5: a refuted pairing reports it.
    let w = refuted_contract().well_formed();
    assert!(w.all_contract_forming_explicit && w.all_proven);
    assert_eq!(w.assumption_satisfiability, Ternary::No);
    // Row 6 (data-only doctrine; UPDATED round 12, change 2 — the
    // round-11 pin showed the two booleans staying true while nothing
    // formed, and that display hazard is exactly what the aggregate now
    // catches): explicit + proven + SHARED KEYS — the narrow booleans
    // stay true (they report explicitness/provenness, not the gate), the
    // source does not form, A stays Top, and the AGGREGATE reports it,
    // with the shared-keys reason itemized.
    let shared = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The daemon is ready."),
        &target,
    );
    assert!(
        !shared.contract_forming(),
        "shared responsible keys ride as candidates"
    );
    let paired = bare.paired(std::slice::from_ref(&shared));
    assert_eq!(paired.assumption, Formula::Top);
    let w = paired.well_formed();
    assert!(w.all_contract_forming_explicit && w.all_proven);
    assert!(
        !w.all_sources_contract_forming,
        "the aggregate catches the shared-keys case"
    );
    assert_eq!(w.source_issues.len(), 1);
    assert_eq!(w.source_issues[0].index, 0);
    assert_eq!(
        w.source_issues[0].reasons,
        vec![SourceIssueReason::SharedSubjectKeys]
    );
}

// =====================================================================
// Change 4 — the refuted-assumption verification guard
// =====================================================================

/// A refuted formed assumption makes `refines` vacuous: Unknown in both
/// positions, self-refinement included; a hand-set Bottom assumption
/// guards the same way.
#[test]
fn refines_is_unknown_over_a_refuted_assumption() {
    let refuted = refuted_contract();
    assert_eq!(assumption_satisfiable(&refuted), Ternary::No);
    let other = contract_formula(&one("The daemon shall flush the buffer.")).unwrap();
    assert_eq!(refines(&refuted, &other), Ternary::Unknown);
    assert_eq!(refines(&other, &refuted), Ternary::Unknown);
    assert_eq!(refines(&refuted, &refuted), Ternary::Unknown);
    // Hand-set Bottom (no sources): judged over the assumption formula.
    let mut bottom = contract_formula(&one("The daemon shall flush the buffer.")).unwrap();
    bottom.assumption = Formula::Bottom;
    assert_eq!(assumption_satisfiable(&bottom), Ternary::No);
    assert_eq!(refines(&bottom, &other), Ternary::Unknown);
    assert_eq!(refines(&other, &bottom), Ternary::Unknown);
}

/// CANDIDATE sources cannot make a contract vacuous: the same
/// contradictory interval pair, paired through the DEFAULT constructor,
/// never enters A — the contract stays healthy and self-refines.
#[test]
fn candidate_sources_never_trip_the_guard() {
    let target = one("The daemon shall flush the buffer.");
    let lo = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at most 3."),
        &target,
    )
    .unwrap();
    let hi = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at least 5."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[lo, hi]);
    assert_eq!(paired.assumption, Formula::Top, "candidates never form A");
    assert_eq!(assumption_satisfiable(&paired), Ternary::Unknown);
    assert_eq!(refines(&paired, &paired), Ternary::Yes);
}

/// The healthy path is unchanged: interval tightening, prohibition
/// against obligation, and self-refinement of a WELL-paired contract.
#[test]
fn refines_healthy_path_unchanged() {
    let tight = contract_formula(&one(
        "When the order ships, the daemon shall respond within 5 seconds.",
    ))
    .unwrap();
    let loose = contract_formula(&one(
        "When the order ships, the daemon shall respond within 10 seconds.",
    ))
    .unwrap();
    assert_eq!(refines(&tight, &loose), Ternary::Yes);
    assert_eq!(refines(&loose, &tight), Ternary::Unknown);
    let stop = contract_formula(&one("The pump shall stop.")).unwrap();
    let dont = contract_formula(&one("The pump shall not stop.")).unwrap();
    assert_eq!(refines(&dont, &stop), Ternary::No);
    // A healthily paired contract still self-refines at Yes.
    let target = one("The daemon shall flush the buffer.");
    let ok = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The scheduler is ready."),
        &target,
    );
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&ok));
    assert_eq!(assumption_satisfiable(&paired), Ternary::Unknown);
    assert_eq!(refines(&paired, &paired), Ternary::Yes);
}

// =====================================================================
// Change 5 — envelope calculus
// =====================================================================

/// (a) A matching obligation is compatible evidence, never a verdict:
/// Unknown, pinned — bare and guarded alike.
#[test]
fn matching_obligation_never_refutes_and_never_certifies() {
    let target = one("The client shall retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // Guarded pair with witnessing guards: still Unknown.
    let target = one("When the order ships, the client shall retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("When the order ships, the client may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

/// (b) The branch rule over a THREE-way alternative: prohibiting one or
/// two branches routes around (Unknown); prohibiting all three revokes
/// the permission entirely (No).
#[test]
fn branch_rule_partial_vs_total_refutation() {
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may either retry or escalate the request or idle."),
        &target,
    )
    .unwrap();
    let base = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    // One of three branches prohibited: Unknown.
    assert_eq!(envelope_compatible(&base), Ternary::Unknown);
    // Two of three: still Unknown.
    let no_escalate = claim_formula(&one("The client shall not escalate the request.")).unwrap();
    let mut two = base.clone();
    two.guarantee = Formula::And {
        items: vec![base.guarantee.clone(), no_escalate.clone()],
    };
    assert_eq!(envelope_compatible(&two), Ternary::Unknown);
    // All three: the permission is entirely revoked — No.
    let no_idle = claim_formula(&one("The client shall not idle.")).unwrap();
    let mut all = base.clone();
    all.guarantee = Formula::And {
        items: vec![base.guarantee.clone(), no_escalate, no_idle],
    };
    assert_eq!(envelope_compatible(&all), Ternary::No);
}

/// The refutation stays a refutation calculus: count subjects never
/// ground, recommended prohibitions never bound, and an obligation
/// conjunct alongside a prohibition refutes only what it forbids.
#[test]
fn refutation_only_edges() {
    // Count-subject prohibition + count-subject envelope: witness sets can
    // differ — Unknown, never No.
    let target = one("At most 3 clients shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("At most 3 clients may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // A merely RECOMMENDED prohibition does not bound.
    let target = one("The client should not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // Obligation-of-one-branch + prohibition-of-another: the obligated
    // branch is not forbidden, so the two-branch envelope routes around.
    let target = one("The client shall not escalate the request.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may either retry or escalate the request."),
        &target,
    )
    .unwrap();
    let mut paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    let must_retry = claim_formula(&one("The client shall retry.")).unwrap();
    paired.guarantee = Formula::And {
        items: vec![paired.guarantee.clone(), must_retry],
    };
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

/// (c) A never-description bounds exactly as a prohibition does; the
/// single-atom refutation is unchanged.
#[test]
fn never_description_and_single_atom_refute() {
    let never = one("The client is never logged.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may be logged."),
        &never,
    )
    .unwrap();
    let paired = contract_formula(&never)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::No);
    let prohibition = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &prohibition,
    )
    .unwrap();
    let paired = contract_formula(&prohibition)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

// =====================================================================
// Change 6 — normalization candidates (proposal-only)
// =====================================================================

/// A passive with a stated agent emits the active-voice candidates with
/// the EXACT legislated stem lists; the note and provenance kind ride on
/// every candidate.
#[test]
fn passive_emits_exact_legislated_stems() {
    let stems = |text: &str| -> Vec<String> {
        normalization_candidates(&one(text))
            .into_iter()
            .map(|c| c.atom.words[0].clone())
            .collect()
    };
    // UPDATED (round 12, change 5 — supersedes the round-11 pin that put
    // the participle first: the better guesses lead now — irregular map
    // hit, then the double-consonant undoubled strip, then the round-11
    // strips, then the participle itself as the always-present fallback).
    // Double-consonant undoubling leads on a map miss.
    assert_eq!(
        stems("Each request shall be logged by the daemon."),
        vec!["log", "logg", "logge", "logged"]
    );
    assert_eq!(
        stems("The report is submitted by the backup daemon."),
        vec!["submit", "submitt", "submitte", "submitted"]
    );
    // en-strip pair with an irregular-map hit leading (take dedupes with
    // the one-character strip).
    assert_eq!(
        stems("The record is taken by the daemon."),
        vec!["take", "tak", "taken"]
    );
    // ed-strip at length four (no doubled consonant, no map hit).
    assert_eq!(
        stems("The record is used by the daemon."),
        vec!["us", "use", "used"]
    );
    // Irregular map hit, then the bare-d strip.
    assert_eq!(
        stems("The record is paid by the daemon."),
        vec!["pay", "pai", "paid"]
    );
    // Three-letter `ed` word falls to the d-strip branch (len > 3 fails).
    assert_eq!(stems("The record is fed by the daemon."), vec!["fe", "fed"]);
    // Irregular map hit where round 11 had no strip at all.
    assert_eq!(
        stems("The report shall be sent by the daemon."),
        vec!["send", "sent"]
    );
    // Candidate shape: kind, subject, patient-as-object, no Agent role,
    // non-empty note.
    for c in normalization_candidates(&one("Each request shall be logged by the daemon.")) {
        assert_eq!(c.kind, NormalizationKind::ActivePassive);
        assert_eq!(c.subject.head, "daemon");
        assert_eq!(c.atom.objects.len(), 1);
        assert_eq!(c.atom.objects[0].head, "request");
        assert!(c.atom.roles.is_empty());
        assert!(!c.note.is_empty());
    }
}

/// Structure survives where legislated: agent restrictors, coordinated
/// agents (one candidate set per item, surface order), and the non-Agent
/// role tail.
#[test]
fn candidate_structure_is_preserved() {
    let c = normalization_candidates(&one("The report is submitted by the backup daemon."));
    assert_eq!(c[0].subject.head, "daemon");
    assert_eq!(c[0].subject.restrictor, vec!["backup".to_string()]);
    // Round 12: `sent` maps to `send` too, so each agent item carries two
    // stems — surface order per item is unchanged.
    let c = normalization_candidates(&one(
        "The report shall be sent by the auditor and the owner.",
    ));
    assert_eq!(c.len(), 4);
    assert_eq!(c[0].subject.head, "auditor");
    assert_eq!(c[1].subject.head, "auditor");
    assert_eq!(c[2].subject.head, "owner");
    assert_eq!(c[3].subject.head, "owner");
    let c = normalization_candidates(&one(
        "The report shall be sent by the daemon within 5 seconds.",
    ));
    assert_eq!(c.len(), 2);
    assert_eq!(c[0].atom.roles.len(), 1);
    assert_eq!(
        c[0].atom.roles[0].kind,
        so_lang::semantics::RoleKind::Deadline
    );
}

/// Out-of-scope shapes emit nothing: actives, agentless passives,
/// definitions, capabilities, comparisons, multi-word predicates, and
/// `either … or …` deontics.
#[test]
fn out_of_scope_shapes_emit_nothing() {
    for text in [
        "The daemon shall log each request.",
        "Each request shall be logged.",
        "The report is submitted.",
        "A session means a sequence of requests.",
        "The client is able to retry.",
        "The retry count is at most 3.",
        "The record is fully archived by the daemon.",
        "The report shall either be sent by the daemon or be archived.",
    ] {
        assert!(normalization_candidates(&one(text)).is_empty(), "{text}");
    }
}

/// FIXED (was a PIN of the reported drift): a PERMISSION passive (`may
/// be sent by …`) no longer emits candidates — the rustdoc scopes the
/// feature to passive BEHAVIORAL claims, and a permission denotes
/// admissibility, not behavior. Recommendations (`should`) stay in
/// scope: a preference is still a behavioral claim.
#[test]
fn permission_passive_emits_nothing() {
    assert!(normalization_candidates(&one("The report may be sent by the daemon.")).is_empty());
    let c = normalization_candidates(&one("The report should be sent by the daemon."));
    // Round 12: the irregular map adds `send` ahead of the participle.
    assert_eq!(c.len(), 2);
    assert_eq!(c[0].atom.words, vec!["send"]);
    assert_eq!(c[1].atom.words, vec!["sent"]);
}

/// FIXED (was FINDING 4): NEGATED passives emit NOTHING. The candidate
/// atom carries no polarity slot, so `is never submitted by the daemon`
/// and `shall not be sent by the daemon` would propose the same active
/// atoms their affirmative twins do — the negation would be simply lost.
/// Rather than grow a polarity field the candidate cannot honestly
/// carry through consumers, negated sites are out of scope.
#[test]
fn negated_passives_must_not_emit_affirmative_candidates() {
    assert!(
        normalization_candidates(&one("The report is never submitted by the daemon.")).is_empty()
    );
    assert!(
        normalization_candidates(&one("The report shall not be sent by the daemon.")).is_empty()
    );
}

/// Proposal-only doctrine, verified operationally: the relation engine
/// does not consume candidates — a passive and its active twin stay
/// Unknown in both directions (no crude morphological Yes).
#[test]
fn candidates_never_reach_the_relation_engine() {
    let passive = contract_formula(&one("The request shall be logged by the daemon.")).unwrap();
    let active = contract_formula(&one("The daemon shall log the request.")).unwrap();
    assert_eq!(refines(&passive, &active), Ternary::Unknown);
    assert_eq!(refines(&active, &passive), Ternary::Unknown);
}

// =====================================================================
// Totality — seeded fuzz around the ambiguity frontier
// =====================================================================

/// Seeded fuzz over the exact vocabulary the frontier discriminates on
/// (determiners, count determiners, particles, numbers, `ly` words,
/// reserved words, copulas) in guard, exception, and content positions:
/// parse is TOTAL — one tree or one error, never a panic — and every
/// error renders.
#[test]
fn frontier_fuzz_is_total() {
    const VOCAB: &[&str] = &[
        "the",
        "a",
        "no",
        "each",
        "at",
        "least",
        "most",
        "exactly",
        "3",
        "zero",
        "client",
        "clients",
        "send",
        "sends",
        "telemetry",
        "quickly",
        "out",
        "up",
        "of",
        "that",
        "is",
        "are",
        "active",
        "who",
        "daemon",
        "backup",
        "and",
        "or",
        "both",
        "either",
        "within",
        "seconds",
        "5",
        "not",
    ];
    let mut state: u64 = 0x5eed_c0de_1011;
    let mut next = move || {
        // xorshift64*
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state.wrapping_mul(0x2545_F491_4F6C_DD1D)
    };
    let mut parsed = 0usize;
    for i in 0..4000 {
        let len = 1 + (next() % 6) as usize;
        let words: Vec<&str> = (0..len)
            .map(|_| VOCAB[(next() % VOCAB.len() as u64) as usize])
            .collect();
        let clause = words.join(" ");
        let text = match i % 4 {
            0 => format!("When {clause}, the fan shall run."),
            1 => format!("The pump shall stop, unless {clause}."),
            2 => format!("The monitor shall ensure that {clause}."),
            _ => format!("While {clause}, the fan shall run."),
        };
        match parse(&text) {
            Ok(spec) => {
                parsed += 1;
                assert_eq!(spec.sentences.len(), 1, "{text}");
            }
            Err(e) => {
                // Every error renders and carries a stable kind.
                assert!(!e.to_string().is_empty(), "{text}");
                assert!(!e.kind().is_empty(), "{text}");
            }
        }
    }
    // The fuzz must exercise both sides of the frontier.
    assert!(parsed > 0, "some fuzz inputs must parse");
    assert!(parsed < 4000, "some fuzz inputs must reject");
}
