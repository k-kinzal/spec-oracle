//! Round 8: clausal role values carry the full nested skeleton (1),
//! pairing hardened against vacuous reliances (2), assumption
//! satisfiability (3), role tails for copular predicates in clauses and
//! relatives (4), positional-consistent capability (5), and the envelope
//! compatibility judgment (6).

use so_lang::ast::*;
use so_lang::parse::parse;
use so_reason::formula::{
    claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula, PairingError,
};
use so_reason::relate::{
    assess, assumption_satisfiable, contradicts, envelope_compatible, implies, RelationVerdict,
    Ternary,
};
use so_reason::semantics::*;

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("parse failed for {input:?}: {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn cf(input: &str) -> Formula {
    claim_formula(&one(input)).unwrap()
}

/// Round 11 (change 3): the satisfiability pins build their reliances with
/// an EXPLICIT selection (the whole source conditional) — a default
/// reliance is a permanent candidate now and never enters A, so it could
/// never make A unsatisfiable.
fn explicit_source(kind: EdgeKind, source: &Sentence, target: &Sentence) -> AssumptionSource {
    let default = AssumptionSource::for_guarantee(kind, source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(kind, source, target, default.formula.clone())
        .unwrap()
}

fn render_round_trips(s: &Sentence) {
    let rendered = s.render();
    let re = one(&rendered);
    assert_eq!(
        re.render(),
        rendered,
        "canonical render must be a fixed point"
    );
}

// ====================================================================================
// 1. Clausal role values carry the full nested skeleton
// ====================================================================================

#[test]
fn negated_nested_clause_no_longer_equates_with_the_affirmative() {
    // The motivating pair: the flat {subject_head, words} digest made
    // these two atoms EQUAL — a false equivalence between waiting on "no
    // backup completes" and "the backup completes".
    let neg = cf("The daemon shall purge the cache after no backup completes.");
    let aff = cf("The daemon shall purge the cache after the backup completes.");
    assert_eq!(implies(&neg, &aff), Ternary::Unknown, "no false Yes");
    assert_eq!(implies(&aff, &neg), Ternary::Unknown, "no false Yes");
    // No nested-clause contradiction logic yet (deliberate stop, change 1):
    // a polarity mismatch in the nested skeleton is enough for Unknown.
    assert_eq!(contradicts(&neg, &aff), Ternary::Unknown);
}

#[test]
fn affirmative_identical_nested_clauses_still_meet() {
    // Identical nested clauses across shall/must still carry one
    // proposition — the richer digest must not break the true Yes.
    let a = cf("The daemon shall purge the cache after the backup completes.");
    let b = cf("The daemon must purge the cache after the backup completes.");
    assert_eq!(implies(&a, &b), Ternary::Yes);
    assert_eq!(implies(&b, &a), Ternary::Yes);
}

#[test]
fn before_after_until_all_carry_the_nested_skeleton() {
    for (neg, aff) in [
        (
            "The daemon shall flush the queue before no user logs out.",
            "The daemon shall flush the queue before the user logs out.",
        ),
        (
            "The daemon shall purge the cache after no backup completes.",
            "The daemon shall purge the cache after the backup completes.",
        ),
        (
            "The pump shall run until no valve is open.",
            "The pump shall run until the valve is open.",
        ),
    ] {
        let kn = skeleton(&one(neg)).unwrap();
        let ka = skeleton(&one(aff)).unwrap();
        let vn = &kn.atoms[0].roles[0].value;
        let va = &ka.atoms[0].roles[0].value;
        assert_ne!(vn, va, "digests must differ for {neg:?} vs {aff:?}");
        match (vn, va) {
            (
                RoleValue::Clause {
                    skeleton: sn,
                    full: fn_,
                },
                RoleValue::Clause {
                    skeleton: sa,
                    full: fa,
                },
            ) => {
                assert_eq!(sn.polarity, Some(Polarity::Negative), "in {neg:?}");
                assert_eq!(sa.polarity, None, "in {aff:?}");
                assert_ne!(fn_, fa, "full renders differ");
            }
            other => panic!("expected clause digests, got {other:?}"),
        }
        assert_eq!(implies(&cf(neg), &cf(aff)), Ternary::Unknown);
        assert_eq!(implies(&cf(aff), &cf(neg)), Ternary::Unknown);
    }
}

#[test]
fn nested_clause_digest_keeps_manner_and_comparison() {
    // The nested skeleton is the WHOLE clause digest: manner and the
    // structured comparison survive the nesting.
    let k = skeleton(&one(
        "The daemon shall retry after the export completes successfully.",
    ))
    .unwrap();
    match &k.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.manner, vec!["successfully"]);
            assert_eq!(full, "the export completes successfully");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    let k = skeleton(&one("The pump shall run until the reading is at most 5.")).unwrap();
    match &k.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, .. } => {
            assert!(skeleton.comparison.is_some(), "nested comparison digested");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
}

#[test]
fn clause_role_value_serde_shape() {
    // Serde pin (round 8): {"kind":"clause","skeleton":{…},"full":"…"}.
    let k = skeleton(&one(
        "The daemon shall purge the cache after no backup completes.",
    ))
    .unwrap();
    let j = serde_json::to_value(&k).unwrap();
    let value = &j["atoms"][0]["roles"][0]["value"];
    assert_eq!(value["kind"], "clause");
    assert_eq!(value["skeleton"]["subject_head"], "backup");
    assert_eq!(value["skeleton"]["polarity"], "negative");
    assert_eq!(value["skeleton"]["words"], serde_json::json!(["completes"]));
    assert_eq!(value["full"], "no backup completes");
    let back: Skeleton = serde_json::from_value(j).unwrap();
    assert_eq!(back, k);
}

// ====================================================================================
// 2. Pairing hardened against vacuous reliances
// ====================================================================================

#[test]
fn bottom_relied_is_rejected_as_vacuous() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    let err = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        Formula::Bottom,
    )
    .unwrap_err();
    assert_eq!(err, PairingError::VacuousRelied);
    assert_eq!(err.kind(), "vacuous_relied");
}

#[test]
fn relied_that_simplifies_to_bottom_is_rejected_too() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    // Not(Top) and And{…, Bottom} both simplify to Bottom: the gate is on
    // the simplified form, not the literal constructor.
    for vacuous in [
        Formula::Not {
            inner: Box::new(Formula::Top),
        },
        Formula::And {
            items: vec![claim_formula(&source).unwrap(), Formula::Bottom],
        },
    ] {
        let err = AssumptionSource::for_guarantee_with_relied(
            EdgeKind::OccurrenceReliance,
            &source,
            &target,
            vacuous,
        )
        .unwrap_err();
        assert_eq!(err, PairingError::VacuousRelied);
    }
}

#[test]
fn proven_flag_is_true_for_proven_reliances() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    // The default reliance (the whole source formula) is self-entailment.
    let s =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert!(s.proven, "relying on the whole source formula is proven");
    // An explicit reliance the formula provably entails.
    let s = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&source).unwrap(),
    )
    .unwrap();
    assert!(s.proven, "implies == Yes at construction");
}

#[test]
fn proven_flag_is_false_for_unproven_reliances() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    // A reliance the structural rules cannot prove: accepted (round-7
    // conservatism, unchanged) but visibly UNPROVEN — a candidate edge,
    // not a contract-forming one.
    let s = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&one("The gateway shall forward the packet.")).unwrap(),
    )
    .unwrap();
    assert!(
        !s.proven,
        "Unknown at construction builds with proven = false"
    );
}

// ====================================================================================
// 3. Assumption satisfiability (pre-saturation)
// ====================================================================================

#[test]
fn conjoined_reliances_with_disjoint_count_intervals_are_unsatisfiable() {
    let target = one("The daemon shall balance the load.");
    let a = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("At least 5 replicas shall run."),
        &target,
    );
    let b = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("At most 3 replicas shall run."),
        &target,
    );
    let paired = contract_formula(&target).unwrap().paired(&[a, b]);
    assert_eq!(
        assumption_satisfiable(&paired),
        Ternary::No,
        "at-least-5 ∧ at-most-3 over one proposition is provably empty"
    );
}

#[test]
fn compatible_reliances_stay_unknown_never_yes() {
    // ASYMMETRY DOCTRINE: satisfiability is not provable syntactically, so
    // the good case is Unknown ("not disproven") — never Yes.
    let target = one("The daemon shall balance the load.");
    let a = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("At least 3 replicas shall run."),
        &target,
    )
    .unwrap();
    let b = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("At least 5 replicas shall run."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[a, b]);
    assert_eq!(assumption_satisfiable(&paired), Ternary::Unknown);
    // The ingest contract (no sources, assumption ⊤) is Unknown too.
    assert_eq!(
        assumption_satisfiable(&contract_formula(&target).unwrap()),
        Ternary::Unknown
    );
}

#[test]
fn envelope_sources_are_excluded_from_the_satisfiability_check() {
    let target = one("The daemon shall balance the load.");
    let reliance = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("At least 5 replicas shall run."),
        &target,
    )
    .unwrap();
    // An envelope whose relied formula WOULD contradict the reliance if it
    // entered the conjunction — envelopes never do (round 6), so the
    // assumption stays not-disproven.
    let envelope = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::AdmissibilityEnvelope,
        &one("The replicas may pause."),
        &target,
        claim_formula(&one("At most 3 replicas shall run.")).unwrap(),
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(&[reliance, envelope]);
    assert_eq!(assumption_satisfiable(&paired), Ternary::Unknown);
}

#[test]
fn atom_against_its_negation_is_unsatisfiable() {
    let target = one("The daemon shall balance the load.");
    let a = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The gateway shall forward the packet."),
        &target,
    );
    let b = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The gateway shall not forward the packet."),
        &target,
    );
    let paired = contract_formula(&target).unwrap().paired(&[a, b]);
    assert_eq!(assumption_satisfiable(&paired), Ternary::No);
}

// ====================================================================================
// 4. Role tails for copular predicates in clauses and relatives
// ====================================================================================

#[test]
fn copular_guard_carries_a_structured_location_role() {
    // The motivating gap: `active at the depot` was flat predicate words.
    let s = one("While the pump is active at the depot, the daemon shall wait.");
    let k = skeleton(&s).unwrap();
    let guard = &k.guards.states[0];
    assert_eq!(guard.words, vec!["active"]);
    assert_eq!(guard.roles.len(), 1);
    assert_eq!(guard.roles[0].kind, RoleKind::Location);
    render_round_trips(&s);
    // Lossiness: differing locations now separate the guard digests.
    let dock = skeleton(&one(
        "While the pump is active at the dock, the daemon shall wait.",
    ))
    .unwrap();
    assert_ne!(k.guards.states[0], dock.guards.states[0]);
}

#[test]
fn copular_relative_carries_agent_and_roles() {
    // `that is signed by the user`: the agent is recorded (round-5 shape,
    // mirrored into relatives).
    let s = one("Each request that is signed by the user shall be logged.");
    match &s.core {
        Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } => match &np.relative.as_ref().unwrap().body {
            RelativeBody::Copular {
                predicate,
                agent,
                roles,
                ..
            } => {
                assert_eq!(
                    predicate,
                    &Predicate::Words {
                        words: vec!["signed".into()]
                    }
                );
                assert_eq!(agent.as_ref().unwrap().heads(), vec!["user"]);
                assert!(roles.is_empty());
            }
            other => panic!("expected copular relative with agent, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
    // The relative joins the subject's full-fidelity identity.
    let k = skeleton(&s).unwrap();
    assert_eq!(k.subject.full, "request that is signed by the user");
    // A role tail on a copular relative: innermost attachment.
    let s = one("Each request that is valid within 5 seconds shall be logged.");
    match &s.core {
        Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } => match &np.relative.as_ref().unwrap().body {
            RelativeBody::Copular { roles, .. } => {
                assert!(matches!(roles.as_slice(), [RolePp::Deadline(_)]));
            }
            other => panic!("expected copular relative with roles, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn copular_guard_agent_then_roles_and_late_agent_role() {
    // Agent immediately after the predicate (round-5 shape), roles after.
    let s = one("When the request is submitted by the user within 5 seconds, the daemon shall log the request.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Copular { agent, roles, .. } => {
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["user"]);
            assert!(matches!(roles.as_slice(), [RolePp::Deadline(_)]));
        }
        other => panic!("expected copular body, got {other:?}"),
    }
    render_round_trips(&s);
    // A `by` later in the tail is the Agent ROLE (a copular body is a
    // passive site): both spellings digest to one Agent role kind.
    let s = one("When the record is stored in the archive by the daemon, the auditor shall sign the record.");
    let k = skeleton(&s).unwrap();
    let guard = &k.guards.trigger.as_ref().unwrap().clauses[0];
    assert_eq!(guard.words, vec!["stored"]);
    assert_eq!(
        guard.roles.iter().map(|r| r.kind).collect::<Vec<_>>(),
        vec![RoleKind::Location, RoleKind::Agent]
    );
    render_round_trips(&s);
}

#[test]
fn content_clause_deadline_is_structured_inside_the_content_skeleton() {
    // Content complements are clauses, so they inherit the role tail: the
    // inner deadline is a structured Deadline INSIDE the content skeleton
    // (attachment stays inner — the outer form is written roles-first).
    let s = one("The system shall verify that the token is valid within 5 seconds.");
    let k = skeleton(&s).unwrap();
    let content = k.atoms[0].content.as_ref().expect("content");
    assert_eq!(content.clause.words, vec!["valid"]);
    assert_eq!(content.clause.roles.len(), 1);
    assert_eq!(content.clause.roles[0].kind, RoleKind::Deadline);
    assert_eq!(
        content.clause.roles[0].value,
        RoleValue::Measure {
            number: "5".into(),
            unit: Some("seconds".into())
        }
    );
    assert_eq!(content.full, "the token is valid within 5 seconds");
    render_round_trips(&s);
}

#[test]
fn copular_until_and_exception_roles_round_trip() {
    // The tail reaches every clause position: until-roles and exceptions.
    let s = one("The pump shall run until the tank is full at the depot.");
    let k = skeleton(&s).unwrap();
    match &k.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.words, vec!["full"]);
            assert_eq!(skeleton.roles[0].kind, RoleKind::Location);
            assert_eq!(full, "the tank is full at the depot");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    render_round_trips(&s);
    let s = one("The pump shall stop, unless the override is active on the console.");
    let k = skeleton(&s).unwrap();
    let exception = k.exception.as_ref().unwrap();
    assert_eq!(exception.words, vec!["active"]);
    assert_eq!(exception.roles[0].kind, RoleKind::Location);
    render_round_trips(&s);
}

// ====================================================================================
// 5. Capability is positional-consistent
// ====================================================================================

#[test]
fn able_to_parses_in_copular_clause_bodies() {
    let s = one("While the client is able to retry, the pump shall run.");
    match &s.frames.states[0].clause.items[0].body {
        ClauseBody::Copular {
            predicate: Predicate::AbleTo { vp },
            ..
        } => {
            assert_eq!(vp.verb, "retry");
        }
        other => panic!("expected AbleTo in the guard, got {other:?}"),
    }
    render_round_trips(&s);
    // With particle, manner, and a role: the vp carries them.
    let s = one("While the daemon is able to shut down gracefully within 5 seconds, the operator shall wait.");
    match &s.frames.states[0].clause.items[0].body {
        ClauseBody::Copular {
            predicate: Predicate::AbleTo { vp },
            ..
        } => {
            assert_eq!(vp.verb, "shut");
            assert_eq!(vp.particle.as_deref(), Some("down"));
            assert_eq!(vp.manner, vec!["gracefully"]);
            assert!(matches!(vp.roles.as_slice(), [RolePp::Deadline(_)]));
        }
        other => panic!("expected AbleTo in the guard, got {other:?}"),
    }
    render_round_trips(&s);
    // Legislated: clause bodies have no adverb slot, so BARE able-to only
    // — `is always able to` is a description form; in a clause the words
    // stay ordinary predicate material, never a capability.
    let s = one("While the client is always able to retry, the pump shall run.");
    assert!(
        !matches!(
            &s.frames.states[0].clause.items[0].body,
            ClauseBody::Copular {
                predicate: Predicate::AbleTo { .. },
                ..
            }
        ),
        "adverbed able-to never reads as capability in a clause"
    );
}

#[test]
fn able_to_parses_in_copular_relatives() {
    let s = one("Each daemon that is able to shut down gracefully shall register.");
    match &s.core {
        Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } => match &np.relative.as_ref().unwrap().body {
            RelativeBody::Copular {
                predicate: Predicate::AbleTo { vp },
                ..
            } => {
                assert_eq!(vp.verb, "shut");
                assert_eq!(vp.particle.as_deref(), Some("down"));
                assert_eq!(vp.manner, vec!["gracefully"]);
            }
            other => panic!("expected AbleTo in the relative, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn able_to_guard_digest_is_structural() {
    // The guard digest represents the capability structurally: the verb
    // kernel under `able to`, with the vp's roles as structured roles —
    // the SAME structured pieces a capability description's atom carries,
    // so capability statements and capability guards meet shape-for-shape.
    let s = one("While the client is able to retry within 5 seconds, the pump shall run.");
    let k = skeleton(&s).unwrap();
    let guard = &k.guards.states[0];
    assert_eq!(guard.words, vec!["able", "to", "retry"]);
    assert_eq!(guard.roles.len(), 1);
    assert_eq!(
        guard.roles[0],
        RoleSkeleton {
            kind: RoleKind::Deadline,
            value: RoleValue::Measure {
                number: "5".into(),
                unit: Some("seconds".into())
            },
            marker: None,
        }
    );
    // The capability description's atom digests the same structured role.
    let d = skeleton(&one("The client is able to retry within 5 seconds.")).unwrap();
    assert_eq!(
        d.atoms[0].roles, guard.roles,
        "description and guard meet structurally"
    );
    // Lossiness: differing deadlines separate the guard digests.
    let k10 = skeleton(&one(
        "While the client is able to retry within 10 seconds, the pump shall run.",
    ))
    .unwrap();
    assert_ne!(k.guards.states[0], k10.guards.states[0]);
}

#[test]
fn able_to_guards_ground_a_conditional_contradiction() {
    // The concrete pair (change 5): one written able-to guard scopes both
    // sides, so the claim-level conflict is a conditional contradiction —
    // capability guards participate in the round-7 guard-aware rule.
    let a = one("While the client is able to retry, the gateway shall throttle the queue.");
    let b = one("While the client is able to retry, the gateway shall not throttle the queue.");
    assert_eq!(assess(&a, &b), RelationVerdict::HardContradiction);
    // Differing capability guards do not witness a shared region: Unknown.
    let c = one("While the client is able to pause, the gateway shall not throttle the queue.");
    assert_eq!(assess(&a, &c), RelationVerdict::Unknown);
}

// ====================================================================================
// 6. Envelope compatibility judgment
// ====================================================================================

#[test]
fn envelope_violated_when_the_guarantee_forbids_the_admitted_behavior() {
    // A may-retry envelope retained on a shall-not-retry guarantee: the
    // guarantee prohibits exactly what the envelope admits. (Built via
    // `from_sentence`: a pairing like this arrives from the graph layer,
    // which is exactly why the judgment exists.)
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

#[test]
fn unrelated_envelope_stays_unknown_never_yes() {
    // ASYMMETRY DOCTRINE: compatibility is not provable syntactically —
    // the good case is Unknown ("no violation provable"), never Yes.
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The gateway may compress the payload."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // No envelopes retained at all: nothing to violate — Unknown.
    assert_eq!(
        envelope_compatible(&contract_formula(&target).unwrap()),
        Ternary::Unknown
    );
}

#[test]
fn envelope_check_respects_guards_and_count_subjects() {
    // Guarded prohibition + unguarded envelope: the envelope's Top guard
    // witnesses the prohibition's own region — still a violation.
    let target = one("While the breaker is open, the client shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::No);
    // Count subjects never ground (round-7 witness-set argument): `at
    // least 3 clients shall not retry` tolerates other retriers.
    let target = one("At least 3 clients shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The clients may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

#[test]
fn proven_serde_default_is_false_for_old_json() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    let s =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let mut json = serde_json::to_value(&s).unwrap();
    assert_eq!(json["proven"], true, "round-8 sources serialize the flag");
    // Pre-round-8 JSON has no `proven` field: it loads as UNPROVEN, even
    // though a re-derivation would prove the defaulted reliance
    // (documented: deserialization restores, it never judges).
    json.as_object_mut().unwrap().remove("proven");
    let back: AssumptionSource = serde_json::from_value(json).unwrap();
    assert!(!back.proven);
    assert_eq!(back.relied, back.formula);
}
