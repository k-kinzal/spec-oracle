//! Round 9: the improvements the ninth external adversarial critique bound.
//!
//! 1. Locative prepositions enter role identity (`in` vs `on the archive`).
//! 2. Contract-forming pairing is proven-only (`paired` conjoins proven
//!    reliances; unproven sources stay candidates).
//! 3. Object-gap relatives (`each request that the gateway forwards`).
//! 4. Content complements in verbal CLAUSE bodies (frames/guards).
//! 5. Guard canonicalization + the interval overlap witness.
//! 6. A descending `between` is a parse error, not an empty interval.

use so_lang::ast::*;
use so_lang::formula::{
    claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{assess, assumption_satisfiable, contradicts, implies, Outcome, Ternary};
use so_lang::semantics::{skeleton, subject_keys, RoleKind};

fn one(input: &str) -> Sentence {
    let spec = parse(input).expect(input);
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

/// Canonical render re-parses to the same tree (source aside).
fn roundtrip(input: &str) {
    let s = one(input);
    let rendered = s.render();
    let back = one(&rendered);
    assert_eq!(back.render(), rendered, "render must be a fixpoint for {input:?}");
    let mut a = s.clone();
    a.source = String::new();
    let mut b = back.clone();
    b.source = String::new();
    assert_eq!(a, b, "canonical form must re-parse to the same tree for {input:?}");
}

// ====================================================================================
// 1. Locative prepositions enter role identity
// ====================================================================================

#[test]
fn location_marker_separates_in_from_on() {
    let in_ = skeleton(&one("The system shall store the report in the archive.")).unwrap();
    let on = skeleton(&one("The system shall store the report on the archive.")).unwrap();
    assert_ne!(in_.atoms[0], on.atoms[0]);
    assert_eq!(in_.atoms[0].roles[0].kind, RoleKind::Location);
    assert_eq!(in_.atoms[0].roles[0].marker.as_deref(), Some("in"));
    assert_eq!(on.atoms[0].roles[0].marker.as_deref(), Some("on"));
    // Same value digest — the marker alone separates them.
    assert_eq!(in_.atoms[0].roles[0].value, on.atoms[0].roles[0].value);
}

#[test]
fn location_marker_is_lowercased_and_same_prep_still_matches() {
    let a = skeleton(&one("The system shall store the report IN the archive.")).unwrap();
    let b = skeleton(&one("The system shall store the report in the archive.")).unwrap();
    assert_eq!(a.atoms[0], b.atoms[0], "the marker is lowercased, so casing never splits");
}

#[test]
fn in_vs_on_claims_relate_unknown_not_yes_and_not_no() {
    // The pair no longer implies/equates; nothing proves disjointness of
    // the two places either, so Unknown is the honest verdict both ways.
    let in_ = claim_formula(&one("The system shall store the report in the archive.")).unwrap();
    let on = claim_formula(&one("The system shall store the report on the archive.")).unwrap();
    assert_eq!(implies(&in_, &on), Ternary::Unknown);
    assert_eq!(implies(&on, &in_), Ternary::Unknown);
    assert_eq!(contradicts(&in_, &on), Ternary::Unknown);
    // End to end: the two obligations are no longer Equivalent.
    assert_eq!(
        assess(
            &one("The system shall store the report in the archive."),
            &one("The system shall store the report on the archive."),
        ),
        Outcome::Unknown
    );
    // Same preposition still meets: equivalence is preserved.
    assert_eq!(
        assess(
            &one("The system shall store the report in the archive."),
            &one("The system shall store the report in the archive."),
        ),
        Outcome::Equivalent
    );
}

#[test]
fn non_locative_roles_keep_a_none_marker_and_old_json_loads() {
    let k = skeleton(&one("The daemon shall send the report to the auditor within 5 seconds."))
        .unwrap();
    assert!(k.atoms[0].roles.iter().all(|r| r.marker.is_none()));
    // Serde: the marker serializes only when present, so pre-round-9
    // skeletons (no `marker` field) load unchanged.
    let loc = skeleton(&one("The pump shall run at the depot.")).unwrap();
    let mut json = serde_json::to_value(&loc.atoms[0].roles[0]).unwrap();
    assert_eq!(json["marker"], "at");
    json.as_object_mut().unwrap().remove("marker");
    let back: so_lang::semantics::RoleSkeleton = serde_json::from_value(json).unwrap();
    assert!(back.marker.is_none());
    let no_marker = serde_json::to_value(&k.atoms[0].roles[0]).unwrap();
    assert!(no_marker.get("marker").is_none(), "absent markers are skipped");
}

#[test]
fn guard_location_roles_carry_the_marker_too() {
    let a = skeleton(&one("While the pump is active in the depot, the daemon shall wait."))
        .unwrap();
    let b = skeleton(&one("While the pump is active at the depot, the daemon shall wait."))
        .unwrap();
    assert_ne!(a.guards.states[0], b.guards.states[0], "guard digests see the preposition");
    assert_eq!(a.guards.states[0].roles[0].marker.as_deref(), Some("in"));
}

// ====================================================================================
// 2. Contract-forming pairing is proven-only
// ====================================================================================

#[test]
fn unproven_sources_stay_out_of_the_paired_assumption() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    // An Unknown reliance: accepted (round-7 conservatism) but UNPROVEN —
    // a candidate edge that must not relieve the guarantee.
    let unproven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&one("The gateway shall forward the packet.")).unwrap(),
    )
    .unwrap();
    assert!(!unproven.proven);
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&unproven));
    assert_eq!(
        paired.assumption,
        Formula::Top,
        "a candidate edge leaves the assumption unchanged"
    );
    assert_eq!(paired.sources.len(), 1, "the candidate is retained in sources");
    // The saturated form is the guarantee itself: nothing relieves it.
    assert_eq!(paired.saturated(), paired.guarantee);
}

#[test]
fn proven_sources_form_the_assumption() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    // Round 11 (change 3): proven alone no longer suffices — the reliance
    // must be selected explicitly to form A.
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert!(default.proven);
    assert!(!default.contract_forming(), "default reliance: candidate only (round 11)");
    let proven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        default.formula.clone(),
    )
    .unwrap();
    assert!(proven.proven);
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&proven));
    assert_eq!(paired.assumption, proven.relied);
}

#[test]
fn mixed_sources_conjoin_only_the_proven_reliances() {
    let target = one("The daemon shall process the event.");
    // Round 11 (change 3): the proven sources select their reliances
    // explicitly (the graph-edge entry point).
    let explicit = |kind, text: &str| {
        let source = one(text);
        let default = AssumptionSource::for_guarantee(kind, &source, &target).unwrap();
        AssumptionSource::for_guarantee_with_relied(kind, &source, &target, default.formula)
            .unwrap()
    };
    let proven_a = explicit(EdgeKind::OccurrenceReliance, "The gateway shall deliver the event.");
    let proven_b =
        explicit(EdgeKind::GuaranteeDischarge, "The scheduler shall start the worker.");
    let unproven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &one("The broker shall hold the queue."),
        &target,
        claim_formula(&one("The broker shall drain the queue.")).unwrap(),
    )
    .unwrap();
    assert!(!unproven.proven);
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[
        proven_a.clone(),
        unproven,
        proven_b.clone(),
        envelope,
    ]);
    assert_eq!(
        paired.assumption,
        Formula::And { items: vec![proven_a.relied.clone(), proven_b.relied.clone()] },
        "A conjoins exactly the proven non-envelope reliances"
    );
    assert_eq!(paired.sources.len(), 4, "candidates and envelopes stay retained");
}

#[test]
fn unproven_only_pairing_keeps_top_and_saturation_shape() {
    let target = one("The daemon shall process the event.");
    let unproven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &one("The gateway shall deliver the event."),
        &target,
        claim_formula(&one("The gateway shall forward the packet.")).unwrap(),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[unproven]);
    assert_eq!(paired.assumption, Formula::Top);
    // Satisfiability judges the contract-forming assumption (Top here):
    // an unproven candidate cannot make A unsatisfiable.
    assert_eq!(assumption_satisfiable(&paired), Ternary::Unknown);
}

// ====================================================================================
// 3. Object-gap relatives
// ====================================================================================

#[test]
fn the_motivating_object_gap_sentence_parses() {
    // SUPERSEDED PIN (round 9, recorded): rounds 6–8 pinned this sentence
    // as DeterminerAsVerb — the precise rejection that replaced the round-6
    // nonsense tree (relative verb `the`). The gap reading now exists, so
    // the rejection is superseded by a correct parse.
    let s = one("Each request that the gateway forwards shall be logged.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    let rel = np.relative.as_ref().expect("relative");
    assert_eq!(rel.marker, RelMarker::That);
    match &rel.body {
        RelativeBody::ObjectGap { subject, verb, particle, manner, roles } => {
            assert_eq!(subject.heads(), vec!["gateway"]);
            assert_eq!(verb, "forwards");
            assert!(particle.is_none());
            assert!(manner.is_empty());
            assert!(roles.is_empty());
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip("Each request that the gateway forwards shall be logged.");
}

#[test]
fn object_gap_with_roles_particle_and_manner() {
    let s = one(
        "Each packet that the router sends out promptly via the tunnel within 5 seconds \
         shall be counted.",
    );
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { subject, verb, particle, manner, roles } => {
            assert_eq!(subject.heads(), vec!["router"]);
            assert_eq!(verb, "sends");
            assert_eq!(particle.as_deref(), Some("out"));
            assert_eq!(manner, &vec!["promptly".to_string()]);
            assert_eq!(roles.len(), 2, "Means and Deadline attach to the gap verb");
            assert!(matches!(&roles[0], RolePp::Means { .. }));
            assert!(matches!(&roles[1], RolePp::Deadline(_)));
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip(
        "Each packet that the router sends out promptly via the tunnel within 5 seconds \
         shall be counted.",
    );
}

#[test]
fn who_form_object_gap_parses() {
    let s = one("Each user who the auditor flags shall be reviewed.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    let rel = np.relative.as_ref().expect("relative");
    assert_eq!(rel.marker, RelMarker::Who);
    match &rel.body {
        RelativeBody::ObjectGap { subject, verb, .. } => {
            assert_eq!(subject.heads(), vec!["auditor"]);
            assert_eq!(verb, "flags");
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip("Each user who the auditor flags shall be reviewed.");
}

#[test]
fn object_gap_subject_may_carry_an_of_chain_and_coordination() {
    let s = one("Each file that the owner of the workspace shares shall be scanned.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { subject, verb, .. } => {
            let NpGroup::Single(inner) = subject else { panic!("single gap subject") };
            assert_eq!(inner.head, "owner");
            assert_eq!(inner.of.as_ref().unwrap().head, "workspace");
            assert_eq!(verb, "shares");
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    let s = one("Each event that the gateway and the proxy forward shall be logged.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { subject, verb, .. } => {
            assert_eq!(subject.heads(), vec!["gateway", "proxy"]);
            assert_eq!(verb, "forward");
        }
        other => panic!("expected object gap, got {other:?}"),
    }
}

#[test]
fn object_gap_in_object_position_and_in_guards() {
    // Object position: `the packets that the gateway forwards`.
    let s = one("The daemon shall log the packets that the gateway forwards.");
    let Core::Deontic { vp, .. } = &s.core else { panic!("deontic") };
    let object = vp.single().unwrap().object.as_ref().unwrap();
    let NpGroup::Single(np) = object else { panic!("single object") };
    assert!(matches!(
        &np.relative.as_ref().unwrap().body,
        RelativeBody::ObjectGap { .. }
    ));
    // Guard position: the subject of a frame clause restricted by a gap.
    let s = one("When each request that the gateway forwards arrives, the daemon shall wake.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    let clause = &trigger.clause.items[0];
    let NpGroup::Single(np) = &clause.subject else { panic!("single subject") };
    assert!(matches!(
        &np.relative.as_ref().unwrap().body,
        RelativeBody::ObjectGap { .. }
    ));
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "arrives"));
    roundtrip("When each request that the gateway forwards arrives, the daemon shall wake.");
}

#[test]
fn object_gap_enters_full_identity_but_never_subject_keys() {
    // Lossiness: the gap relative is part of the subject's full identity,
    // so differently-restricted subjects never share a proposition.
    let a = skeleton(&one("Each request that the gateway forwards shall be logged.")).unwrap();
    let b = skeleton(&one("Each request that the proxy forwards shall be logged.")).unwrap();
    assert_eq!(a.subject.full, "request that the gateway forwards");
    assert_ne!(a.subject.full, b.subject.full);
    assert_eq!(
        assess(
            &one("Each request that the gateway forwards shall be logged."),
            &one("Each request that the proxy forwards shall be logged."),
        ),
        Outcome::Unknown
    );
    // PIN: relatives never enter subject keys — gap relatives included.
    assert_eq!(
        subject_keys(&one("Each request that the gateway forwards shall be logged.")),
        vec!["request".to_string()]
    );
}

#[test]
fn determiner_led_object_after_the_gap_verb_is_still_rejected() {
    // Not a gap: the relative's verb has an explicit determiner-led
    // object, so the head is not the missing object — the round-6/7
    // DeterminerAsVerb diagnosis stands.
    assert!(matches!(
        parse("Each request that the gateway forwards the packet shall be logged."),
        Err(ParseError::DeterminerAsVerb { .. })
    ));
}

#[test]
fn that_plus_copular_stays_copular_never_a_gap() {
    // False-positive guard: a copular relative is claimed by the copular
    // reading before the gap trigger ever looks.
    let s = one("Each request that is signed shall be accepted.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    assert!(matches!(
        &np.relative.as_ref().unwrap().body,
        RelativeBody::Copular { .. }
    ));
    // And a det-led relative whose tail is copular is NOT a gap (`the
    // token is valid` has no verb-position word after any subject split):
    // the round-7 relative-wins-after-a-noun rejection stands.
    assert!(matches!(
        parse("The daemon shall record the fact that the token is valid."),
        Err(ParseError::DeterminerAsVerb { .. })
    ));
}

#[test]
fn subject_gap_relatives_are_unchanged() {
    // Existing subject-gap (verbal) relatives keep their reading: an
    // open-class word after `that` is the relative's VERB.
    let s = one("Each request that arrives from the gateway shall be logged.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::Verbal { verb, roles, .. } => {
            assert_eq!(verb, "arrives");
            assert_eq!(roles.len(), 1);
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
    // Bare-word tails stay verb-led (LEGISLATED, round 9): `that emits
    // telemetry data` keeps verb `emits` — a bare noun phrase after
    // that/who never opens a gap, because `that gateways forward` (gap)
    // and `that holds locks` (verb + object) are indistinguishable without
    // a lexicon, and the established reading must win.
    let s = one("Each daemon that emits telemetry data shall be sampled.");
    let Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let NpGroup::Single(np) = subject else { panic!("single subject") };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "emits");
            assert_eq!(object.as_ref().unwrap().heads(), vec!["data"]);
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
}

#[test]
fn object_gap_serde_round_trip() {
    let s = one("Each request that the gateway forwards shall be logged.");
    let json = serde_json::to_value(&s).unwrap();
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
}

// ====================================================================================
// 4. Content complements in verbal clause bodies
// ====================================================================================

#[test]
fn the_motivating_guard_content_parses() {
    // SUPERSEDED LEGISLATION (round 9, recorded): round 7 kept clause
    // bodies content-free ("frames stay content-free in v0.2") and round 7
    // pinned this sentence as DeterminerAsVerb. New grounds: assumptions
    // depend on observed/asserted content — dependency statements belong
    // in guards — so the verbal clause body now carries the same final
    // content slot a verb phrase does.
    let s = one("When the monitor ensures that the token is valid, the pump shall stop.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    let clause = &trigger.clause.items[0];
    match &clause.body {
        ClauseBody::Verbal { verb, content, object, .. } => {
            assert_eq!(verb, "ensures");
            assert!(object.is_none());
            let content = content.as_ref().expect("content clause");
            assert_eq!(content.subject.heads(), vec!["token"]);
            assert!(matches!(&content.body, ClauseBody::Copular { .. }));
        }
        other => panic!("expected verbal body with content, got {other:?}"),
    }
    roundtrip("When the monitor ensures that the token is valid, the pump shall stop.");
}

#[test]
fn clause_content_is_final_and_follows_roles() {
    let s = one(
        "When the monitor verifies within 5 seconds that the token is valid, \
         the pump shall stop.",
    );
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, roles, content, .. } => {
            assert_eq!(verb, "verifies");
            assert_eq!(roles.len(), 1, "the deadline role precedes the content");
            assert!(content.is_some());
        }
        other => panic!("expected verbal body, got {other:?}"),
    }
    roundtrip(
        "When the monitor verifies within 5 seconds that the token is valid, \
         the pump shall stop.",
    );
}

#[test]
fn content_in_exceptions_and_nested_until_clauses() {
    // Exception clause content.
    let s = one("The pump shall stop, unless the monitor reports that the link is down.");
    let exception = s.exception.as_ref().unwrap();
    match &exception.body {
        ClauseBody::Verbal { verb, content, .. } => {
            assert_eq!(verb, "reports");
            assert!(content.is_some());
        }
        other => panic!("expected verbal exception body, got {other:?}"),
    }
    // Content inside a clause nested under an `until` role.
    let s = one(
        "While the pump runs until the monitor confirms that the tank is full, \
         the daemon shall wait.",
    );
    let state = &s.frames.states[0].clause.items[0];
    let ClauseBody::Verbal { roles, .. } = &state.body else { panic!("verbal") };
    let RolePp::Until(inner) = &roles[0] else { panic!("until role") };
    let ClauseBody::Verbal { content, .. } = &inner.body else { panic!("inner verbal") };
    assert!(content.is_some(), "content nests through clausal roles");
    roundtrip(
        "While the pump runs until the monitor confirms that the tank is full, \
         the daemon shall wait.",
    );
}

#[test]
fn clause_content_depth_is_bounded() {
    // Nested content clauses recurse; the shared depth budget keeps the
    // recognizer total instead of overflowing.
    let mut guard = String::from("the monitor confirms");
    for _ in 0..70 {
        guard.push_str(" that the monitor confirms");
    }
    guard.push_str(" that the tank is full");
    let input = format!("When {guard}, the pump shall stop.");
    assert!(matches!(
        parse(&input),
        Err(ParseError::PhraseTooDeep { .. })
    ));
}

#[test]
fn guard_content_is_identity_for_the_relation_engine() {
    // Differing content blocks Yes: the guard digests differ in their
    // content skeleton (and full render), so the guards never witness one
    // region.
    let valid = one("When the monitor ensures that the token is valid, the pump shall stop.");
    let expired =
        one("When the monitor ensures that the token is expired, the pump shall not stop.");
    assert_eq!(assess(&valid, &expired), Outcome::Unknown);
    // Equal content still meets: the same guard over contradicting claims
    // grounds a conditional contradiction.
    let stop = one("When the monitor ensures that the token is valid, the pump shall stop.");
    let no_stop =
        one("When the monitor ensures that the token is valid, the pump shall not stop.");
    assert_eq!(assess(&stop, &no_stop), Outcome::HardContradiction);
    // The skeleton digest carries the content.
    let k = skeleton(&valid).unwrap();
    let trigger = k.guards.trigger.as_ref().unwrap();
    let content = trigger.clauses[0].content.as_ref().expect("content digest");
    assert_eq!(content.clause.subject_head, "token");
    assert_eq!(content.full, "the token is valid");
}

#[test]
fn clause_content_serde_round_trip_and_old_json_loads() {
    let s = one("When the monitor ensures that the token is valid, the pump shall stop.");
    let json = serde_json::to_value(&s).unwrap();
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
    // A content-free clause serializes WITHOUT the field, so pre-round-9
    // trees and skeletons load unchanged.
    let plain = one("When the order ships, the pump shall stop.");
    let json = serde_json::to_value(&plain).unwrap();
    let body = &json["frames"]["trigger"]["clause"]["items"][0]["body"];
    assert!(body.get("content").is_none());
    let k = skeleton(&plain).unwrap();
    let cj = serde_json::to_value(k.guards.trigger.as_ref().unwrap().clauses[0].clone()).unwrap();
    assert!(cj.get("content").is_none());
}

#[test]
fn relative_bodies_stay_content_free() {
    // LEGISLATED (round 9): RelativeBody verbal arms carry NO content slot
    // in v0.2 — `that` after a relative's verbal tail is not content
    // there; the sentence is diagnosed, never silently re-read.
    assert!(parse("Each daemon that reports that the link is down shall halt.").is_err());
}

// ====================================================================================
// 5. Guard canonicalization + interval overlap witness
// ====================================================================================

#[test]
fn reordered_joint_guards_now_ground_contradictions() {
    // SUPERSEDED IN PART (round 10, change 4): the round-9 form of this
    // pin swapped the two conditions ACROSS the frame families (`Where A,
    // While B` vs `Where B, While A`); guard atoms now carry their
    // GuardRole, so the swapped pair are different condition sets and the
    // engine answers Unknown, conservatively.
    let a = one("Where the mode is manual, While the pump is running, the valve shall open.");
    let b = one("Where the pump is running, While the mode is manual, the valve shall not open.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
    // Canonicalization itself is unchanged: reordered `and` conjuncts
    // inside ONE frame family still ground.
    let a = one("While the pump is running and the mode is manual, the valve shall open.");
    let b = one("While the mode is manual and the pump is running, the valve shall not open.");
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
}

#[test]
fn overlapping_bounded_guards_witness_for_contradicting_claims() {
    // [−∞,5] ∩ [−∞,3] = [−∞,3] is provably non-empty (an interior point
    // exists), so the claims' conflict is in force somewhere: grounded.
    let a = one("While the depth is at most 5, the pump shall run.");
    let b = one("While the depth is at most 3, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
    // Overlap without containment witnesses too.
    let a = one("While the depth is between 2 and 6, the pump shall run.");
    let b = one("While the depth is between 4 and 8, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
}

#[test]
fn disjoint_bounded_guards_still_refuse_to_witness() {
    let a = one("While the depth is at most 3, the pump shall run.");
    let b = one("While the depth is at least 5, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::Unknown, "disjoint guard regions never meet");
}

#[test]
fn mixed_or_ungroundable_guard_shapes_stay_unknown() {
    // Different subjects: no witness.
    let a = one("While the depth is at most 5, the pump shall run.");
    let b = one("While the height is at most 3, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
    // Same head, different full identity (of-chain): no witness.
    let a = one("While the depth of the tank is at most 5, the pump shall run.");
    let b = one("While the depth of the sump is at most 3, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
    // Unit mismatch: no witness.
    let a = one("While the depth is at most 5 meters, the pump shall run.");
    let b = one("While the depth is at most 3, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
    // A comparison guard against a non-comparison guard: no witness.
    let a = one("While the depth is at most 5, the pump shall run.");
    let b = one("While the tank is draining, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
    // A role-bearing comparison guard is out of the witness's scope.
    let a = one("While the depth is at most 5 at the depot, the pump shall run.");
    let b = one("While the depth is at most 3 at the depot, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
}

#[test]
fn equal_guards_and_unguarded_sides_still_witness() {
    // The round-7 rules are unchanged: equal guards and Top witness.
    let a = one("While the depth is at most 5, the pump shall run.");
    let b = one("While the depth is at most 5, the pump shall not run.");
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
    let unguarded = one("The pump shall not run.");
    assert_eq!(assess(&a, &unguarded), Outcome::HardContradiction);
}

// ====================================================================================
// 6. Descending `between` is a parse error
// ====================================================================================

#[test]
fn descending_between_is_rejected_in_comparisons() {
    let err = parse("The latency is between 6 and 4.").unwrap_err();
    assert_eq!(
        err,
        ParseError::DescendingBetween { lower: "6".into(), upper: "4".into() }
    );
    assert_eq!(err.kind(), "descending_between");
    assert!(err.to_string().contains("swap"), "the message tells the author to swap");
    // Number words count too, and units do not change the check.
    assert!(matches!(
        parse("The delay is between five and three seconds."),
        Err(ParseError::DescendingBetween { .. })
    ));
    // Guards and be-complements go through the same comparison path.
    assert!(matches!(
        parse("While the reading is between 6 and 4, the pump shall stop."),
        Err(ParseError::DescendingBetween { .. })
    ));
    assert!(matches!(
        parse("The retry count shall be between 9 and 2."),
        Err(ParseError::DescendingBetween { .. })
    ));
}

#[test]
fn descending_bounded_for_measures_are_rejected_too() {
    assert!(matches!(
        parse("The daemon shall retain the log for between 30 and 10 days."),
        Err(ParseError::DescendingBetween { .. })
    ));
}

#[test]
fn equal_and_ascending_and_np_bounds_are_unaffected() {
    // Equal bounds are a point interval — fine.
    assert!(parse("The latency is between 4 and 4.").is_ok());
    assert!(parse("The daemon shall retain the log for between 5 and 5 days.").is_ok());
    // Ascending stays accepted.
    assert!(parse("The latency is between 4 and 6.").is_ok());
    // NP bounds are value names, not numbers: never checked.
    assert!(parse("The latency is between the floor and the ceiling.").is_ok());
    assert!(parse("The latency is between 6 and the ceiling.").is_ok());
    // Decimals compare numerically, not lexically.
    assert!(parse("The latency is between 2.5 and 10.5.").is_ok());
    assert!(matches!(
        parse("The latency is between 10.5 and 2.5."),
        Err(ParseError::DescendingBetween { .. })
    ));
}
