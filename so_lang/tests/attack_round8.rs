//! Adversarial conformance attack on the round-8 changes: clausal-role
//! fidelity (change 1), pairing hardening (change 2), assumption
//! satisfiability (change 3), copular role tails (change 4), positional
//! capability (change 5), and envelope compatibility (change 6).
//!
//! Every test here tries to break a round-8 guarantee: force a false `Yes`
//! through nested clauses, sneak a vacuous reliance past the gate, make a
//! satisfiability or envelope judgment say `Yes`, collide digests the new
//! tails were supposed to separate, or panic the recognizer. Passing tests
//! are permanent pins; failing expectations are `#[ignore]`d with the
//! finding title.

use so_lang::ast::*;
use so_lang::formula::{
    applicability, claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula,
    PairingError,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{
    assess, assumption_satisfiable, contradicts, envelope_compatible, implies, Outcome, Ternary,
};
use so_lang::semantics::*;

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

fn render_round_trips(s: &Sentence) {
    let rendered = s.render();
    let re = one(&rendered);
    assert_eq!(
        re.render(),
        rendered,
        "canonical render must be a fixed point"
    );
}

/// Round 11 (change 3): the satisfiability pins build their reliances with
/// an EXPLICIT selection (the whole source conditional) — a default
/// reliance is a permanent candidate now and never enters A.
fn explicit_source(kind: EdgeKind, source: &Sentence, target: &Sentence) -> AssumptionSource {
    let default = AssumptionSource::for_guarantee(kind, source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(kind, source, target, default.formula.clone())
        .unwrap()
}

// ====================================================================================
// 1. Clausal-role fidelity: no false Yes through nested clauses
// ====================================================================================

#[test]
fn until_and_after_over_the_same_nested_words_never_meet() {
    // Same nested clause, different temporal role KIND: the role kind is
    // identity, so neither implication nor contradiction may fire.
    let until = cf("The pump shall run until the valve is open.");
    let after = cf("The pump shall run after the valve is open.");
    assert_eq!(
        implies(&until, &after),
        Ternary::Unknown,
        "no false Yes across kinds"
    );
    assert_eq!(
        implies(&after, &until),
        Ternary::Unknown,
        "no false Yes across kinds"
    );
    assert_eq!(contradicts(&until, &after), Ternary::Unknown);
}

#[test]
fn nested_verbal_object_drop_is_anchored_by_the_full_render() {
    // SUPERSEDED (round 11, change 2): ClauseSkeleton no longer drops a
    // verbal body's object, so the nested DIGESTS of `exceeds the limit`
    // and `exceeds the threshold` now differ in their object digests too;
    // the round-8 `full` anchor still separates them, and the relation
    // verdicts are unchanged (Unknown, never Yes).
    let a = one("The daemon shall retry after the reading exceeds the limit.");
    let b = one("The daemon shall retry after the reading exceeds the threshold.");
    let ka = skeleton(&a).unwrap();
    let kb = skeleton(&b).unwrap();
    match (&ka.atoms[0].roles[0].value, &kb.atoms[0].roles[0].value) {
        (
            RoleValue::Clause {
                skeleton: sa,
                full: fa,
            },
            RoleValue::Clause {
                skeleton: sb,
                full: fb,
            },
        ) => {
            assert_ne!(
                sa, sb,
                "round 11: the nested digests separate in the INDEX too"
            );
            assert_eq!(sa.objects[0].head, "limit");
            assert_eq!(sb.objects[0].head, "threshold");
            assert_ne!(fa, fb, "the full render stays the lossiness anchor");
        }
        other => panic!("expected clause digests, got {other:?}"),
    }
    let (fa, fb) = (cf(a.source.as_str()), cf(b.source.as_str()));
    assert_eq!(
        implies(&fa, &fb),
        Ternary::Unknown,
        "coarse match, full mismatch: no Yes"
    );
    assert_eq!(implies(&fb, &fa), Ternary::Unknown);
    assert_eq!(contradicts(&fa, &fb), Ternary::Unknown);
}

#[test]
fn nested_role_tails_separate_nested_digests() {
    // The nested skeleton keeps its ROLES: a location inside the temporal
    // clause is identity.
    let depot = one("The daemon shall retry after the backup completes at the depot.");
    let dock = one("The daemon shall retry after the backup completes at the dock.");
    let kd = skeleton(&depot).unwrap();
    match &kd.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.roles.len(), 1);
            assert_eq!(skeleton.roles[0].kind, RoleKind::Location);
            assert_eq!(full, "the backup completes at the depot");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    let (fa, fb) = (cf(depot.source.as_str()), cf(dock.source.as_str()));
    assert_eq!(implies(&fa, &fb), Ternary::Unknown);
    assert_eq!(implies(&fb, &fa), Ternary::Unknown);
    render_round_trips(&depot);
    // Identical nested clauses WITH the role tail still meet across
    // shall/must — the richer digest must not break the true Yes.
    let must = cf("The daemon must retry after the backup completes at the depot.");
    let shall = cf("The daemon shall retry after the backup completes at the depot.");
    assert_eq!(implies(&must, &shall), Ternary::Yes);
    assert_eq!(implies(&shall, &must), Ternary::Yes);
}

#[test]
fn nested_manner_separates_nested_digests() {
    let plain = cf("The daemon shall retry after the export completes.");
    let manner = cf("The daemon shall retry after the export completes successfully.");
    assert_eq!(implies(&plain, &manner), Ternary::Unknown);
    assert_eq!(implies(&manner, &plain), Ternary::Unknown);
    assert_eq!(contradicts(&plain, &manner), Ternary::Unknown);
}

#[test]
fn nested_comparison_intervals_never_ground_across_clausal_roles() {
    // The interval hooks read Deadline/Duration MEASURE values only: a
    // comparison nested inside an until-clause must not ground implication
    // (`until at most 5` vs `until at most 7`) nor contradiction (`until at
    // most 3` vs `until at least 5`) — the temporal boundary is not the
    // claim.
    let a = cf("The pump shall run until the reading is at most 5.");
    let b = cf("The pump shall run until the reading is at most 7.");
    assert_eq!(
        implies(&a, &b),
        Ternary::Unknown,
        "no interval Yes through until"
    );
    assert_eq!(implies(&b, &a), Ternary::Unknown);
    let lo = cf("The pump shall run until the reading is at most 3.");
    let hi = cf("The pump shall run until the reading is at least 5.");
    assert_eq!(
        contradicts(&lo, &hi),
        Ternary::Unknown,
        "no interval No through until"
    );
}

#[test]
fn nested_clause_depth_bound_is_an_error_not_a_crash() {
    // 80 levels of `after` nesting: the shared depth budget must reject the
    // phrase precisely, never overflow the stack.
    let mut input = String::from("The daemon shall wait");
    for _ in 0..80 {
        input.push_str(" after the pump runs");
    }
    input.push('.');
    match parse(&input) {
        Err(ParseError::PhraseTooDeep { limit }) => assert_eq!(limit, 64),
        other => panic!("expected PhraseTooDeep, got {other:?}"),
    }
}

#[test]
fn clause_role_serde_keeps_nested_roles_and_rejects_the_old_flat_shape() {
    // Nested roles and polarity survive the JSON round trip.
    let k = skeleton(&one(
        "The pump shall run until the tank is full at the depot.",
    ))
    .unwrap();
    let j = serde_json::to_value(&k).unwrap();
    let value = &j["atoms"][0]["roles"][0]["value"];
    assert_eq!(value["kind"], "clause");
    assert_eq!(value["skeleton"]["subject_head"], "tank");
    assert_eq!(value["skeleton"]["words"], serde_json::json!(["full"]));
    assert_eq!(value["skeleton"]["roles"][0]["kind"], "location");
    assert_eq!(value["full"], "the tank is full at the depot");
    let back: Skeleton = serde_json::from_value(j).unwrap();
    assert_eq!(back, k);
    // The round-3 flat shape has NO migration path (documented): it must
    // fail to load, never silently produce an empty nested skeleton.
    let old = serde_json::json!({
        "kind": "clause",
        "subject_head": "backup",
        "words": ["completes"],
    });
    assert!(
        serde_json::from_value::<RoleValue>(old).is_err(),
        "the pre-round-8 flat clause digest must not deserialize"
    );
}

// ====================================================================================
// 2. Pairing hardening
// ====================================================================================

#[test]
fn provably_unsupported_relied_is_rejected_not_marked_unproven() {
    // The proven-flag truth table's No row: implies == No is a REJECTION
    // (SourceDoesNotSupportRelied), never an accepted proven=false source.
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall forward the packet.");
    let denial = claim_formula(&one("The gateway shall not forward the packet.")).unwrap();
    let err = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        denial,
    )
    .unwrap_err();
    assert_eq!(err, PairingError::SourceDoesNotSupportRelied);
}

#[test]
fn vacuity_gate_fires_before_the_support_check() {
    // A relied that both simplifies to Bottom AND is unsupported must be
    // diagnosed as VACUOUS: the erasure argument is the sharper doctrine.
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall forward the packet.");
    let relied = Formula::And {
        items: vec![
            claim_formula(&one("The relay shall close.")).unwrap(),
            Formula::Bottom,
        ],
    };
    let err = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        relied,
    )
    .unwrap_err();
    assert_eq!(err, PairingError::VacuousRelied);
}

#[test]
fn weakened_relied_is_proven_and_envelope_defaults_are_proven() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall forward the packet.");
    // Relying on a disjunction the source formula is one arm of: provable
    // weakening, so proven = true.
    let relied = Formula::Or {
        items: vec![
            claim_formula(&source).unwrap(),
            claim_formula(&one("The relay shall close.")).unwrap(),
        ],
    };
    let s = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        relied,
    )
    .unwrap();
    assert!(s.proven, "a provable weakening is a proven reliance");
    // The default-relied envelope constructor is self-entailment too.
    let env = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
    )
    .unwrap();
    assert!(env.proven);
}

#[test]
fn pre_round7_json_without_relied_or_proven_loads_with_the_defaults() {
    // Old JSON has NEITHER `relied` (round 7) nor `proven` (round 8): the
    // reliance defaults to the source formula and the flag to UNPROVEN —
    // deserialization restores, it never judges.
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    let s =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let mut json = serde_json::to_value(&s).unwrap();
    let obj = json.as_object_mut().unwrap();
    obj.remove("relied");
    obj.remove("proven");
    let back: AssumptionSource = serde_json::from_value(json).unwrap();
    assert_eq!(
        back.relied, back.formula,
        "relied defaults to the source formula"
    );
    assert!(!back.proven, "pre-round-8 sources load unproven");
}

// ====================================================================================
// 3. Assumption satisfiability
// ====================================================================================

#[test]
fn duration_interval_emptiness_across_reliances_is_unsatisfiable() {
    // Two individually valid duration reliances whose intervals share no
    // point: `for at least 30 days` ∧ `for less than 10 days`.
    let target = one("The auditor shall review the log.");
    let a = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The archive daemon shall retain the log for at least 30 days."),
        &target,
    );
    let b = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The archive daemon shall retain the log for less than 10 days."),
        &target,
    );
    let paired = contract_formula(&target).unwrap().paired(&[a, b]);
    assert_eq!(assumption_satisfiable(&paired), Ternary::No);
}

#[test]
fn comparison_interval_emptiness_across_state_reliances_is_unsatisfiable() {
    // Two described states over one measured subject: `at least 5` ∧
    // `at most 3` over the queue depth is provably empty.
    let target = one("The operator shall balance the load.");
    let a = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth of the broker is at least 5."),
        &target,
    );
    let b = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth of the broker is at most 3."),
        &target,
    );
    let paired = contract_formula(&target).unwrap().paired(&[a, b]);
    assert_eq!(assumption_satisfiable(&paired), Ternary::No);
}

#[test]
fn a_relied_guard_against_its_own_negation_is_unsatisfiable() {
    // "Guards provably empty by shape": a reliance whose relied formula
    // conjoins a guard atom with its own negation (the g ∧ ¬g shape).
    let target = one("The auditor shall review the log.");
    let source = one("While the breaker is open, the gateway shall halt.");
    let g = applicability(&source);
    let mut s =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    s.relied = Formula::And {
        items: vec![g.clone(), Formula::Not { inner: Box::new(g) }],
    };
    // SUPERSEDED PIN (round 9, recorded): this fixture used to set
    // `proven = false`, and the old `paired`/`assumption_satisfiable`
    // still conjoined and judged the unproven reliance. Pairing is now
    // proven-only — an unproven source is a candidate that never enters A
    // — so the fixture declares its hand-built reliance proven to keep
    // exercising the g ∧ ¬g emptiness rule on a contract-forming edge.
    s.proven = true;
    // Round 11 (change 3): contract forming additionally requires the
    // explicit selection; the hand-built fixture declares it.
    s.explicit_relied = true;
    let paired = contract_formula(&target).unwrap().paired(&[s]);
    assert_eq!(assumption_satisfiable(&paired), Ternary::No);
}

#[test]
fn hand_built_bottom_assumption_is_unsatisfiable() {
    // A contract whose assumption was set directly (no sources) is judged
    // over that formula.
    let target = one("The auditor shall review the log.");
    let mut c = contract_formula(&target).unwrap();
    c.assumption = Formula::Bottom;
    assert_eq!(assumption_satisfiable(&c), Ternary::No);
}

#[test]
fn satisfiable_is_never_yes_even_for_the_trivial_assumption() {
    // ASYMMETRY DOCTRINE: the good case is Unknown everywhere — the ingest
    // contract (assumption ⊤), a single reliance, and a hand-built Top.
    let target = one("The auditor shall review the log.");
    let c = contract_formula(&target).unwrap();
    assert_eq!(assumption_satisfiable(&c), Ternary::Unknown);
    let reliance = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The gateway shall forward the packet."),
        &target,
    )
    .unwrap();
    assert_eq!(
        assumption_satisfiable(&c.paired(&[reliance])),
        Ternary::Unknown
    );
    let mut top = contract_formula(&target).unwrap();
    top.assumption = Formula::Top;
    assert_eq!(assumption_satisfiable(&top), Ternary::Unknown);
}

// ====================================================================================
// 4. Copular role tails in clauses, relatives, and content
// ====================================================================================

#[test]
fn until_tail_inside_a_while_guard_is_structured() {
    let s = one("While the pump is active until the tank is full, the daemon shall wait.");
    let k = skeleton(&s).unwrap();
    let guard = &k.guards.states[0];
    assert_eq!(guard.words, vec!["active"]);
    assert_eq!(guard.roles.len(), 1);
    assert_eq!(guard.roles[0].kind, RoleKind::Until);
    match &guard.roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.subject_head, "tank");
            assert_eq!(skeleton.words, vec!["full"]);
            assert_eq!(full, "the tank is full");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn if_and_where_guards_carry_role_tails() {
    let s = one("If the breaker is open at the depot, then the daemon shall halt.");
    let k = skeleton(&s).unwrap();
    let trigger = k.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Contingency);
    assert_eq!(trigger.clauses[0].words, vec!["open"]);
    assert_eq!(trigger.clauses[0].roles[0].kind, RoleKind::Location);
    render_round_trips(&s);
    let s = one("Where the cluster is deployed in the west region, the daemon shall replicate.");
    let k = skeleton(&s).unwrap();
    assert_eq!(k.guards.scopes[0].words, vec!["deployed"]);
    assert_eq!(k.guards.scopes[0].roles[0].kind, RoleKind::Location);
    render_round_trips(&s);
}

#[test]
fn by_in_a_verbal_guard_tail_stays_rejected() {
    // The round-8 tail admits `by` in COPULAR bodies only (a passive
    // site); an active verbal guard keeps the round-5 rejection.
    assert_eq!(
        parse(
            "When the daemon stores the record by the archive, the auditor shall sign the record."
        ),
        Err(ParseError::ByOutsidePassive)
    );
}

#[test]
fn relative_until_tail_stops_at_the_enclosing_modal() {
    let s = one("Each request that is valid until the session expires shall be logged.");
    match &s.core {
        Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } => match &np.relative.as_ref().unwrap().body {
            RelativeBody::Copular {
                predicate, roles, ..
            } => {
                assert_eq!(
                    predicate,
                    &Predicate::Words {
                        words: vec!["valid".into()]
                    }
                );
                assert!(matches!(roles.as_slice(), [RolePp::Until(_)]));
            }
            other => panic!("expected copular relative with until, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    let k = skeleton(&s).unwrap();
    assert_eq!(
        k.subject.full,
        "request that is valid until the session expires"
    );
    render_round_trips(&s);
}

#[test]
fn copular_relative_late_by_is_the_agent_role() {
    // `by` after a role in the relative's tail: the Agent ROLE, per the
    // round-5 passive rules mirrored into relatives.
    let s = one("Each record that is stored in the archive by the daemon shall be retained.");
    match &s.core {
        Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } => match &np.relative.as_ref().unwrap().body {
            RelativeBody::Copular { agent, roles, .. } => {
                assert!(
                    agent.is_none(),
                    "the late `by` is a role, not the agent slot"
                );
                assert!(matches!(
                    roles.as_slice(),
                    [RolePp::Location { .. }, RolePp::Agent(_)]
                ));
            }
            other => panic!("expected copular relative, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    let k = skeleton(&s).unwrap();
    assert_eq!(
        k.subject.full,
        "record that is stored in the archive by the daemon"
    );
    render_round_trips(&s);
}

#[test]
fn content_clauses_carry_structured_locations_and_untils() {
    let s = one("The system shall ensure that the pump is active at the depot.");
    let k = skeleton(&s).unwrap();
    let content = k.atoms[0].content.as_ref().unwrap();
    assert_eq!(content.clause.words, vec!["active"]);
    assert_eq!(content.clause.roles[0].kind, RoleKind::Location);
    assert_eq!(content.full, "the pump is active at the depot");
    render_round_trips(&s);
    let s = one("The system shall verify that the token is valid until the session expires.");
    let k = skeleton(&s).unwrap();
    let content = k.atoms[0].content.as_ref().unwrap();
    assert_eq!(content.clause.roles[0].kind, RoleKind::Until);
    render_round_trips(&s);
}

#[test]
fn inner_content_deadlines_never_ground_but_outer_deadlines_do() {
    // Attachment stays INNER (documented): a deadline inside the content
    // clause is content identity, so no interval hook may reach it —
    // while the roles-first outer spelling grounds containment as always.
    let i5 = cf("The system shall verify that the token is valid within 5 seconds.");
    let i10 = cf("The system shall verify that the token is valid within 10 seconds.");
    assert_eq!(
        implies(&i5, &i10),
        Ternary::Unknown,
        "inner deadlines are content identity"
    );
    assert_eq!(implies(&i10, &i5), Ternary::Unknown);
    let o5 = cf("The system shall verify within 5 seconds that the token is valid.");
    let o10 = cf("The system shall verify within 10 seconds that the token is valid.");
    assert_eq!(
        implies(&o5, &o10),
        Ternary::Yes,
        "outer deadlines ground containment"
    );
    assert_eq!(implies(&o10, &o5), Ternary::Unknown);
}

#[test]
fn description_passive_with_deadline_meets_the_deontic_passive() {
    // Round 5 promised the described passive and the deontic passive meet
    // at one atom; round 8 structured the deontic (and clause/relative)
    // tails but at first left the description core swallowing the tail
    // into the agent noun phrase (agent head `seconds`, full `daemon
    // within 5 seconds`) — an accepted-but-wrong tree of exactly the
    // family ForRequiresMeasure/WithIsAmbiguous/ByOutsidePassive were
    // added to prevent. FIXED (round 8 follow-up): the description's
    // agent phrase is collected in verb-phrase context and a structured
    // role tail follows it, so both spellings digest [Agent daemon,
    // Deadline 5 seconds].
    let described = skeleton(&one(
        "The request is logged by the daemon within 5 seconds.",
    ))
    .unwrap();
    let obliged = skeleton(&one(
        "The request shall be logged by the daemon within 5 seconds.",
    ))
    .unwrap();
    assert_eq!(described.atoms[0], obliged.atoms[0]);
    render_round_trips(&one(
        "The request is logged by the daemon within 5 seconds.",
    ));
}

// ====================================================================================
// 5. Positional capability
// ====================================================================================

#[test]
fn able_to_reaches_exceptions_and_until_clauses() {
    // The exception is a clause position: the capability parses there too.
    let s = one("The pump shall stop, unless the client is able to retry.");
    let k = skeleton(&s).unwrap();
    let exception = k.exception.as_ref().unwrap();
    assert_eq!(exception.words, vec!["able", "to", "retry"]);
    render_round_trips(&s);
    // And inside a clausal role value.
    let s = one("The pump shall run until the client is able to retry.");
    let k = skeleton(&s).unwrap();
    match &k.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.words, vec!["able", "to", "retry"]);
            assert_eq!(full, "the client is able to retry");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn able_to_guard_roles_meet_the_description_atom_roles() {
    // The guard digest carries the capability vp's roles structurally, so a
    // guard and a capability description share role digests exactly.
    let s = one("While the client is able to publish to the topic, the pump shall run.");
    let k = skeleton(&s).unwrap();
    let guard = &k.guards.states[0];
    assert_eq!(guard.words, vec!["able", "to", "publish"]);
    let d = skeleton(&one("The client is able to publish to the topic.")).unwrap();
    assert_eq!(d.atoms[0].words, vec!["publish"]);
    assert_eq!(
        d.atoms[0].roles, guard.roles,
        "description and guard meet on roles"
    );
    render_round_trips(&s);
}

#[test]
fn differing_able_to_guard_objects_do_not_witness_overlap() {
    // UPDATED (round 12, change 6 — supersedes the round-8 pin that
    // asserted the digest COLLISION): capability clause bodies now carry
    // their verb phrase's object digests, so the lock and token guards
    // differ in the INDEX itself, not only in the lossless render anchor.
    // The assess() outcome is unchanged — no shared-region witness, no
    // false HardContradiction.
    let a = one("While the client is able to hold the lock, the gateway shall throttle the queue.");
    let b = one(
        "While the client is able to hold the token, the gateway shall not throttle the queue.",
    );
    let ka = skeleton(&a).unwrap();
    let kb = skeleton(&b).unwrap();
    assert_ne!(
        ka.guards.states[0], kb.guards.states[0],
        "the digests separate now (round 12: capability objects digest)"
    );
    assert_eq!(ka.guards.states[0].objects[0].head, "lock");
    assert_eq!(kb.guards.states[0].objects[0].head, "token");
    assert_eq!(
        assess(&a, &b),
        Outcome::Unknown,
        "still no manufactured witness"
    );
}

#[test]
fn able_to_guards_ground_a_deadline_refinement() {
    // A concrete implies-hit through a capability guard: one written
    // able-to guard scopes both sides, the claims differ in one contained
    // deadline interval.
    let concrete =
        one("While the client is able to retry, the gateway shall stop within 5 seconds.");
    let abstract_ =
        one("While the client is able to retry, the gateway shall stop within 10 seconds.");
    assert_eq!(
        assess(&concrete, &abstract_),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
    assert_eq!(
        assess(&abstract_, &concrete),
        Outcome::Refinement {
            concrete_is_a: false
        }
    );
}

#[test]
fn adverbed_able_to_stays_flat_in_clauses_and_relatives() {
    // Legislated: bare able-to only in clause/relative position. With an
    // adverb the words fall back to ordinary predicate material. Round-8
    // FINDING, fixed: the predicate used to keep only `always able` and
    // hand `to retry` to the role grammar as a Recipient over a verb — an
    // accepted-but-wrong tree. Predicate collection now resumes flat past
    // the `to` of a trailing `able`, so ALL the words stay predicate
    // material, exactly as the legislation reads.
    let flat = Predicate::Words {
        words: vec!["always".into(), "able".into(), "to".into(), "retry".into()],
    };
    let s = one("While the client is always able to retry, the pump shall run.");
    match &s.frames.states[0].clause.items[0].body {
        ClauseBody::Copular {
            predicate, roles, ..
        } => {
            assert_eq!(predicate, &flat);
            assert!(roles.is_empty(), "no role is carved out of the flat tail");
        }
        other => panic!("expected flat copular body, got {other:?}"),
    }
    render_round_trips(&s);
    let s = one("Each client that is always able to retry shall register.");
    match &s.core {
        Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } => match &np.relative.as_ref().unwrap().body {
            RelativeBody::Copular {
                predicate, roles, ..
            } => {
                assert_eq!(predicate, &flat);
                assert!(roles.is_empty(), "no role is carved out of the flat tail");
            }
            other => panic!("expected flat copular relative, got {other:?}"),
        },
        other => panic!("expected deontic, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn able_to_is_not_a_passive_site() {
    // The capability vp keeps the round-5 agent rule: no `by` role outside
    // a passive site, in guard position included.
    assert_eq!(
        parse("While the client is able to retry by the user, the pump shall run."),
        Err(ParseError::ByOutsidePassive)
    );
}

// ====================================================================================
// 6. Envelope compatibility
// ====================================================================================

#[test]
fn universal_subject_envelope_violation_is_no() {
    let target = one("Each client shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("Each client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

#[test]
fn guarded_envelope_against_an_unguarded_prohibition_is_no() {
    // The prohibition holds everywhere (Top guard), so the envelope's own
    // region is inside it: a violation wherever the envelope admits.
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("While the breaker is open, the client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

#[test]
fn differing_guards_stay_unknown() {
    let target = one("While the breaker is closed, the client shall not retry.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("While the breaker is open, the client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

#[test]
fn an_empty_guard_region_never_witnesses_a_violation() {
    // A prohibition whose applicability is provably empty (trigger equal to
    // its own exception) asserts nothing anywhere: no violation provable.
    let target =
        one("When the breaker is open, the client shall not retry, unless the breaker is open.");
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

#[test]
fn obligations_recommendations_and_count_admissions_stay_unknown() {
    let envelope = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
    )
    .unwrap();
    // An obligation of the admitted behavior: compatible in fact, but
    // compatibility is never provable — Unknown, not Yes.
    let target = one("The client shall retry.");
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // A merely recommended prohibition does not bound.
    let target = one("The client should not retry.");
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // A count-subject admission never grounds (witness-set argument).
    let target = one("The clients shall not retry.");
    let counted = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("At least 3 clients may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[counted]);
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

#[test]
fn one_violated_envelope_among_several_is_no() {
    let target = one("The client shall not retry.");
    let unrelated = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The gateway may compress the payload."),
    )
    .unwrap();
    let violated = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
    )
    .unwrap();
    let paired = contract_formula(&target)
        .unwrap()
        .paired(&[unrelated, violated]);
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

#[test]
fn the_edge_kind_gates_the_envelope_check_not_the_formula_shape() {
    // A hand-built NON-envelope source carrying the very admissibility
    // formula must be skipped: the kind is the gate.
    let target = one("The client shall not retry.");
    let admitted = claim_formula(&one("The client may retry.")).unwrap();
    let reliance = AssumptionSource {
        kind: EdgeKind::OccurrenceReliance,
        formula: admitted.clone(),
        relied: admitted.clone(),
        act: SpeechAct::Permission,
        force: None,
        proven: true,
        subject_relation: so_lang::formula::SubjectRelation::DisjointKeys,
        // Round 11, change 3: hand-built fixture — explicitness is not
        // what this pin tests.
        explicit_relied: true,
    };
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&reliance));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
    // The same formula under the envelope kind IS the violation.
    let envelope = AssumptionSource {
        kind: EdgeKind::AdmissibilityEnvelope,
        ..reliance
    };
    let paired = contract_formula(&target).unwrap().paired(&[envelope]);
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

// ====================================================================================
// 7. Totality: seeded fuzz over the round-8 surface
// ====================================================================================

#[test]
fn seeded_fuzz_over_round8_shapes_never_panics() {
    let frames = [
        "",
        "While the client is able to retry, ",
        "While the pump is active at the depot, ",
        "While the pump remains active at the depot, ",
        "When the record is stored in the archive by the daemon, ",
        "If the breaker is open at the depot, then ",
    ];
    let subjects = [
        "The daemon",
        "Each request that is signed by the user",
        "No client",
        "At least 3 replicas",
        "The owner of the file",
    ];
    let cores = [
        "shall retry",
        "shall not retry",
        "may retry",
        "is able to retry",
        "shall purge the cache after no backup completes",
        "shall run until the tank is full at the depot",
        "shall verify that the token is valid within 5 seconds",
        "shall be logged by the daemon within 5 seconds",
        "is active at the depot",
    ];
    let tails = [
        "",
        ", unless the override is active on the console",
        ", so that the operator retains control",
    ];
    let mut parsed: Vec<Sentence> = Vec::new();
    for frame in frames {
        for subject in subjects {
            for core in cores {
                for tail in tails {
                    let input = format!("{frame}{subject} {core}{tail}.");
                    let Ok(spec) = parse(&input) else {
                        continue; // a precise rejection is a fine outcome
                    };
                    for sentence in spec.sentences {
                        let rendered = sentence.render();
                        let re = parse(&rendered).unwrap_or_else(|e| {
                            panic!("canonical render of {input:?} does not re-parse: {e}")
                        });
                        assert_eq!(
                            re.sentences[0].render(),
                            rendered,
                            "render fixed point violated for {input:?}"
                        );
                        let _ = claim_formula(&sentence);
                        let _ = contract_formula(&sentence);
                        if let Some(k) = skeleton(&sentence) {
                            let j = serde_json::to_value(&k).unwrap();
                            let back: Skeleton = serde_json::from_value(j).unwrap();
                            assert_eq!(back, k);
                        }
                        parsed.push(sentence);
                    }
                }
            }
        }
    }
    assert!(
        parsed.len() > 300,
        "the corpus must actually exercise the grammar"
    );
    // Seeded pair sampling: assess must be total over every parsed pair.
    let mut state: u64 = 0x5DEECE66D;
    let mut next = |m: usize| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 33) as usize) % m
    };
    for _ in 0..500 {
        let a = &parsed[next(parsed.len())];
        let b = &parsed[next(parsed.len())];
        let _ = assess(a, b);
    }
}
