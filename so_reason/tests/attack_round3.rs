//! Adversarial conformance attack on the round-3 changes (IMPROVE-SPEC-3).
//!
//! Object under test: the code in `so_lang/src` after round 3 —
//!
//! 1. clause verbal bodies carry thematic roles (every `RolePp` kind, in
//!    every clause site: `When`/`While`/`Where`/`If`/`unless`/purpose/
//!    definiens), nested `before`/`after` clauses bounded by the shared
//!    depth budget, roles inside coordinated clause groups, render
//!    round-trips;
//! 2. the sequence pattern (`the payment clears after the order ships`) and
//!    its or-group variants; `After`/`Before` digests in guard skeletons;
//! 3. particle verbs: the closed list (`out`, `down`, `up`, `off`), with and
//!    without objects, with deadlines, inside frame clauses, the `out of`
//!    legislation, particle words as ordinary NP material once an object
//!    precedes them, hyphenated verbs, casing;
//! 4. skeleton v3: object quantifiers for every `Det`, `any` legislated
//!    universal everywhere, `log no request` vs `log the request`,
//!    `RoleValue::Heads` quantifiers, coordination items, serde wire shapes;
//! 5. the formula layer: applicability shapes, exception negation placement,
//!    conditional guarantee `Or(Not(app), claim)`, `saturated()` =
//!    `Or(guarantee, Not(assumption))`, permission/definition `None`,
//!    negative-claim `Not` placement, JSON round trips;
//! 6. totality: a seeded fuzz mixing particles, roles, and clause groups.
//!
//! Every test pins behavior the round-3 spec legislates, or probes an edge
//! the spec left to the implementation (those pins say so). Tests that fail
//! are marked `#[ignore]` with the finding title.

use so_lang::ast::*;
use so_lang::parse::{parse, ParseError};
use so_reason::formula::{
    applicability, claim_formula, contract_formula, AtomRef, ContractFormula, Formula,
};
use so_reason::semantics::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

// ---- helpers ----------------------------------------------------------------------

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("expected {input:?} to parse, got {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn sk(input: &str) -> Skeleton {
    skeleton(&one(input)).unwrap_or_else(|| panic!("expected a skeleton for {input:?}"))
}

/// Render must be a fixpoint that re-parses to the same tree. The input must
/// already use canonical frame-keyword casing (render emits `Where`/`While`/
/// `When`/`If` in title case regardless of the surface).
fn roundtrip(input: &str) {
    let s = one(input);
    let rendered = s.render();
    let r = one(&rendered);
    assert_eq!(
        (&s.frames, &s.core, &s.exception, &s.purpose),
        (&r.frames, &r.core, &r.exception, &r.purpose),
        "render {rendered:?} of {input:?} must re-parse to the same tree"
    );
    assert_eq!(
        r.render(),
        rendered,
        "render must be a fixpoint for {input:?}"
    );
}

fn verbal(body: &ClauseBody) -> (&str, Option<&str>, &Option<NpGroup>, &[RolePp]) {
    match body {
        ClauseBody::Verbal {
            verb,
            particle,
            object,
            roles,
            ..
        } => (verb.as_str(), particle.as_deref(), object, roles.as_slice()),
        other => panic!("expected verbal clause body, got {other:?}"),
    }
}

fn deontic_vp(s: &Sentence) -> &Vp {
    match &s.core {
        Core::Deontic { vp, .. } => vp.single().expect("single vp fixture"),
        other => panic!("expected deontic core, got {other:?}"),
    }
}

fn guard_head(formula: &Formula) -> &str {
    match formula {
        Formula::Atom {
            atom: AtomRef::Guard { clause, .. },
        } => clause.subject_head.as_str(),
        other => panic!("expected guard atom, got {other:?}"),
    }
}

fn json<T: serde::Serialize + serde::de::DeserializeOwned + PartialEq + std::fmt::Debug>(
    value: &T,
) -> serde_json::Value {
    let json = serde_json::to_value(value)
        .unwrap_or_else(|e| panic!("must serialize, got {e} for {value:?}"));
    let back: T = serde_json::from_value(json.clone())
        .unwrap_or_else(|e| panic!("must deserialize, got {e} from {json}"));
    assert_eq!(&back, value, "JSON round trip must be lossless");
    json
}

// ====================================================================================
// 1. Clause roles: every RolePp kind, in every clause site
// ====================================================================================

#[test]
fn when_clause_carries_topic_role() {
    let s = one("When the monitor warns about the disk, the daemon shall alert.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let (verb, particle, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "warns");
    assert_eq!(particle, None);
    assert!(object.is_none());
    assert!(matches!(&roles[0], RolePp::Topic(np) if np.heads() == vec!["disk"]));
    roundtrip("When the monitor warns about the disk, the daemon shall alert.");
}

#[test]
fn while_clause_carries_recipient_means_source_deadline() {
    let input = "While the relay sends the digest to the auditor using the key \
                 from the depot within 5 seconds, the daemon shall wait.";
    let s = one(input);
    let clause = &s.frames.states[0].clause.items[0];
    let (verb, _, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "sends");
    assert_eq!(object.as_ref().unwrap().heads(), vec!["digest"]);
    assert!(matches!(&roles[0], RolePp::Recipient(np) if np.heads() == vec!["auditor"]));
    assert!(matches!(
        &roles[1],
        RolePp::Means { marker: MeansMarker::Using, np } if np.heads() == vec!["key"]
    ));
    assert!(matches!(&roles[2], RolePp::Source(np) if np.heads() == vec!["depot"]));
    assert!(matches!(
        &roles[3],
        RolePp::Deadline(Measure::Quantity { number, unit })
            if number == "5" && unit.as_deref() == Some("seconds")
    ));
    roundtrip(input);
}

#[test]
fn where_clause_carries_rate_and_duration_roles() {
    let input = "Where the meter samples per second for 30 seconds, the daemon shall wait.";
    let s = one(input);
    let clause = &s.frames.scopes[0].clause.items[0];
    let (verb, _, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "samples");
    assert!(object.is_none());
    assert!(matches!(&roles[0], RolePp::Rate { unit } if unit == "second"));
    assert!(matches!(
        &roles[1],
        RolePp::Duration(Measure::Quantity { number, unit })
            if number == "30" && unit.as_deref() == Some("seconds")
    ));
    roundtrip(input);
}

#[test]
fn if_clause_carries_source_and_goal_roles() {
    let input =
        "If the archiver moves the log from the disk into the vault, then the daemon shall alert.";
    let s = one(input);
    let trigger = s.frames.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Contingency);
    let (verb, _, object, roles) = verbal(&trigger.clause.items[0].body);
    assert_eq!(verb, "moves");
    assert_eq!(object.as_ref().unwrap().heads(), vec!["log"]);
    assert!(matches!(&roles[0], RolePp::Source(np) if np.heads() == vec!["disk"]));
    assert!(matches!(&roles[1], RolePp::Goal(np) if np.heads() == vec!["vault"]));
    roundtrip(input);
}

#[test]
fn unless_clause_carries_recipient_and_deadline_roles() {
    let input =
        "The daemon shall wait, unless the relay sends the alarm to the operator within 5 seconds.";
    let s = one(input);
    let (verb, _, object, roles) = verbal(&s.exception.as_ref().unwrap().body);
    assert_eq!(verb, "sends");
    assert_eq!(object.as_ref().unwrap().heads(), vec!["alarm"]);
    assert!(matches!(&roles[0], RolePp::Recipient(np) if np.heads() == vec!["operator"]));
    assert!(
        matches!(&roles[1], RolePp::Deadline(Measure::Quantity { number, .. }) if number == "5")
    );
    roundtrip(input);
}

#[test]
fn clause_location_role_covers_every_locative_preposition() {
    for prep in ["in", "on", "at", "under", "over", "above", "below"] {
        let input = format!("While the sensor sits {prep} the rack, the daemon shall wait.");
        let s = one(&input);
        let clause = &s.frames.states[0].clause.items[0];
        let (verb, _, object, roles) = verbal(&clause.body);
        assert_eq!(verb, "sits", "verb of {input:?}");
        assert!(object.is_none());
        match &roles[0] {
            RolePp::Location { preposition, np } => {
                assert_eq!(preposition, prep);
                assert_eq!(np.heads(), vec!["rack"]);
            }
            other => panic!("expected location role in {input:?}, got {other:?}"),
        }
        roundtrip(&input);
    }
}

#[test]
fn clause_at_lookahead_keeps_at_least_out_of_location() {
    // `at least`/`at most` after a clause verb stay the quantifier path (an
    // object with a count determiner), never a Location role.
    let s = one("When the pool holds at least 3 workers, the daemon shall wait.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let (verb, _, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "holds");
    assert!(roles.is_empty());
    match object.as_ref().unwrap() {
        NpGroup::Single(np) => {
            assert_eq!(np.det, Some(Det::AtLeast { n: 3 }));
            assert_eq!(np.head, "workers");
        }
        other => panic!("expected single object, got {other:?}"),
    }
    roundtrip("When the pool holds at least 3 workers, the daemon shall wait.");
}

#[test]
fn when_clause_carries_before_role() {
    let input =
        "When the guard locks the door before the shift ends, the daemon shall log the event.";
    let s = one(input);
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let (verb, _, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "locks");
    assert_eq!(object.as_ref().unwrap().heads(), vec!["door"]);
    match &roles[0] {
        RolePp::Before(before) => {
            assert_eq!(before.subject.heads(), vec!["shift"]);
            let (verb, _, object, roles) = verbal(&before.body);
            assert_eq!(verb, "ends");
            assert!(object.is_none());
            assert!(roles.is_empty());
        }
        other => panic!("expected Before role, got {other:?}"),
    }
    roundtrip(input);
}

#[test]
fn clause_roles_inside_coordinated_clause_groups() {
    // Roles on both items of an `or` group.
    let input = "While the pump runs at the depot or the valve drains into the tank, \
                 the daemon shall wait.";
    let s = one(input);
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::Or));
    assert_eq!(group.items.len(), 2);
    let (_, _, _, roles0) = verbal(&group.items[0].body);
    assert!(matches!(&roles0[0], RolePp::Location { preposition, .. } if preposition == "at"));
    let (_, _, _, roles1) = verbal(&group.items[1].body);
    assert!(matches!(&roles1[0], RolePp::Goal(np) if np.heads() == vec!["tank"]));
    roundtrip(input);

    // Roles on both items of an `and` state group (While is unrestricted).
    let input = "While the pump runs at the depot and the valve drains into the tank, \
                 the daemon shall wait.";
    let s = one(input);
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 2);
    roundtrip(input);
}

#[test]
fn definiens_clause_carries_particle_and_location_role() {
    let input = "A handoff means that the operator signs off at the console.";
    let s = one(input);
    match &s.core {
        Core::Definition {
            definiens: Definiens::Clause(clause),
            ..
        } => {
            let (verb, particle, object, roles) = verbal(&clause.body);
            assert_eq!(verb, "signs");
            assert_eq!(particle, Some("off"));
            assert!(object.is_none());
            assert!(matches!(
                &roles[0],
                RolePp::Location { preposition, np }
                    if preposition == "at" && np.heads() == vec!["console"]
            ));
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
    roundtrip(input);
}

#[test]
fn purpose_clause_carries_after_role() {
    let input = "The daemon shall flush, so that the archive closes after the batch completes.";
    let s = one(input);
    match &s.purpose {
        Some(Purpose::SoThat(clause)) => {
            let (verb, _, _, roles) = verbal(&clause.body);
            assert_eq!(verb, "closes");
            assert!(matches!(&roles[0], RolePp::After(after)
                if after.subject.heads() == vec!["batch"]));
        }
        other => panic!("expected so-that purpose, got {other:?}"),
    }
    roundtrip(input);
}

#[test]
fn np_first_verbal_subject_still_reaches_clause_roles() {
    // A structured subject (of-chain) takes the noun-phrase-first path; the
    // verbal tail must still carry particle and roles.
    let s = one("When the owner of the file logs out, the session shall end.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    match &clause.subject {
        NpGroup::Single(np) => {
            assert_eq!(np.head, "owner");
            assert_eq!(np.of.as_ref().unwrap().head, "file");
        }
        other => panic!("expected single subject, got {other:?}"),
    }
    let (verb, particle, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "logs");
    assert_eq!(particle, Some("out"));
    assert!(object.is_none());
    assert!(roles.is_empty());
    roundtrip("When the owner of the file logs out, the session shall end.");
}

#[test]
fn copular_clause_keeps_locatives_in_the_predicate() {
    // SUPERSEDED PIN (round 8, change 4): round 3 gave roles to VERBAL
    // clause bodies only, so a copular clause kept trailing locative
    // material as flat predicate words — `active at the depot` — hiding
    // the location from the guard skeleton. Copular bodies now carry the
    // same thematic-role tail, so the locative is a structured Location
    // role on the predicate.
    let s = one("While the pump is active at the depot, the daemon shall wait.");
    match &s.frames.states[0].clause.items[0].body {
        ClauseBody::Copular {
            predicate: Predicate::Words { words },
            roles,
            ..
        } => {
            assert_eq!(words, &["active"]);
            match roles.as_slice() {
                [RolePp::Location { preposition, np }] => {
                    assert_eq!(preposition, "at");
                    assert_eq!(np.heads(), vec!["depot"]);
                }
                other => panic!("expected one Location role, got {other:?}"),
            }
        }
        other => panic!("expected words predicate with a role tail, got {other:?}"),
    }
    roundtrip("While the pump is active at the depot, the daemon shall wait.");
}

// ---- depth: nested before/after against the recursion bound -----------------------

/// A trigger clause with `n` nested `after` clauses.
fn nested_after_sentence(n: usize) -> String {
    format!(
        "When the pump runs{}, the system shall stop.",
        " after the pump runs".repeat(n)
    )
}

#[test]
fn nested_after_at_the_depth_limit_is_phrase_too_deep_not_a_crash() {
    // The shared budget is MAX_NP_DEPTH = 64; each `after` nests one clause.
    // 64 levels must be the precise error, never an abort.
    let outcome = catch_unwind(AssertUnwindSafe(|| parse(&nested_after_sentence(64))));
    assert_eq!(
        outcome.expect("parse must not panic at the depth limit"),
        Err(ParseError::PhraseTooDeep { limit: 64 })
    );
}

#[test]
fn nested_after_just_under_the_depth_limit_parses() {
    let input = nested_after_sentence(63);
    let s = one(&input);
    // Walk to the innermost clause: 63 After links.
    let mut clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let mut depth = 0;
    loop {
        let (verb, _, _, roles) = verbal(&clause.body);
        assert_eq!(verb, "runs");
        match roles.first() {
            Some(RolePp::After(inner)) => {
                depth += 1;
                clause = inner;
            }
            None => break,
            other => panic!("expected After role, got {other:?}"),
        }
    }
    assert_eq!(depth, 63);
}

#[test]
fn nested_after_in_exception_definiens_and_purpose_hits_the_bound() {
    let tail = " after the pump runs".repeat(70);
    for input in [
        format!("The pump shall stop, unless the pump runs{tail}."),
        format!("A cascade means that the pump runs{tail}."),
        format!("The pump shall stop, so that the pump rests{tail}."),
        // Depth through a VP role, not a clause.
        format!("The pump shall rest{tail}."),
    ] {
        let outcome = catch_unwind(AssertUnwindSafe(|| parse(&input)));
        assert_eq!(
            outcome.unwrap_or_else(|_| panic!("parse panicked on {input:?}")),
            Err(ParseError::PhraseTooDeep { limit: 64 }),
            "for {input:?}"
        );
    }
}

#[test]
fn of_chains_and_after_clauses_share_one_depth_budget() {
    // 35 `after` levels plus a 35-deep `of` chain inside the innermost
    // clause's locative role NP: neither alone crosses 64, together they
    // must — the budget threads from clause nesting into phrase nesting.
    let deep = format!(
        "When the pump runs{} at the depot{}, the system shall stop.",
        " after the pump runs".repeat(35),
        " of the part".repeat(35)
    );
    let outcome = catch_unwind(AssertUnwindSafe(|| parse(&deep)));
    assert_eq!(
        outcome.expect("parse must not panic"),
        Err(ParseError::PhraseTooDeep { limit: 64 })
    );
    // The same shape well under the budget parses, with the of-chain inside
    // the innermost Location role.
    let shallow = format!(
        "When the pump runs{} at the depot{}, the system shall stop.",
        " after the pump runs".repeat(20),
        " of the part".repeat(20)
    );
    assert!(
        parse(&shallow).is_ok(),
        "20 + 20 stays under the shared budget"
    );
}

#[test]
fn after_clause_with_structured_subject_should_keep_the_after_role() {
    // FIXED (round-3 fixer): the verbal clause readings now agree by
    // preferring the shorter subject, so the boundary heuristic's split at
    // `clears` beats the noun-phrase-first reading that swallowed the whole
    // guard — `the payment clears after the [owner of the file]` — into one
    // flat subject NP (modifiers ["payment", "clears", "after", "the"])
    // with verb `approves`, erasing the trigger event and the After role.
    let s = one(
        "When the payment clears after the owner of the file approves, \
         the system shall issue the receipt.",
    );
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["payment"]);
    let (verb, _, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "clears");
    assert!(object.is_none());
    match &roles[0] {
        RolePp::After(after) => {
            assert_eq!(after.subject.heads(), vec!["owner"]);
            let (verb, _, _, _) = verbal(&after.body);
            assert_eq!(verb, "approves");
        }
        other => panic!("expected After role, got {other:?}"),
    }
    // The exception site misparses the same way.
    let s = one("The pump shall stop, unless the pump runs after the owner of the file approves.");
    let exception = s.exception.as_ref().unwrap();
    assert_eq!(exception.subject.heads(), vec!["pump"]);
    let (verb, _, _, roles) = verbal(&exception.body);
    assert_eq!(verb, "runs");
    assert!(matches!(&roles[0], RolePp::After(_)));
    // And a relative-structured nested subject triggers it too.
    let s = one(
        "When the pump runs after the user who is authenticated logs out, \
                 the session shall end.",
    );
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["pump"]);
}

// ====================================================================================
// 2. The sequence pattern
// ====================================================================================

#[test]
fn sequence_pattern_payment_clears_after_order_ships() {
    let input =
        "When the payment clears after the order ships, the system shall issue the receipt.";
    let s = one(input);
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["payment"]);
    let (verb, particle, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "clears");
    assert_eq!(particle, None);
    assert!(object.is_none());
    assert_eq!(roles.len(), 1);
    match &roles[0] {
        RolePp::After(after) => {
            assert_eq!(after.subject.heads(), vec!["order"]);
            let (verb, _, _, roles) = verbal(&after.body);
            assert_eq!(verb, "ships");
            assert!(roles.is_empty());
        }
        other => panic!("expected After role, got {other:?}"),
    }
    assert_eq!(s.render(), input);
    roundtrip(input);
}

#[test]
fn sequence_pattern_or_group_variant_splits_at_the_conjunction() {
    // The coordination split wins over swallowing the `or` into the `after`
    // clause: item 0 keeps the After role, item 1 is its own event.
    let input = "When the payment clears after the order ships or the invoice posts, \
                 the system shall issue the receipt.";
    let s = one(input);
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::Or));
    assert_eq!(group.items.len(), 2);
    let (verb0, _, _, roles0) = verbal(&group.items[0].body);
    assert_eq!(verb0, "clears");
    assert!(matches!(&roles0[0], RolePp::After(after) if after.subject.heads() == vec!["order"]));
    let (verb1, _, _, roles1) = verbal(&group.items[1].body);
    assert_eq!(verb1, "posts");
    assert!(roles1.is_empty());
    roundtrip(input);

    // The mirror: the After role sits on the LAST item of the group.
    let input = "When the payment clears or the order ships after the invoice posts, \
                 the system shall issue the receipt.";
    let s = one(input);
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::Or));
    let (_, _, _, roles1) = verbal(&group.items[1].body);
    assert!(matches!(&roles1[0], RolePp::After(after) if after.subject.heads() == vec!["invoice"]));
    roundtrip(input);
}

#[test]
fn sequence_pattern_and_group_still_limits_events() {
    // An `and` split leaves two VERBAL conjuncts → still the legislated
    // rejection; the sequence pattern is the answer, not conjunction.
    assert_eq!(
        parse(
            "When the payment clears after the order ships and the valve opens, \
             the system shall issue the receipt."
        ),
        Err(ParseError::MultipleEventConjuncts)
    );
    // The same shape under While is unrestricted.
    let s = one(
        "While the payment clears after the order ships and the valve opens, \
         the daemon shall wait.",
    );
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::And));
    let (_, _, _, roles0) = verbal(&group.items[0].body);
    assert!(matches!(&roles0[0], RolePp::After(_)));
    // And one event + one state stays accepted under When.
    let s = one(
        "When the payment clears after the order ships and the pump is active, \
         the system shall issue the receipt.",
    );
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.items.len(), 2);
    assert!(matches!(&group.items[1].body, ClauseBody::Copular { .. }));
}

/// Round 8, change 1 (pins updated): clausal role values carry the full
/// nested skeleton + full render, not the flat `{subject_head, words}`.
fn nested_clause_value(subject_head: &str, words: &[&str], full: &str) -> RoleValue {
    RoleValue::Clause {
        skeleton: ClauseSkeleton {
            subject_head: subject_head.to_string(),
            polarity: None,
            words: words.iter().map(|s| s.to_string()).collect(),
            manner: Vec::new(),
            // Round 11, change 2: verbal digests carry object digests;
            // these fixtures digest object-free clauses.
            objects: Vec::new(),
            roles: Vec::new(),
            comparison: None,
            content: None,
        },
        full: full.to_string(),
    }
}

#[test]
fn after_and_before_digests_appear_in_guard_skeletons() {
    let k =
        sk("When the payment clears after the order ships, the system shall issue the receipt.");
    let trigger = k.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.clauses[0].roles.len(), 1);
    assert_eq!(trigger.clauses[0].roles[0].kind, RoleKind::After);
    assert_eq!(
        trigger.clauses[0].roles[0].value,
        nested_clause_value("order", &["ships"], "the order ships")
    );

    // Before, in a While frame digest.
    let k = sk("While the guard locks the door before the shift ends, the daemon shall wait.");
    assert_eq!(k.guards.states[0].roles[0].kind, RoleKind::Before);
    assert_eq!(
        k.guards.states[0].roles[0].value,
        nested_clause_value("shift", &["ends"], "the shift ends")
    );

    // Exception digests carry them too.
    let k = sk("The pump shall stop, unless the valve opens after the tank fills.");
    let exception = k.exception.as_ref().unwrap();
    assert_eq!(exception.roles[0].kind, RoleKind::After);
    assert_eq!(
        exception.roles[0].value,
        nested_clause_value("tank", &["fills"], "the tank fills")
    );
}

#[test]
fn nested_clause_role_digests_carry_the_nested_structure() {
    // SUPERSEDED PIN (round 8, change 1): the round-3 blind spot — a
    // `before`/`after` digest keeping subject head + words only — let
    // `after no backup completes` digest exactly like `after the backup
    // completes`. Clausal role values now carry the whole nested clause
    // skeleton plus the full render, so the nested roles DO separate the
    // digests.
    let with = sk(
        "When the payment clears after the order ships from the depot, \
         the system shall issue the receipt.",
    );
    let without =
        sk("When the payment clears after the order ships, the system shall issue the receipt.");
    let t_with = with.guards.trigger.as_ref().unwrap();
    let t_without = without.guards.trigger.as_ref().unwrap();
    assert_ne!(
        t_with.clauses[0].roles[0].value, t_without.clauses[0].roles[0].value,
        "nested-clause roles are digested since round 8 (change 1)"
    );
    match &t_with.clauses[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.roles.len(), 1);
            assert_eq!(skeleton.roles[0].kind, RoleKind::Source);
            assert_eq!(full, "the order ships from the depot");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
}

#[test]
fn verbal_guard_digest_drops_the_object_documented_blind_spot() {
    // SUPERSEDED (round 11, change 2): the blind spot this pin recorded is
    // retired — verbal guard digests carry their object digests now, so
    // `holds no message` and `holds the message` no longer share a
    // skeleton (the object's quantifier is exactly where they differ).
    let no = sk("When the queue holds no message, the daemon shall idle.");
    let the = sk("When the queue holds the message, the daemon shall idle.");
    assert_ne!(no.guards, the.guards);
    let objects = |k: &so_reason::semantics::Skeleton| {
        k.guards.trigger.as_ref().unwrap().clauses[0]
            .objects
            .clone()
    };
    assert_eq!(objects(&no)[0].quantifier, Quantifier::Negative);
    assert_eq!(objects(&the)[0].quantifier, Quantifier::Definite);
    assert_eq!(objects(&no)[0].head, "message");
    assert_eq!(objects(&the)[0].head, "message");
}

// ====================================================================================
// 3. Particle verbs
// ====================================================================================

#[test]
fn all_four_particles_without_objects() {
    for (input, verb, particle) in [
        ("The user shall log out.", "log", "out"),
        ("The system shall shut down.", "shut", "down"),
        ("The daemon shall start up.", "start", "up"),
        ("The exporter shall back off.", "back", "off"),
    ] {
        let s = one(input);
        let vp = deontic_vp(&s);
        assert_eq!(vp.verb, verb, "verb of {input:?}");
        assert_eq!(
            vp.particle.as_deref(),
            Some(particle),
            "particle of {input:?}"
        );
        assert!(vp.object.is_none(), "object of {input:?}");
        assert_eq!(
            sk(input).atoms[0].words,
            vec![verb, particle],
            "atom of {input:?}"
        );
        roundtrip(input);
    }
}

#[test]
fn all_four_particles_with_objects() {
    for (input, verb, particle, object) in [
        ("The daemon shall log out the user.", "log", "out", "user"),
        (
            "The operator shall shut down the server.",
            "shut",
            "down",
            "server",
        ),
        (
            "The service shall spin up a worker.",
            "spin",
            "up",
            "worker",
        ),
        (
            "The operator shall turn off the alarm.",
            "turn",
            "off",
            "alarm",
        ),
    ] {
        let s = one(input);
        let vp = deontic_vp(&s);
        assert_eq!(vp.verb, verb, "verb of {input:?}");
        assert_eq!(
            vp.particle.as_deref(),
            Some(particle),
            "particle of {input:?}"
        );
        assert_eq!(
            vp.object.as_ref().unwrap().heads(),
            vec![object],
            "object of {input:?}"
        );
        roundtrip(input);
    }
}

#[test]
fn particle_with_deadline_and_atom() {
    let s = one("The session shall time out within 30 seconds.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "time");
    assert_eq!(vp.particle.as_deref(), Some("out"));
    assert!(matches!(
        &vp.roles[0],
        RolePp::Deadline(Measure::Quantity { number, unit })
            if number == "30" && unit.as_deref() == Some("seconds")
    ));
    let k = sk("The session shall time out within 30 seconds.");
    assert_eq!(k.atoms[0].words, vec!["time", "out"]);
    assert_ne!(
        k.atoms[0].words,
        sk("The session shall time the request.").atoms[0].words
    );
    roundtrip("The session shall time out within 30 seconds.");
}

#[test]
fn particles_inside_every_frame_kind() {
    // When (already the round-3 pin), While, Where, If, unless.
    for (input, frame_words) in [
        (
            "When the user logs out, the session shall end.",
            ("logs", "out"),
        ),
        (
            "While the operator shuts down the server, the daemon shall wait.",
            ("shuts", "down"),
        ),
        (
            "Where the cluster spins up, the daemon shall wait.",
            ("spins", "up"),
        ),
        (
            "If the exporter backs off, then the daemon shall alert.",
            ("backs", "off"),
        ),
        (
            "The daemon shall wait, unless the exporter backs off.",
            ("backs", "off"),
        ),
    ] {
        let s = one(input);
        let clause = if input.starts_with("When") {
            &s.frames.trigger.as_ref().unwrap().clause.items[0]
        } else if input.starts_with("While") {
            &s.frames.states[0].clause.items[0]
        } else if input.starts_with("Where") {
            &s.frames.scopes[0].clause.items[0]
        } else if input.starts_with("If") {
            &s.frames.trigger.as_ref().unwrap().clause.items[0]
        } else {
            s.exception.as_ref().unwrap()
        };
        let (verb, particle, _, _) = verbal(&clause.body);
        assert_eq!(verb, frame_words.0, "verb of {input:?}");
        assert_eq!(particle, Some(frame_words.1), "particle of {input:?}");
        roundtrip(input);
    }
}

#[test]
fn particle_plus_object_plus_role_in_a_frame_clause() {
    let input = "While the operator shuts down the server at the depot, the daemon shall wait.";
    let s = one(input);
    let (verb, particle, object, roles) = verbal(&s.frames.states[0].clause.items[0].body);
    assert_eq!(verb, "shuts");
    assert_eq!(particle, Some("down"));
    assert_eq!(object.as_ref().unwrap().heads(), vec!["server"]);
    assert!(matches!(&roles[0], RolePp::Location { preposition, .. } if preposition == "at"));
    // The guard digest carries verb + particle + role.
    let k = sk(input);
    assert_eq!(k.guards.states[0].words, vec!["shuts", "down"]);
    assert_eq!(k.guards.states[0].roles[0].kind, RoleKind::Location);
    roundtrip(input);
}

#[test]
fn particle_with_coordinated_object_in_a_clause() {
    let input = "While the operator shuts down the server and the relay, the daemon shall wait.";
    let s = one(input);
    // One clause with a coordinated object — NOT a two-clause group (the
    // `and` remainder `the relay` is no clause).
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, None);
    assert_eq!(group.items.len(), 1);
    let (verb, particle, object, _) = verbal(&group.items[0].body);
    assert_eq!(verb, "shuts");
    assert_eq!(particle, Some("down"));
    assert_eq!(object.as_ref().unwrap().heads(), vec!["server", "relay"]);
    roundtrip(input);
}

#[test]
fn out_of_stays_legislated_unattached_in_core_and_clause() {
    // LEGISLATED (round 3, change 2): a particle never combines with a
    // following `of` — `out` reads as the particle, the dangling `of` is
    // stray material.
    assert_eq!(
        parse("The pump shall run out of water."),
        Err(ParseError::UnexpectedTokens { token: "of".into() })
    );
    // The same legislation must hold inside a frame clause: whatever the
    // exact diagnosis, it is a rejection, not a silent misparse.
    let clause_form = parse("When the pump runs out of water, the daemon shall alert.");
    assert!(
        clause_form.is_err(),
        "`out of` in a clause must be rejected too, got {clause_form:?}"
    );
}

#[test]
fn particle_word_trailing_the_object_joins_the_verb() {
    // SUPERSEDED PIN (round-3 fixer): this test originally pinned the
    // trailing particle word as the object's HEAD (`lift the beam up` →
    // object head "up", modifiers ["beam"]). That displaced the true noun
    // and split the object digests of `lift the beam up` / `lift the beam`
    // — the very atom corruption change 2 set out to remove from the verb
    // slot. The rule is now: a particle word left trailing the object joins
    // the verb, so both spellings share one atom (`lift up`) and one object
    // head (`beam`).
    let s = one("The crane shall lift the beam up.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "lift");
    assert_eq!(vp.particle.as_deref(), Some("up"));
    match vp.object.as_ref().unwrap() {
        NpGroup::Single(np) => {
            assert!(np.modifiers.is_empty());
            assert_eq!(np.head, "beam");
        }
        other => panic!("expected single object, got {other:?}"),
    }
    assert_eq!(
        sk("The crane shall lift the beam up.").atoms[0].words,
        vec!["lift", "up"]
    );
    assert_eq!(
        sk("The crane shall lift the beam up.").atoms[0].objects[0].head,
        sk("The crane shall lift the beam.").atoms[0].objects[0].head,
    );
    // The canonical render normalizes the particle next to its verb and is
    // a fixpoint.
    assert_eq!(
        one("The crane shall lift the beam up.").render(),
        "the crane shall lift up the beam."
    );
    roundtrip("the crane shall lift up the beam.");

    // The pop applies once: with the particle slot already filled, a second
    // particle word stays the object's final word as before.
    let s = one("The operator shall shut down the power down.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.particle.as_deref(), Some("down"));
    match vp.object.as_ref().unwrap() {
        NpGroup::Single(np) => {
            assert_eq!(np.modifiers, vec!["power".to_string()]);
            assert_eq!(np.head, "down");
        }
        other => panic!("expected single object, got {other:?}"),
    }
    roundtrip("The operator shall shut down the power down.");

    // Structure defends the noun reading: an `of`-chain keeps a particle
    // word as its head, and a determiner-only phrase has no other head to
    // fall back to.
    let s = one("The daemon shall start the power up of the system.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.particle, None);
    match vp.object.as_ref().unwrap() {
        NpGroup::Single(np) => {
            assert_eq!(np.head, "up");
            assert_eq!(np.of.as_ref().unwrap().head, "system");
        }
        other => panic!("expected single object, got {other:?}"),
    }
    // In a coordination only the last item touches the phrase end.
    let s = one("The operator shall shut the power and the relay down.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.particle.as_deref(), Some("down"));
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["power", "relay"]);
    // The clause side reads the same way.
    let s = one("When the crane lifts the beam up, the daemon shall wait.");
    let (verb, particle, object, _) =
        verbal(&s.frames.trigger.as_ref().unwrap().clause.items[0].body);
    assert_eq!(verb, "lifts");
    assert_eq!(particle, Some("up"));
    assert_eq!(object.as_ref().unwrap().heads(), vec!["beam"]);
}

#[test]
fn hyphenated_verbs_stay_untouched() {
    for input in [
        "The user shall log-in to the portal.",
        "The system shall shut-down.",
    ] {
        let s = one(input);
        let vp = deontic_vp(&s);
        assert!(vp.verb.contains('-'), "verb of {input:?} keeps its hyphen");
        assert_eq!(vp.particle, None, "no particle in {input:?}");
        roundtrip(input);
    }
    assert_eq!(
        sk("The system shall shut-down.").atoms[0].words,
        vec!["shut-down"]
    );
}

#[test]
fn particle_casing_is_preserved_in_the_tree_and_lowercased_in_the_atom() {
    let s = one("The user shall log OUT.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "log");
    assert_eq!(
        vp.particle.as_deref(),
        Some("OUT"),
        "surface casing kept (losslessness)"
    );
    assert_eq!(s.render(), "the user shall log OUT.");
    assert_eq!(
        sk("The user shall log OUT.").atoms[0].words,
        vec!["log", "out"]
    );
    roundtrip("The user shall log OUT.");
    // Clause side.
    let s = one("When the user LOGS Out, the session shall end.");
    let (verb, particle, _, _) = verbal(&s.frames.trigger.as_ref().unwrap().clause.items[0].body);
    assert_eq!(verb, "LOGS");
    assert_eq!(particle, Some("Out"));
}

#[test]
fn purpose_vp_takes_a_particle() {
    let s = one("The daemon shall wait, in order to back off.");
    match &s.purpose {
        Some(Purpose::InOrderTo(vp)) => {
            assert_eq!(vp.verb, "back");
            assert_eq!(vp.particle.as_deref(), Some("off"));
        }
        other => panic!("expected in-order-to purpose, got {other:?}"),
    }
    roundtrip("The daemon shall wait, in order to back off.");
}

// ====================================================================================
// 4. Skeleton v3
// ====================================================================================

#[test]
fn object_quantifiers_cover_every_determiner() {
    let cases: &[(&str, Quantifier, &str)] = &[
        (
            "The daemon shall log the request.",
            Quantifier::Definite,
            "request",
        ),
        (
            "The daemon shall log a request.",
            Quantifier::Existential,
            "request",
        ),
        (
            "The daemon shall log an entry.",
            Quantifier::Existential,
            "entry",
        ),
        (
            "The daemon shall log each request.",
            Quantifier::Universal,
            "request",
        ),
        (
            "The daemon shall log every request.",
            Quantifier::Universal,
            "request",
        ),
        (
            "The daemon shall log all requests.",
            Quantifier::Universal,
            "requests",
        ),
        (
            "The daemon shall log any request.",
            Quantifier::Universal,
            "request",
        ),
        (
            "The daemon shall log no request.",
            Quantifier::Negative,
            "request",
        ),
        (
            "The daemon shall log requests.",
            Quantifier::None,
            "requests",
        ),
        (
            "The daemon shall retain at least 3 copies.",
            Quantifier::Count {
                op: CountOp::AtLeast,
                n: 3,
            },
            "copies",
        ),
        (
            "The daemon shall retain at most two copies.",
            Quantifier::Count {
                op: CountOp::AtMost,
                n: 2,
            },
            "copies",
        ),
        (
            "The daemon shall retain exactly 7 copies.",
            Quantifier::Count {
                op: CountOp::Exactly,
                n: 7,
            },
            "copies",
        ),
    ];
    for (input, quantifier, head) in cases {
        let k = sk(input);
        assert_eq!(
            k.atoms[0].objects,
            vec![ObjectSkeleton {
                quantifier: *quantifier,
                head: head.to_string(),
                full: head.to_string()
            }],
            "objects of {input:?}"
        );
    }
}

#[test]
fn any_is_universal_in_subject_object_and_role_positions() {
    // Subject.
    assert_eq!(
        sk("Any request is logged.").subject.quantifier,
        Quantifier::Universal
    );
    assert_eq!(
        sk("Any request is logged.").subject.quantifier,
        sk("Each request is logged.").subject.quantifier
    );
    // Object.
    assert_eq!(
        sk("The daemon shall log any request.").atoms[0].objects[0].quantifier,
        Quantifier::Universal
    );
    // Role.
    let k = sk("The daemon shall send the report to any subscriber.");
    assert_eq!(
        k.atoms[0].roles[0].value,
        RoleValue::Heads {
            items: vec![ObjectSkeleton {
                quantifier: Quantifier::Universal,
                head: "subscriber".into(),
                full: "subscriber".into()
            }],
            conj: None,
        }
    );
    // Guard-clause object position: `any` lives in the AST even where the
    // digest drops objects.
    let s = one("When the daemon accepts any request, the log shall grow.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let (_, _, object, _) = verbal(&clause.body);
    match object.as_ref().unwrap() {
        NpGroup::Single(np) => assert_eq!(np.det, Some(Det::Any)),
        other => panic!("expected single object, got {other:?}"),
    }
    // SUPERSEDED PIN (round 5, change 2): round 3 had kept subject `a`
    // existential (its legislation covered `any` alone); round 5 legislates
    // the generic reading for behavioral subjects, so `a` there is now
    // Universal too. Object/role `a` stays existential.
    assert_eq!(
        sk("A request is logged.").subject.quantifier,
        Quantifier::Universal
    );
}

#[test]
fn log_no_request_and_log_the_request_differ_only_in_the_object() {
    let no = sk("The daemon shall log no request.");
    let the = sk("The daemon shall log the request.");
    assert_ne!(no.atoms[0].objects, the.atoms[0].objects);
    assert_eq!(
        no.atoms[0].objects,
        vec![ObjectSkeleton {
            quantifier: Quantifier::Negative,
            head: "request".into(),
            full: "request".into()
        }]
    );
    // Everything else is identical: object `no` stays out of claim polarity.
    assert_eq!(no.polarity, the.polarity);
    assert_eq!(no.polarity, Polarity::Affirmative);
    assert_eq!(no.atoms[0].words, the.atoms[0].words);
    assert_eq!(no.subject, the.subject);
    assert_eq!(no.force, the.force);
    assert_eq!(no.act, the.act);
}

#[test]
fn role_heads_carry_quantifiers_including_coordination() {
    let k = sk("The daemon shall send the report to each subscriber and an auditor.");
    assert_eq!(
        k.atoms[0].roles[0].value,
        RoleValue::Heads {
            items: vec![
                ObjectSkeleton {
                    quantifier: Quantifier::Universal,
                    head: "subscriber".into(),
                    full: "subscriber".into()
                },
                ObjectSkeleton {
                    quantifier: Quantifier::Existential,
                    head: "auditor".into(),
                    full: "auditor".into()
                },
            ],
            conj: Some(Conj::And),
        }
    );
    // A measured role over an NP measure digests as quantified heads too.
    let k = sk("The batch shall complete within the timeout.");
    assert_eq!(
        k.atoms[0].roles[0].value,
        RoleValue::Heads {
            items: vec![ObjectSkeleton {
                quantifier: Quantifier::Definite,
                head: "timeout".into(),
                full: "timeout".into()
            }],
            conj: None,
        }
    );
    // Rate units digest as an unquantified head.
    let k = sk("The meter shall sample per second.");
    assert_eq!(k.atoms[0].roles[0].kind, RoleKind::Rate);
    assert_eq!(
        k.atoms[0].roles[0].value,
        RoleValue::Heads {
            items: vec![ObjectSkeleton {
                quantifier: Quantifier::None,
                head: "second".into(),
                full: "second".into()
            }],
            conj: None,
        }
    );
}

#[test]
fn coordinated_objects_get_one_skeleton_entry_per_item() {
    let k = sk("The daemon shall log no request and every response.");
    assert_eq!(
        k.atoms[0].objects,
        vec![
            ObjectSkeleton {
                quantifier: Quantifier::Negative,
                head: "request".into(),
                full: "request".into()
            },
            ObjectSkeleton {
                quantifier: Quantifier::Universal,
                head: "response".into(),
                full: "response".into()
            },
        ]
    );
    // Heads are lowercased; quantifiers survive count forms.
    let k = sk("The daemon shall retain at least 3 Copies and the Manifest.");
    assert_eq!(
        k.atoms[0].objects,
        vec![
            ObjectSkeleton {
                quantifier: Quantifier::Count {
                    op: CountOp::AtLeast,
                    n: 3
                },
                head: "copies".into(),
                full: "copies".into()
            },
            ObjectSkeleton {
                quantifier: Quantifier::Definite,
                head: "manifest".into(),
                full: "manifest".into()
            },
        ]
    );
}

#[test]
fn skeleton_v3_serde_wire_shapes() {
    // Count quantifiers on objects: internally tagged with op + n.
    let k = sk("The daemon shall retain at most two copies to any subscriber.");
    let j = json(&k);
    let object = &j["atoms"][0]["objects"][0];
    assert_eq!(object["quantifier"]["kind"], "count");
    assert_eq!(object["quantifier"]["op"], "at_most");
    assert_eq!(object["quantifier"]["n"], 2);
    assert_eq!(object["head"], "copies");
    // Heads role values carry quantifier objects per item.
    let role = &j["atoms"][0]["roles"][0];
    assert_eq!(role["kind"], "recipient");
    assert_eq!(role["value"]["kind"], "heads");
    assert_eq!(role["value"]["items"][0]["quantifier"]["kind"], "universal");

    // Clause role digests: the clause value wire shape.
    let k =
        sk("When the payment clears after the order ships, the system shall issue the receipt.");
    let j = json(&k);
    let role = &j["guards"]["trigger"]["clauses"][0]["roles"][0];
    assert_eq!(role["kind"], "after");
    // Round 8, change 1 (serde pin updated): the clause value carries the
    // nested skeleton + full render.
    assert_eq!(role["value"]["kind"], "clause");
    assert_eq!(role["value"]["skeleton"]["subject_head"], "order");
    assert_eq!(
        role["value"]["skeleton"]["words"],
        serde_json::json!(["ships"])
    );
    assert_eq!(role["value"]["full"], "the order ships");

    // The AST wire: verbal clause bodies expose particle (null when absent)
    // and roles; the VP particle field serializes alongside.
    let s = one("When the user logs out, the session shall time out within 30 seconds.");
    let j = json(&s);
    let clause = &j["frames"]["trigger"]["clause"]["items"][0];
    assert_eq!(clause["body"]["kind"], "verbal");
    assert_eq!(clause["body"]["particle"], "out");
    assert_eq!(j["core"]["vp"]["particle"], "out");
    let s = one("When the order ships, the daemon shall pack.");
    let j = json(&s);
    assert_eq!(
        j["frames"]["trigger"]["clause"]["items"][0]["body"]["particle"],
        serde_json::Value::Null
    );
}

// ====================================================================================
// 5. The formula layer
// ====================================================================================

#[test]
fn applicability_top_for_ubiquitous_sentences_of_every_act() {
    for input in [
        "The pump shall stop.",
        "Requests are logged.",
        "The client may retry.",
        "The pump should stop.",
        "A session means a sequence of requests.",
    ] {
        assert_eq!(applicability(&one(input)), Formula::Top, "for {input:?}");
    }
}

#[test]
fn applicability_multi_frame_and_or_structure() {
    // Two scopes, an or-state group, an or-trigger group, an exception:
    // And[ guard, guard, Or[..], Or[..], Not[guard] ] — surface structure
    // preserved, nothing flattened.
    let s = one("Where the plan is enabled, Where the region is isolated, \
         While the pump runs or the valve is open, \
         When the disk fails or the link drops, \
         the daemon shall alert, unless the override is active.");
    match applicability(&s) {
        Formula::And { items } => {
            assert_eq!(items.len(), 5);
            assert_eq!(guard_head(&items[0]), "plan");
            assert_eq!(guard_head(&items[1]), "region");
            match &items[2] {
                Formula::Or { items } => {
                    assert_eq!(items.len(), 2);
                    assert_eq!(guard_head(&items[0]), "pump");
                    assert_eq!(guard_head(&items[1]), "valve");
                }
                other => panic!("expected or state group, got {other:?}"),
            }
            match &items[3] {
                Formula::Or { items } => {
                    assert_eq!(guard_head(&items[0]), "disk");
                    assert_eq!(guard_head(&items[1]), "link");
                }
                other => panic!("expected or trigger group, got {other:?}"),
            }
            match &items[4] {
                Formula::Not { inner } => assert_eq!(guard_head(inner), "override"),
                other => panic!("expected negated exception, got {other:?}"),
            }
        }
        other => panic!("expected conjunction, got {other:?}"),
    }
}

#[test]
fn applicability_of_a_single_and_trigger_group_is_the_group_itself() {
    // One frame → no outer And wrapper.
    let s = one("When the order ships and the pump is active, the daemon shall pack.");
    match applicability(&s) {
        Formula::And { items } => {
            assert_eq!(items.len(), 2);
            assert_eq!(guard_head(&items[0]), "order");
            assert_eq!(guard_head(&items[1]), "pump");
        }
        other => panic!("expected the and-group directly, got {other:?}"),
    }
}

#[test]
fn exception_only_applicability_is_a_bare_negation() {
    // No frames + an exception: applicability = Not(guard) — not And([Not]).
    let s = one("The pump shall stop, unless the override is active.");
    match applicability(&s) {
        Formula::Not { inner } => assert_eq!(guard_head(&inner), "override"),
        other => panic!("expected bare negation, got {other:?}"),
    }
}

#[test]
fn guard_atoms_carry_clause_role_digests() {
    // Change 1 reaches the formula layer: the guard atom's clause digest
    // includes the After role.
    let s =
        one("When the payment clears after the order ships, the system shall issue the receipt.");
    match applicability(&s) {
        Formula::Atom {
            atom: AtomRef::Guard { clause, .. },
        } => {
            assert_eq!(clause.subject_head, "payment");
            assert_eq!(clause.words, vec!["clears"]);
            assert_eq!(clause.roles.len(), 1);
            assert_eq!(clause.roles[0].kind, RoleKind::After);
        }
        other => panic!("expected single guard atom, got {other:?}"),
    }
}

#[test]
fn conditional_guarantee_shape_and_negative_claim_placement() {
    // Framed prohibition: guarantee = Or(Not(applicability), Not(claim-atom))
    // — the claim's negation sits INSIDE the second disjunct.
    let c = contract_formula(&one("When the order ships, the daemon shall not sleep.")).unwrap();
    assert_eq!(c.assumption, Formula::Top);
    match &c.guarantee {
        Formula::Or { items } => {
            assert_eq!(items.len(), 2);
            match &items[0] {
                Formula::Not { inner } => assert_eq!(guard_head(inner), "order"),
                other => panic!("expected negated applicability, got {other:?}"),
            }
            match &items[1] {
                Formula::Not { inner } => match inner.as_ref() {
                    Formula::Atom {
                        atom: AtomRef::Behavior { behavior },
                    } => {
                        assert_eq!(behavior.subject.head, "daemon");
                        assert_eq!(behavior.atom.words, vec!["sleep"]);
                        assert_eq!(behavior.force, Some(Force::Binding));
                        assert_eq!(behavior.act, SpeechAct::Prohibition);
                    }
                    other => panic!("expected behavior atom, got {other:?}"),
                },
                other => panic!("expected negated claim, got {other:?}"),
            }
        }
        other => panic!("expected conditional guarantee, got {other:?}"),
    }
}

#[test]
fn subject_no_negates_the_claim_but_object_no_does_not() {
    // Subject `no`: combined polarity Negative → Not(atom).
    // SUPERSEDED PIN (round 4, change 3): the atom's quantifier was pinned
    // `Negative`, leaving `no` counted twice (in the quantifier AND in the
    // Not wrapper) — underdefined for a solver. The formula layer now
    // normalizes subject-`no` to Universal (`no X: P` ≡ `∀X ¬P`), with the
    // negation carried exactly once by the wrapper; the Skeleton (the
    // surface index) still records `Negative`.
    match claim_formula(&one("No daemon shall sleep.")).unwrap() {
        Formula::Not { inner } => match *inner {
            Formula::Atom {
                atom: AtomRef::Behavior { ref behavior },
            } => {
                assert_eq!(behavior.subject.quantifier, Quantifier::Universal);
            }
            ref other => panic!("expected behavior atom, got {other:?}"),
        },
        other => panic!("expected negated claim, got {other:?}"),
    }
    // Object `no`: polarity stays affirmative — the negation is the object
    // quantifier, not a Not wrapper.
    match claim_formula(&one("The daemon shall log no request.")).unwrap() {
        Formula::Atom {
            atom: AtomRef::Behavior { behavior },
        } => {
            assert_eq!(behavior.atom.objects[0].quantifier, Quantifier::Negative);
        }
        other => panic!("expected bare claim atom, got {other:?}"),
    }
    // `never` description: Not(atom).
    assert!(matches!(
        claim_formula(&one("The temperature is never above the limit.")).unwrap(),
        Formula::Not { .. }
    ));
    // Double negation cancels before the formula is built.
    assert!(matches!(
        claim_formula(&one("No request shall not be logged.")).unwrap(),
        Formula::Atom { .. }
    ));
}

#[test]
fn saturated_is_or_of_guarantee_and_negated_assumption() {
    // Ingest assumption Top: saturated == guarantee, no Or wrapper.
    let c = contract_formula(&one("When the order ships, the daemon shall pack.")).unwrap();
    assert_eq!(c.saturated(), c.guarantee);
    // Non-trivial assumption (hand-paired): Or(guarantee, Not(assumption)),
    // in that order.
    let assumption = applicability(&one("When the order ships, the daemon shall pack."));
    // Round 5: `sources` field added (empty for a hand-built pairing).
    let paired = ContractFormula {
        assumption: assumption.clone(),
        guarantee: c.guarantee.clone(),
        sources: Vec::new(),
    };
    match paired.saturated() {
        Formula::Or { items } => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], c.guarantee);
            assert_eq!(
                items[1],
                Formula::Not {
                    inner: Box::new(assumption)
                }
            );
        }
        other => panic!("expected saturated disjunction, got {other:?}"),
    }
}

#[test]
fn permission_and_definition_have_no_contract_formula() {
    assert!(contract_formula(&one("The client may retry.")).is_none());
    assert!(contract_formula(&one("A session means a sequence of requests.")).is_none());
    assert!(claim_formula(&one("A session means a sequence of requests.")).is_none());
    // A permission keeps a claim formula (admissible behavior) with no
    // force. SUPERSEDED PIN (round 4, change 4): the atom was pinned as a
    // plain Behavior atom distinguished only by `act` — admissibility is
    // now its own AtomRef arm (it bounds tolerated environment behavior
    // and can never witness occurrence).
    match claim_formula(&one("The client may retry.")).unwrap() {
        Formula::Atom {
            atom: AtomRef::Admissibility { behavior },
        } => {
            assert_eq!(behavior.act, SpeechAct::Permission);
            assert_eq!(behavior.force, None);
        }
        other => panic!("expected admissibility atom, got {other:?}"),
    }
    // A FRAMED permission still yields no contract (the applicability alone
    // does not make one).
    assert!(contract_formula(&one("When the queue drains, the client may retry.")).is_none());
    // SUPERSEDED PIN (round 4, change 2): coordinated subjects were pinned
    // formula-free (mirroring the skeleton). The skeleton stays
    // single-subject — it is the surface index — but the formula layer now
    // builds one atom per coordinated item, so these sentences carry claim
    // and contract formulas.
    match claim_formula(&one("The pump and the valve shall stop.")).unwrap() {
        Formula::And { items } => assert_eq!(items.len(), 2),
        other => panic!("expected per-item conjunction, got {other:?}"),
    }
    assert!(contract_formula(&one("The pump and the valve shall stop.")).is_some());
}

#[test]
fn formula_json_wire_shapes_round_trip() {
    let s = one(
        "If the disk fails or the link drops, then the daemon shall not sleep, \
         unless the override is active.",
    );
    let app = applicability(&s);
    let j = json(&app);
    assert_eq!(j["kind"], "and");
    assert_eq!(j["items"][0]["kind"], "or");
    assert_eq!(j["items"][0]["items"][0]["kind"], "atom");
    assert_eq!(j["items"][0]["items"][0]["atom"]["kind"], "guard");
    assert_eq!(
        j["items"][0]["items"][0]["atom"]["clause"]["subject_head"],
        "disk"
    );
    assert_eq!(j["items"][1]["kind"], "not");
    assert_eq!(j["items"][1]["inner"]["kind"], "atom");

    let claim = claim_formula(&s).unwrap();
    let j = json(&claim);
    assert_eq!(j["kind"], "not");
    assert_eq!(j["inner"]["atom"]["kind"], "behavior");
    assert_eq!(j["inner"]["atom"]["behavior"]["subject"]["head"], "daemon");

    let contract = contract_formula(&s).unwrap();
    let j = json(&contract);
    assert_eq!(j["assumption"]["kind"], "top");
    assert_eq!(j["guarantee"]["kind"], "or");
    json(&contract.saturated());

    // Top and Bottom wire shapes.
    assert_eq!(json(&Formula::Top), serde_json::json!({ "kind": "top" }));
    assert_eq!(
        json(&Formula::Bottom),
        serde_json::json!({ "kind": "bottom" })
    );
}

// ====================================================================================
// 6. Totality: seeded fuzz mixing particles, roles, and clause groups
// ====================================================================================

/// A deterministic xorshift64* generator — seeded, no dependencies.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn pick<'a>(&mut self, pool: &[&'a str]) -> &'a str {
        pool[self.below(pool.len())]
    }
}

const FUZZ_WORDS: &[&str] = &[
    // Frame keywords and pivots.
    "When", "While", "Where", "If", "unless", "then", "shall", "must", "should", "may", "is", "are",
    "means", "remains", "not", "never", "always", // Particles and their traps.
    "out", "down", "up", "off", "of", "in", "on", "`out`", "log-in",
    // Role prepositions and locatives.
    "to", "via", "using", "about", "within", "for", "per", "before", "after", "from", "into", "at",
    "under", "over", "above", "below", "least", "most", "exactly", "between", "and", "or", "both",
    "either", "that", "who", // Determiners and numbers.
    "the", "a", "an", "each", "every", "all", "any", "no", "3", "5.5", "zero", "two",
    // Open-class filler.
    "pump", "valve", "daemon", "user", "logs", "shuts", "backs", "times", "runs", "ships", "clears",
    "server", "depot", "seconds", "session", // Punctuation glue.
    ",", ".", ",.", "..",
];

/// Assert that `parse` returns without panicking; when it accepts, the
/// canonical render must itself parse, and be a render fixpoint.
fn total_and_coherent(input: &str) {
    let outcome = catch_unwind(AssertUnwindSafe(|| parse(input)));
    let Ok(result) = outcome else {
        panic!("parse panicked on {input:?}");
    };
    let Ok(spec) = result else { return };
    let rendered = spec.render();
    let re = catch_unwind(AssertUnwindSafe(|| parse(&rendered)));
    let Ok(re) = re else {
        panic!("parse panicked on render {rendered:?} of {input:?}");
    };
    let respec = re.unwrap_or_else(|e| {
        panic!("render {rendered:?} of accepted {input:?} must re-parse, got {e}")
    });
    assert_eq!(
        respec.render(),
        rendered,
        "render must be a fixpoint after one round for {input:?}"
    );
}

#[test]
fn fuzz_word_soup_mixing_particles_roles_and_clause_groups() {
    let mut rng = Rng(0x5EED_2026_0706_0003);
    for _ in 0..4000 {
        let len = 1 + rng.below(14);
        let mut input = String::new();
        for i in 0..len {
            if i > 0 {
                input.push(' ');
            }
            input.push_str(rng.pick(FUZZ_WORDS));
        }
        if rng.below(2) == 0 {
            input.push('.');
        }
        total_and_coherent(&input);
    }
}

#[test]
fn fuzz_templated_frames_with_random_verbal_tails() {
    // Structured fuzz: frames + cores whose verbal material is drawn from
    // particle/role/coordination vocabulary — the round-3 surface, stressed
    // where the pieces interact.
    let subjects = [
        "the pump",
        "the user",
        "no daemon",
        "any valve",
        "the owner of the file",
    ];
    let tails = [
        "logs out",
        "shuts down the server",
        "backs off",
        "times out within 5 seconds",
        "runs at the depot",
        "runs out of water",
        "ships the report to the auditor",
        "clears after the order ships",
        "drains into the tank before the shift ends",
        "lifts the beam up",
        "samples per second",
        "holds at least 3 workers",
        "is active",
        "remains below the limit",
    ];
    let frames = ["When", "While", "Where", "If"];
    let cores = [
        "the daemon shall wait",
        "the daemon shall not sleep",
        "the session shall time out",
        "the client may retry",
        "the operator should shut down the server",
        "a workspace means a shared folder",
        "the pumps are stopped",
    ];
    let adjuncts = [
        "",
        ", unless the exporter backs off",
        ", so that the water drains into the tank",
        ", in order to back off",
        ", unless the pump runs at the depot, so that the audit trail survives",
    ];
    let mut rng = Rng(0x00A7_7AC4_2026_0707);
    for _ in 0..3000 {
        let mut input = String::new();
        for _ in 0..rng.below(3) {
            input.push_str(rng.pick(&frames));
            input.push(' ');
            input.push_str(rng.pick(&subjects));
            input.push(' ');
            input.push_str(rng.pick(&tails));
            if rng.below(3) == 0 {
                input.push(' ');
                input.push_str(rng.pick(&["and", "or"]));
                input.push(' ');
                input.push_str(rng.pick(&subjects));
                input.push(' ');
                input.push_str(rng.pick(&tails));
            }
            input.push_str(", ");
        }
        input.push_str(rng.pick(&cores));
        input.push_str(rng.pick(&adjuncts));
        input.push('.');
        total_and_coherent(&input);

        // Derived views must be total over whatever parses.
        if let Ok(spec) = parse(&input) {
            for sentence in &spec.sentences {
                let outcome = catch_unwind(AssertUnwindSafe(|| {
                    let _ = denote(sentence);
                    let _ = skeleton(sentence);
                    let _ = ingest_contract(sentence);
                    let _ = subject_keys(sentence);
                    let _ = applicability(sentence);
                    let _ = claim_formula(sentence);
                    if let Some(contract) = contract_formula(sentence) {
                        let _ = contract.saturated();
                    }
                }));
                assert!(outcome.is_ok(), "derived views panicked on {input:?}");
            }
        }
    }
}

#[test]
fn fuzz_deep_role_chains_stay_total() {
    // Depth-flavored fuzz: random towers of `after`/`before`/`of` around the
    // budget must yield Ok or PhraseTooDeep — never a panic or abort.
    let mut rng = Rng(0xDEEB_0003);
    for _ in 0..40 {
        let n = 55 + rng.below(20); // straddles the 64 budget
        let link = ["after the pump runs", "before the valve opens"][rng.below(2)];
        let mut input = String::from("When the pump runs");
        for _ in 0..n {
            input.push(' ');
            input.push_str(link);
        }
        input.push_str(", the system shall stop.");
        let outcome = catch_unwind(AssertUnwindSafe(|| parse(&input)));
        match outcome {
            Ok(Ok(_)) => assert!(n < 64, "depth {n} must exceed the budget"),
            Ok(Err(e)) => assert_eq!(
                e,
                ParseError::PhraseTooDeep { limit: 64 },
                "depth {n}: only the depth diagnosis is acceptable, got {e:?}"
            ),
            Err(_) => panic!("parse panicked at depth {n}"),
        }
    }
}
