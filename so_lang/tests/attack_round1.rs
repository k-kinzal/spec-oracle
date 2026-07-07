//! Adversarial conformance attack — improvement round 1 constructs.
//!
//! Object under test: the constructs added by improvement round 1 (see the
//! round's spec): VP `Location` roles, the `means that` definiens marker,
//! clause coordination inside frames, the greedy noun-phrase-first verbal
//! clause split, the backtick escape hatch, the permission ingest change, the
//! logical skeleton, and totality of the new surface syntax.
//!
//! Every expectation was re-derived from the round-1 change spec and
//! `docs/grammar` independently of the implementation's own tests. Passing
//! tests are permanent conformance pins. Tests whose expectation the current
//! implementation does not meet are `#[ignore]`d and carry their finding
//! title; each has a companion pin of the behavior actually observed, so a
//! later fix flips both.

use so_lang::ast::*;
use so_lang::parse::{parse, ParseError};
use so_lang::semantics::{
    self, denote, ingest_contract, skeleton, CountOp, Denotation, Force, Polarity, Quantifier,
    SpeechAct,
};
use std::panic::{catch_unwind, AssertUnwindSafe};

// ---- helpers -----------------------------------------------------------------------

/// Parse an input expected to hold exactly one sentence.
fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

fn deontic(s: &Sentence) -> (&NpGroup, Modal, bool, &Vp) {
    match &s.core {
        Core::Deontic { subject, modal, negated, vp } => {
            (subject, *modal, *negated, vp.single().expect("single vp fixture"))
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
}

fn definition(s: &Sentence) -> (&Np, &Definiens) {
    match &s.core {
        Core::Definition { term, definiens } => (term, definiens),
        other => panic!("expected definition core, got {other:?}"),
    }
}

fn single(group: &NpGroup) -> &Np {
    match group {
        NpGroup::Single(np) => np,
        other => panic!("expected single np, got {other:?}"),
    }
}

/// Round trip: the canonical render must re-parse to the same tree
/// (everything but `source`) and be a render fixpoint. Exact-string identity
/// is NOT required of the input — canonical form lowercases closed-class
/// words (documented in lexical.md), so `The pump …` renders `the pump …`,
/// and a bare copular definiens gains its `that` marker.
fn roundtrip_exact(input: &str) {
    roundtrip_tree(input);
}

fn roundtrip_tree(input: &str) {
    let s = one(input);
    let rendered = s.render();
    let r = one(&rendered);
    assert_eq!(
        (&s.frames, &s.core, &s.exception, &s.purpose),
        (&r.frames, &r.core, &r.exception, &r.purpose),
        "render {rendered:?} of {input:?} must re-parse to the same tree"
    );
    assert_eq!(r.render(), rendered, "render must be a fixpoint for {input:?}");
}

fn location(role: &RolePp) -> (&str, &NpGroup) {
    match role {
        RolePp::Location { preposition, np } => (preposition.as_str(), np),
        other => panic!("expected Location role, got {other:?}"),
    }
}

// ====================================================================================
// 0. Canonical render is exact on already-canonical inputs
// ====================================================================================

#[test]
fn canonical_inputs_render_to_themselves() {
    for input in [
        "the system shall store the report in the archive.",
        "the pump shall run at the depot.",
        // Round 2, change 3: a trigger's `and` group keeps ONE event; the
        // former two-event `ships and clears` form is now rejected.
        "When the order ships and the payment is cleared, the system shall issue the receipt.",
        "While the pump runs or the valve is open, the daemon shall wait.",
        "a timeout means that the request expires.",
        "the system shall record the `will`.",
        "If the disk fails or the link drops, then the daemon shall alert.",
        "When the owner of the file logs out, the session shall end.",
    ] {
        assert_eq!(one(input).render(), input, "canonical input must render to itself");
    }
}

// ====================================================================================
// 1. Location thematic roles
// ====================================================================================

#[test]
fn loc_object_stops_before_locative_and_location_role_opens() {
    let s = one("The system shall store the report in the archive.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.verb, "store");
    let object = single(vp.object.as_ref().expect("object"));
    assert_eq!(object.head, "report", "the locative must NOT fold into the object");
    assert!(object.modifiers.is_empty());
    assert_eq!(vp.roles.len(), 1);
    let (prep, np) = location(&vp.roles[0]);
    assert_eq!(prep, "in");
    assert_eq!(single(np).head, "archive");
    assert_eq!(single(np).det, Some(Det::The));
    roundtrip_exact("The system shall store the report in the archive.");
}

#[test]
fn loc_at_opens_location_when_not_a_comparison() {
    let s = one("The pump shall run at the depot.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.verb, "run");
    assert!(vp.object.is_none(), "a locative directly after the verb is not an object");
    let (prep, np) = location(&vp.roles[0]);
    assert_eq!(prep, "at");
    assert_eq!(single(np).head, "depot");
    roundtrip_exact("The pump shall run at the depot.");
}

#[test]
fn loc_at_least_at_most_stay_on_the_comparison_and_quantifier_paths() {
    // Description predicate: still a comparison.
    let s = one("The retry count is at most 3.");
    match &s.core {
        Core::Description { predicate, .. } => assert_eq!(
            *predicate,
            Predicate::Comparison(Comparison {
                op: ComparisonOp::AtMost,
                value: Measure::Quantity { number: "3".into(), unit: None },
                upper: None,
            })
        ),
        other => panic!("expected description, got {other:?}"),
    }
    // VP object position: `at least n` is a quantifier determiner, never a
    // Location role.
    let s = one("The daemon shall retain at least 3 copies.");
    let (_, _, _, vp) = deontic(&s);
    let object = single(vp.object.as_ref().expect("object"));
    assert_eq!(object.det, Some(Det::AtLeast { n: 3 }));
    assert_eq!(object.head, "copies");
    assert!(vp.roles.is_empty(), "`at least` must not open a Location role");
    roundtrip_exact("The daemon shall retain at least 3 copies.");
}

#[test]
fn loc_every_locative_preposition_opens_a_role() {
    for prep in ["in", "on", "at", "under", "over", "above", "below"] {
        let input = format!("The drone shall hover {prep} the pad.");
        let s = one(&input);
        let (_, _, _, vp) = deontic(&s);
        assert!(vp.object.is_none(), "{input}: no object expected");
        let (got, np) = location(&vp.roles[0]);
        assert_eq!(got, prep);
        assert_eq!(single(np).head, "pad");
        roundtrip_exact(&input);
    }
}

#[test]
fn loc_multiple_locations_and_mixed_roles_keep_surface_order() {
    let input = "The daemon shall write the log into the store on the node within 5 seconds.";
    let s = one(input);
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "log");
    assert_eq!(vp.roles.len(), 3);
    assert!(matches!(&vp.roles[0], RolePp::Goal(np) if single(np).head == "store"));
    let (prep, np) = location(&vp.roles[1]);
    assert_eq!((prep, single(np).head.as_str()), ("on", "node"));
    assert!(matches!(&vp.roles[2], RolePp::Deadline(_)));
    roundtrip_exact(input);

    let input = "The system shall store the report in the archive on the server.";
    let s = one(input);
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.roles.len(), 2);
    assert_eq!(location(&vp.roles[0]).0, "in");
    assert_eq!(location(&vp.roles[1]).0, "on");
    roundtrip_exact(input);
}

#[test]
fn loc_location_np_may_coordinate_and_carry_quantifiers() {
    let input = "The system shall store the report in the archive or the cache.";
    let s = one(input);
    let (_, _, _, vp) = deontic(&s);
    let (prep, np) = location(&vp.roles[0]);
    assert_eq!(prep, "in");
    match np {
        NpGroup::Coordinated { conj: Conj::Or, marker: None, items } => {
            assert_eq!(items[0].head, "archive");
            assert_eq!(items[1].head, "cache");
        }
        other => panic!("expected coordinated location np, got {other:?}"),
    }
    roundtrip_exact(input);

    let input = "The system shall store the report in at most 5 buckets.";
    let s = one(input);
    let (_, _, _, vp) = deontic(&s);
    let (_, np) = location(&vp.roles[0]);
    assert_eq!(single(np).det, Some(Det::AtMost { n: 5 }));
    assert_eq!(single(np).head, "buckets");
    roundtrip_exact(input);
}

#[test]
fn loc_predicate_pps_are_unchanged() {
    let s = one("The temperature is below the limit.");
    match &s.core {
        Core::Description { predicate: Predicate::Pp { preposition, np }, .. } => {
            assert_eq!(preposition, "below");
            assert_eq!(single(np).head, "limit");
        }
        other => panic!("expected pp predicate, got {other:?}"),
    }
    let s = one("The pump is at the depot.");
    assert!(matches!(
        &s.core,
        Core::Description { predicate: Predicate::Pp { .. }, .. }
    ));
    roundtrip_exact("The pump is at the depot.");
}

#[test]
fn loc_be_complement_pp_is_a_complement_not_a_location_role() {
    let s = one("The report shall be in the archive.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.verb, "be");
    assert!(vp.object.is_none());
    assert!(vp.roles.is_empty(), "a be-complement PP is not a Location role");
    match vp.complement.as_ref().expect("complement") {
        Predicate::Pp { preposition, np } => {
            assert_eq!(preposition, "in");
            assert_eq!(single(np).head, "archive");
        }
        other => panic!("expected pp complement, got {other:?}"),
    }
    roundtrip_exact("The report shall be in the archive.");
}

#[test]
fn loc_clause_locatives_open_location_roles() {
    // SUPERSEDED PIN (round 3, change 1): clause verbal bodies carry the
    // same thematic roles as verb phrases, so the leftover-locative
    // rejection (`UnexpectedTokens { token: "at" }`) is gone — the locative
    // opens a Location role on the clause.
    // Frame clause.
    let s = one("When the pump runs at the depot, the system shall stop.");
    match &s.frames.trigger.as_ref().unwrap().clause.items[0].body {
        ClauseBody::Verbal { verb, object, roles, .. } => {
            assert_eq!(verb, "runs");
            assert!(object.is_none());
            let (prep, np) = location(&roles[0]);
            assert_eq!(prep, "at");
            assert_eq!(single(np).head, "depot");
        }
        other => panic!("expected verbal body with a location role, got {other:?}"),
    }
    roundtrip_exact("When the pump runs at the depot, the system shall stop.");
    // Exception clause.
    let s = one("The pump shall stop, unless the pump runs at the depot.");
    match &s.exception.as_ref().unwrap().body {
        ClauseBody::Verbal { verb, roles, .. } => {
            assert_eq!(verb, "runs");
            let (prep, np) = location(&roles[0]);
            assert_eq!(prep, "at");
            assert_eq!(single(np).head, "depot");
        }
        other => panic!("expected verbal body with a location role, got {other:?}"),
    }
    roundtrip_exact("The pump shall stop, unless the pump runs at the depot.");
    // A copular clause with a PP *predicate* stays a predicate — the
    // locative is the predicate, not a role.
    let s = one("While the pump is in the bay, the system shall wait.");
    match &s.frames.states[0].clause.items[0].body {
        ClauseBody::Copular { predicate: Predicate::Pp { preposition, .. }, .. } => {
            assert_eq!(preposition, "in");
        }
        other => panic!("expected pp-predicate copular clause, got {other:?}"),
    }
}

#[test]
fn loc_empty_location_np_is_an_error() {
    assert_eq!(
        parse("The pump shall run in."),
        Err(ParseError::UnexpectedTokens { token: "end of sentence".into() })
    );
}

#[test]
fn loc_backticked_least_defuses_the_comparison_guard() {
    // ``at `least` …`` is NOT the comparison opener: the backticked token
    // never keyword-matches, so `at` opens a Location role.
    let s = one("The pump shall idle at `least` speed.");
    let (_, _, _, vp) = deontic(&s);
    let (prep, np) = location(&vp.roles[0]);
    assert_eq!(prep, "at");
    assert_eq!(single(np).head, "speed");
    assert_eq!(single(np).modifiers, vec!["`least`".to_string()]);
    roundtrip_exact("The pump shall idle at `least` speed.");
}

// ====================================================================================
// 2. `means that <clause>`
// ====================================================================================

#[test]
fn means_that_forces_the_verbal_clause_reading() {
    let s = one("A timeout means that the request expires.");
    let (term, definiens) = definition(&s);
    assert_eq!(term.head, "timeout");
    match definiens {
        Definiens::Clause(clause) => {
            assert_eq!(single(&clause.subject).head, "request");
            match &clause.body {
                ClauseBody::Verbal { verb, object, .. } => {
                    assert_eq!(verb, "expires");
                    assert!(object.is_none());
                }
                other => panic!("expected verbal body, got {other:?}"),
            }
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
    roundtrip_exact("A timeout means that the request expires.");
}

#[test]
fn means_that_copular_clause() {
    let s = one("A session means that a token is issued.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Clause(clause) => {
            assert_eq!(single(&clause.subject).head, "token");
            assert!(matches!(
                &clause.body,
                ClauseBody::Copular { copula: ClauseCopula::Is, predicate: Predicate::Words { words: w }, .. }
                    if w == &vec!["issued".to_string()]
            ));
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
    roundtrip_exact("A session means that a token is issued.");
}

#[test]
fn means_bare_np_misread_is_unchanged() {
    // The documented deterministic misread: without `that`, a copula-free
    // definiens is an NP — head `expires`.
    let s = one("A timeout means the request expires.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Np { np, roles } => {
            let np = single(np);
            assert_eq!(np.det, Some(Det::The));
            assert_eq!(np.modifiers, vec!["request".to_string()]);
            assert_eq!(np.head, "expires");
            assert!(roles.is_empty());
        }
        other => panic!("expected np definiens (documented misread), got {other:?}"),
    }
}

#[test]
fn means_bare_copular_definiens_gains_that_and_reparses_identically() {
    let s = one("A valid token means the signature is correct.");
    let (_, definiens) = definition(&s);
    assert!(matches!(definiens, Definiens::Clause(_)));
    assert_eq!(
        s.render(),
        "a valid token means that the signature is correct.",
        "the canonical form always carries the `that` marker"
    );
    roundtrip_tree("A valid token means the signature is correct.");
}

#[test]
fn means_bare_np_definiens_with_roles_is_unchanged() {
    let s = one("A session means a sequence of requests from one client.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Np { np, roles } => {
            assert_eq!(single(np).head, "sequence");
            assert_eq!(single(np).of.as_ref().unwrap().head, "requests");
            assert!(matches!(&roles[0], RolePp::Source(_)));
        }
        other => panic!("expected np definiens, got {other:?}"),
    }
    roundtrip_exact("A session means a sequence of requests from one client.");
}

#[test]
fn means_definiens_np_takes_a_location_role() {
    let s = one("An archive means a folder on the server.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Np { np, roles } => {
            assert_eq!(single(np).head, "folder");
            let (prep, np) = location(&roles[0]);
            assert_eq!(prep, "on");
            assert_eq!(single(np).head, "server");
        }
        other => panic!("expected np definiens with location role, got {other:?}"),
    }
    roundtrip_exact("An archive means a folder on the server.");
}

#[test]
fn means_that_with_nothing_after_is_empty_definiens() {
    assert_eq!(parse("A timeout means that."), Err(ParseError::EmptyDefiniens));
    assert_eq!(parse("A timeout means."), Err(ParseError::EmptyDefiniens));
}

// `A widget means a part that is small.` — `that` here is a relative marker
// on the definiens NP. The copula commits to the clause reading first, but no
// clause exists (`a part that` is no subject), so the definiens falls back to
// the noun-phrase reading with a copular relative.
#[test]
fn means_np_relative_copula_collision_expected_np_reading() {
    let s = one("A widget means a part that is small.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Np { np, .. } => {
            let np = single(np);
            assert_eq!(np.head, "part");
            let relative = np.relative.as_ref().expect("relative clause");
            assert!(matches!(
                &relative.body,
                RelativeBody::Copular { copula: ClauseCopula::Is, predicate: Predicate::Words { words: w }, .. }
                    if w == &vec!["small".to_string()]
            ));
        }
        other => panic!("expected np definiens with relative, got {other:?}"),
    }
}

// ====================================================================================
// 3. Clause coordination inside frames
// ====================================================================================

#[test]
fn coord_event_conjunction_is_one_joint_guard() {
    // SUPERSEDED IN PART (round 2, change 3): the original two-event form
    // `ships and clears` smuggled back the simultaneity ambiguity the
    // single-trigger rule exists for, so a trigger's `and` group now keeps
    // one event and reads the other conjuncts as states at its instant.
    let input =
        "When the order ships and the payment is cleared, the system shall issue the receipt.";
    let s = one(input);
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    assert_eq!(trigger.kind, TriggerKind::Event);
    assert_eq!(trigger.clause.conj, Some(Conj::And));
    assert_eq!(trigger.clause.items.len(), 2);
    assert_eq!(single(&trigger.clause.items[0].subject).head, "order");
    assert!(matches!(&trigger.clause.items[0].body, ClauseBody::Verbal { verb, .. } if verb == "ships"));
    assert_eq!(single(&trigger.clause.items[1].subject).head, "payment");
    assert!(matches!(&trigger.clause.items[1].body, ClauseBody::Copular { .. }));
    roundtrip_exact(input);
}

#[test]
fn coord_state_disjunction_mixes_verbal_and_copular_items() {
    let input = "While the pump runs or the valve is open, the daemon shall wait.";
    let s = one(input);
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::Or));
    assert_eq!(group.items.len(), 2);
    assert!(matches!(&group.items[0].body, ClauseBody::Verbal { verb, .. } if verb == "runs"));
    assert!(matches!(&group.items[1].body, ClauseBody::Copular { .. }));
    roundtrip_exact(input);
}

#[test]
fn coord_three_items_one_conjunction() {
    // SUPERSEDED IN PART (round 2, change 3): `ships and clears and exists`
    // carried three events under one `and`; a trigger keeps one event, so
    // the other conjuncts are states now.
    let input = "When the order ships and the payment is cleared and the stock is available, \
                 the system shall pack.";
    let s = one(input);
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 3);
    assert!(matches!(&group.items[0].body, ClauseBody::Verbal { verb, .. } if verb == "ships"));
    assert!(matches!(&group.items[2].body, ClauseBody::Copular { .. }));
    roundtrip_exact(input);
}

#[test]
fn coord_mixed_conjunctions_rejected() {
    assert_eq!(
        parse("When the order ships and the payment clears or the stock exists, the system shall pack."),
        Err(ParseError::MixedCoordination)
    );
    // Mixing across the NP and clause levels is still one frame with two
    // conjunctions — rejected.
    assert_eq!(
        parse("While the pump runs or the valve is open and the fan runs, the daemon shall wait."),
        Err(ParseError::MixedCoordination)
    );
}

#[test]
fn coord_np_coordination_in_a_subject_stays_one_clause() {
    // The pinned disambiguation case: the continuation after `and` is not
    // itself a complete clause, so this is ONE clause with a coordinated
    // subject.
    let input = "When the pump and the valve are open, the system shall start.";
    let s = one(input);
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, None, "one clause, not a clause coordination");
    assert_eq!(group.items.len(), 1);
    match &group.items[0].subject {
        NpGroup::Coordinated { conj: Conj::And, items, .. } => {
            assert_eq!(items[0].head, "pump");
            assert_eq!(items[1].head, "valve");
        }
        other => panic!("expected coordinated subject, got {other:?}"),
    }
    assert!(matches!(&group.items[0].body, ClauseBody::Copular { copula: ClauseCopula::Are, .. }));
    roundtrip_exact(input);

    // Same for a disjoined subject.
    let s = one("While the pump or the valve is open, the daemon shall wait.");
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, None);
    assert!(matches!(&group.items[0].subject, NpGroup::Coordinated { conj: Conj::Or, .. }));
}

#[test]
fn coord_np_coordinated_subject_item_composes_with_a_clause_item() {
    // First item's subject is an NP coordination, second item is a clause —
    // both under one `and` frame.
    let input = "When the pump and the valve are open and the fan runs, the system shall start.";
    let s = one(input);
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 2);
    assert!(matches!(&group.items[0].subject, NpGroup::Coordinated { conj: Conj::And, .. }));
    assert!(matches!(&group.items[1].body, ClauseBody::Verbal { verb, .. } if verb == "runs"));
    roundtrip_exact(input);
}

#[test]
fn coord_item_with_of_chain_subject() {
    // Round 2, change 3: the second conjunct became a state (`is closed`) —
    // a trigger's `and` group keeps one event. The pin's point is unchanged:
    // an of-chain subject inside a coordinated item.
    let input =
        "When the owner of the file logs out and the session is closed, the daemon shall lock.";
    let s = one(input);
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 2);
    let first = single(&group.items[0].subject);
    assert_eq!(first.head, "owner");
    assert_eq!(first.of.as_ref().unwrap().head, "file");
    assert!(matches!(&group.items[1].body, ClauseBody::Copular { .. }));
    roundtrip_exact(input);
}

#[test]
fn coord_contingency_group_keeps_then() {
    let input = "If the disk fails or the link drops, then the daemon shall alert.";
    let s = one(input);
    let trigger = s.frames.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Contingency);
    assert_eq!(trigger.clause.conj, Some(Conj::Or));
    assert_eq!(trigger.clause.items.len(), 2);
    roundtrip_exact(input);
}

// `When the order ships the report and the invoice and the payment clears,` —
// a joint guard whose first clause has a coordinated object. The split
// backtracks past the first `and` (its remainder is no clause sequence) and
// lands on the second, keeping the coordinated object inside the first
// clause.
#[test]
fn coord_object_coordination_plus_clause_expected_two_items() {
    // Round 2, change 3: moved from `When` to `While` — the two-verbal `and`
    // group is now rejected in a trigger, and a copular tail here would make
    // the FIRST split viable (coordinated copular subject), defeating the
    // pin. `While` groups are deliberately unrestricted, so the pin's point
    // — the split backtracks past the object's own `and` — is preserved.
    let s = one(
        "While the order ships the report and the invoice and the payment clears, \
         the system shall pay.",
    );
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 2);
    match &group.items[0].body {
        ClauseBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "ships");
            assert!(matches!(
                object.as_ref().unwrap(),
                NpGroup::Coordinated { conj: Conj::And, items, .. } if items.len() == 2
            ));
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    assert!(matches!(&group.items[1].body, ClauseBody::Verbal { verb, .. } if verb == "clears"));
}

// ====================================================================================
// 4. Greedy noun-phrase-first verbal clause splits
// ====================================================================================

#[test]
fn npfirst_owner_of_the_file_logs_out() {
    let s = one("When the owner of the file logs out, the session shall end.");
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.items.len(), 1);
    let clause = &group.items[0];
    let subject = single(&clause.subject);
    assert_eq!(subject.head, "owner");
    assert_eq!(subject.of.as_ref().unwrap().head, "file");
    match &clause.body {
        ClauseBody::Verbal { verb, particle, object, .. } => {
            assert_eq!(verb, "logs");
            // SUPERSEDED PIN (round 3, change 2): `out` is a particle from
            // the closed list (`out`/`down`/`up`/`off`), no longer the
            // bare-NP-object approximation round 1 documented.
            assert_eq!(particle.as_deref(), Some("out"));
            assert!(object.is_none());
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    roundtrip_exact("When the owner of the file logs out, the session shall end.");
}

#[test]
fn npfirst_of_chain_subject_with_real_object() {
    let s = one("When the size of the file exceeds the limit, the daemon shall reject the upload.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let subject = single(&clause.subject);
    assert_eq!(subject.head, "size");
    assert_eq!(subject.of.as_ref().unwrap().head, "file");
    match &clause.body {
        ClauseBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "exceeds");
            assert_eq!(single(object.as_ref().unwrap()).head, "limit");
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
}

#[test]
fn npfirst_verbal_relative_in_subject() {
    let s = one("When the owner that holds the lock logs out, the daemon shall lock.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let subject = single(&clause.subject);
    assert_eq!(subject.head, "owner");
    let relative = subject.relative.as_ref().expect("relative");
    assert!(matches!(
        &relative.body,
        RelativeBody::Verbal { verb, object: Some(_), .. } if verb == "holds"
    ));
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "logs"));
}

#[test]
fn npfirst_copular_reading_still_wins_over_np_first() {
    let s = one("When the owner of the file is active, the daemon shall wait.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(single(&clause.subject).head, "owner");
    assert!(matches!(
        &clause.body,
        ClauseBody::Copular { copula: ClauseCopula::Is, predicate: Predicate::Words { words: w }, .. }
            if w == &vec!["active".to_string()]
    ));
}

#[test]
fn npfirst_plain_subjects_keep_the_determiner_heuristic() {
    let s = one("When the temperature exceeds the limit, the controller shall open the valve.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "exceeds"));
    let s = one("When a session expires, the system shall close the session.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, object: None, .. } if verb == "expires"));
}

// `the user who is authenticated logs out` — a verbal clause whose subject
// carries a COPULAR relative. Every copular split fails, so the clause
// parser falls through to the noun-phrase-first verbal reading, which reads
// the relative into the subject.
#[test]
fn npfirst_copular_relative_subject_expected_to_parse() {
    let s = one("When the user who is authenticated logs out, the session shall end.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let subject = single(&clause.subject);
    assert_eq!(subject.head, "user");
    assert!(subject.relative.is_some());
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "logs"));
}

// ====================================================================================
// 6. Backtick escape hatch
// ====================================================================================

#[test]
fn bt_reserved_word_as_object_head() {
    let s = one("The system shall record the `will`.");
    let (_, _, _, vp) = deontic(&s);
    let object = single(vp.object.as_ref().expect("object"));
    assert_eq!(object.det, Some(Det::The));
    assert_eq!(object.head, "`will`", "backticks are preserved in the token");
    roundtrip_exact("The system shall record the `will`.");
}

#[test]
fn bt_reserved_word_as_modifier() {
    let s = one("The `while` loop shall terminate.");
    let (subject, _, _, vp) = deontic(&s);
    assert_eq!(single(subject).modifiers, vec!["`while`".to_string()]);
    assert_eq!(single(subject).head, "loop");
    assert_eq!(vp.verb, "terminate");
    roundtrip_exact("The `while` loop shall terminate.");
}

#[test]
fn bt_backticked_pivot_does_not_end_the_subject() {
    let s = one("The `shall` flag shall be set.");
    let (subject, modal, _, vp) = deontic(&s);
    assert_eq!(single(subject).modifiers, vec!["`shall`".to_string()]);
    assert_eq!(single(subject).head, "flag");
    assert_eq!(modal, Modal::Shall);
    assert_eq!(vp.verb, "be");
    roundtrip_exact("The `shall` flag shall be set.");
}

#[test]
fn bt_backticked_keywords_never_keyword_match() {
    // Modal position: a backticked modal is not a pivot, so no pivot exists.
    assert_eq!(parse("The pump `shall` stop."), Err(ParseError::MissingPivot));
    // Frame keyword position: a backticked `When` opens no frame.
    assert_eq!(
        parse("`When` the pump runs, the system shall stop."),
        Err(ParseError::MissingPivot)
    );
    // `means` position: a backticked `means` is not a definition pivot.
    assert_eq!(
        parse("A timeout `means` the request expires."),
        Err(ParseError::MissingPivot)
    );
    // Adjunct keyword position: a backticked `unless` is stray material.
    assert_eq!(
        parse("The pump shall stop, `unless` the valve is open."),
        Err(ParseError::UnexpectedTokens { token: "`unless`".into() })
    );
}

#[test]
fn bt_backticked_not_is_an_ordinary_word() {
    // After a modal, backticked `not` is the verb, not negation.
    let s = one("The pump shall `not` stop.");
    let (_, _, negated, vp) = deontic(&s);
    assert!(!negated);
    assert_eq!(vp.verb, "`not`");
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "stop");
    // And it defuses the `may not` ambiguity rejection.
    let s = one("The client may `not` retry.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Permission);
    let (_, modal, negated, vp) = deontic(&s);
    assert_eq!(modal, Modal::May);
    assert!(!negated);
    assert_eq!(vp.verb, "`not`");
}

#[test]
fn bt_backticked_frame_word_inside_a_clause() {
    // A role boundary fixes the verb position, so the backticked frame
    // word is provably an ordinary modifier word (the original intent of
    // this pin, unchanged).
    let s = one("When the `if` token arrives at the depot, the parser shall halt.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    let subject = single(&clause.subject);
    assert_eq!(subject.modifiers, vec!["`if`".to_string()]);
    assert_eq!(subject.head, "token");
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "arrives"));
    roundtrip_exact("When the `if` token arrives at the depot, the parser shall halt.");
    // SUPERSEDED READING (round 11, change 1 — fail-closed, superseding
    // the round-10 SVO pin here): the boundary-less original is a
    // three-word bare run after `the`, which admits both the SVO reading
    // (verb `token`) and the final-word reading (verb `arrives`) — the
    // genuinely ambiguous class, now rejected instead of scrambled either
    // way. The backticked word still parses as an ordinary word wherever a
    // boundary fixes the verb (the role-boundaried form above).
    assert_eq!(
        parse("When the `if` token arrives, the parser shall halt."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
}

#[test]
fn bt_backticked_locative_folds_into_the_object() {
    // Backticking the preposition suppresses the Location role: the words
    // stay in the object NP.
    let s = one("The system shall store the report `in` the archive.");
    let (_, _, _, vp) = deontic(&s);
    assert!(vp.roles.is_empty());
    let object = single(vp.object.as_ref().unwrap());
    assert_eq!(object.head, "archive");
    assert_eq!(
        object.modifiers,
        vec!["report".to_string(), "`in`".to_string(), "the".to_string()]
    );
    roundtrip_exact("The system shall store the report `in` the archive.");
}

#[test]
fn bt_backticked_determiner_and_conjunction() {
    let s = one("The system shall record `the`.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "`the`");
    assert_eq!(single(vp.object.as_ref().unwrap()).det, None);

    // A backticked `and` never opens a coordination.
    let s = one("The daemon shall merge alpha `and` beta.");
    let (_, _, _, vp) = deontic(&s);
    let object = single(vp.object.as_ref().unwrap());
    assert_eq!(object.head, "beta");
    assert_eq!(object.modifiers, vec!["alpha".to_string(), "`and`".to_string()]);
    roundtrip_exact("The daemon shall merge alpha `and` beta.");
}

#[test]
fn bt_unmatched_and_empty_backticks_are_ordinary_words() {
    // Unmatched leading backtick.
    let s = one("The system shall record the `will.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "`will");
    // Unmatched trailing backtick.
    let s = one("The system shall record the will`.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "will`");
    // A lone backtick and an empty pair are words too.
    let s = one("The system shall record the `.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "`");
    let s = one("The system shall record the ``.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "``");
}

#[test]
fn bt_multibyte_inside_backticks() {
    let s = one("The system shall record the `日本語`.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().unwrap()).head, "`日本語`");
    roundtrip_exact("The system shall record the `日本語`.");

    let s = one("When the `will` executes, the estate shall transfer.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(single(&clause.subject).head, "`will`");
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "executes"));
}

// ====================================================================================
// 5. Permission ingest
// ====================================================================================

#[test]
fn perm_lone_permission_has_no_contract_view() {
    let s = one("The client may retry.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Permission);
    assert_eq!(semantics::force(&s), None);
    assert!(matches!(denote(&s), Denotation::Admissibility(_)));
    assert!(
        ingest_contract(&s).is_none(),
        "a permission admits rather than constrains: no (⊤, G) reading"
    );
    // Frames do not change that.
    let s = one("When the request fails, the client may retry via the backup channel.");
    assert!(matches!(denote(&s), Denotation::Admissibility(_)));
    assert!(ingest_contract(&s).is_none());
}

#[test]
fn perm_denotation_keeps_the_admissible_claim() {
    match denote(&one("The client may retry.")) {
        Denotation::Admissibility(assertion) => {
            assert_eq!(assertion.subject.heads(), vec!["client"]);
            assert!(matches!(
                assertion.claim,
                semantics::Claim::Admissible { ref vp } if vp.single().unwrap().verb == "retry"
            ));
        }
        other => panic!("expected admissibility, got {other:?}"),
    }
}

#[test]
fn perm_other_acts_keep_their_contract_views() {
    let contract = ingest_contract(&one("The pump shall stop.")).expect("obligation ingests");
    assert_eq!(contract.assumption.render(), "⊤");
    assert_eq!(contract.act, SpeechAct::Obligation);
    assert_eq!(contract.force, Some(Force::Binding));
    let contract =
        ingest_contract(&one("The library should install propagators.")).expect("recommendation");
    assert_eq!(contract.force, Some(Force::Recommended));
    let contract =
        ingest_contract(&one("The temperature is never above the limit.")).expect("description");
    assert_eq!(contract.act, SpeechAct::Description);
    assert_eq!(contract.force, None);
    assert!(ingest_contract(&one("A session means a sequence of requests.")).is_none());
}

#[test]
fn perm_skeleton_still_derived_for_permissions() {
    let sk = skeleton(&one("The client may retry.")).expect("permission skeleton");
    assert_eq!(sk.act, SpeechAct::Permission);
    assert_eq!(sk.force, None);
    assert_eq!(sk.polarity, Polarity::Affirmative);
    assert_eq!(sk.atoms[0].words, vec!["retry"]);
    // SUPERSEDED (round 2, change 1): a `no` subject under `may` used to
    // yield a negative-polarity permission skeleton. In specification
    // English `No client may retry.` is a prohibition (denial of
    // permission), not an admissibility — the same legislated-ambiguity
    // family as `may not` — so the grammar now rejects it and directs the
    // author to `shall not`.
    assert_eq!(parse("No client may retry."), Err(ParseError::NoWithMay));
}

// ====================================================================================
// 7. Logical skeleton
// ====================================================================================

#[test]
fn sk_polarity_composition_truth_table() {
    let polarity = |input: &str| skeleton(&one(input)).unwrap().polarity;
    // Zero flips.
    assert_eq!(polarity("The request shall be logged."), Polarity::Affirmative);
    assert_eq!(polarity("The request is logged."), Polarity::Affirmative);
    assert_eq!(polarity("The request is always logged."), Polarity::Affirmative);
    // One flip, each site alone.
    assert_eq!(polarity("The request shall not be logged."), Polarity::Negative);
    assert_eq!(polarity("The request is never logged."), Polarity::Negative);
    assert_eq!(polarity("No request shall be logged."), Polarity::Negative);
    assert_eq!(polarity("No request is logged."), Polarity::Negative);
    // Two flips cancel: modal `not` XOR subject `no`…
    assert_eq!(polarity("No request shall not be logged."), Polarity::Affirmative);
    // …and description `never` XOR subject `no`.
    assert_eq!(polarity("No request is never logged."), Polarity::Affirmative);
    // A third site cannot be stacked: `not` is a deontic-only site and
    // `never` a description-only site, so no sentence carries three flips.
    // Writing `never` after `shall not` does not add one — `never` is
    // open-class in verb position, so it becomes the VERB and the skeleton
    // stays a double flip (not XOR no = affirmative) with atom `never`.
    let s = one("No request shall not never be logged.");
    let (_, _, negated, vp) = deontic(&s);
    assert!(negated);
    assert_eq!(vp.verb, "never");
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.polarity, Polarity::Affirmative);
    assert_eq!(sk.atoms[0].words, vec!["never"]);
}

#[test]
fn sk_quantifier_mapping_for_every_determiner() {
    let quantifier = |input: &str| skeleton(&one(input)).unwrap().subject.quantifier;
    assert_eq!(quantifier("The request is logged."), Quantifier::Definite);
    // SUPERSEDED PIN (round 5, change 2): a behavioral subject with `a`/`an`
    // or no determiner is the requirements-English GENERIC reading —
    // legislated Universal, so `A request shall be logged.`, `Requests are
    // logged.`, and `Each request shall be logged.` meet instead of
    // under-detecting conflicts (round 1 had mapped them Existential/None).
    // Object position is untouched: `a`/`an` there stays Existential.
    assert_eq!(quantifier("A request is logged."), Quantifier::Universal);
    assert_eq!(quantifier("An event is logged."), Quantifier::Universal);
    // SUPERSEDED PIN (round 3, change 3): `any` is legislated UNIVERSAL —
    // requirements English reads `any request …` as `every request …`, not
    // as an existential witness (round 1 had mapped it existential).
    assert_eq!(quantifier("Any request is logged."), Quantifier::Universal);
    assert_eq!(quantifier("Each request is logged."), Quantifier::Universal);
    assert_eq!(quantifier("Every request is logged."), Quantifier::Universal);
    assert_eq!(quantifier("All requests are logged."), Quantifier::Universal);
    assert_eq!(quantifier("No request is logged."), Quantifier::Negative);
    assert_eq!(quantifier("Requests are logged."), Quantifier::Universal);
    assert_eq!(
        quantifier("At least 3 replicas shall be available."),
        Quantifier::Count { op: CountOp::AtLeast, n: 3 }
    );
    assert_eq!(
        quantifier("At most two probes are active."),
        Quantifier::Count { op: CountOp::AtMost, n: 2 }
    );
    assert_eq!(
        quantifier("Exactly ten nodes are active."),
        Quantifier::Count { op: CountOp::Exactly, n: 10 }
    );
}

#[test]
fn sk_count_quantifier_skeletons_keep_force_and_atom() {
    let sk = skeleton(&one("At least 3 replicas shall be available.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Count { op: CountOp::AtLeast, n: 3 });
    assert_eq!(sk.subject.head, "replicas");
    assert_eq!(sk.atoms[0].words, vec!["available"]);
    assert_eq!(sk.force, Some(Force::Binding));
    assert_eq!(sk.polarity, Polarity::Affirmative);
}

#[test]
fn sk_atoms_match_across_prohibition_and_never_description() {
    let prohibition = skeleton(&one("The request shall not be logged.")).unwrap();
    let never = skeleton(&one("The request is never logged.")).unwrap();
    assert_eq!(prohibition.atoms[0].words, vec!["logged"]);
    assert_eq!(prohibition.atoms[0], never.atoms[0]);
    assert_eq!(prohibition.polarity, Polarity::Negative);
    assert_eq!(never.polarity, Polarity::Negative);
    assert_eq!(prohibition.subject, never.subject);
    // The `no`-subject universal pair from the round spec.
    let no = skeleton(&one("No request is logged.")).unwrap();
    let each = skeleton(&one("Each request shall be logged.")).unwrap();
    assert_eq!(no.atoms[0], each.atoms[0]);
    assert_eq!(no.atoms[0].words, vec!["logged"]);
    assert_eq!((no.polarity, each.polarity), (Polarity::Negative, Polarity::Affirmative));
    assert_eq!(no.subject.quantifier, Quantifier::Negative);
    assert_eq!(each.subject.quantifier, Quantifier::Universal);
}

#[test]
fn sk_atoms_match_across_be_complement_and_state_pp() {
    // `shall be in the archive` (Action, be-complement) and `is in the
    // archive` (State, pp predicate) normalize to the same atom words.
    let action = skeleton(&one("The report shall be in the archive.")).unwrap();
    let state = skeleton(&one("The report is in the archive.")).unwrap();
    assert_eq!(action.atoms[0].words, vec!["in", "the", "archive"]);
    assert_eq!(action.atoms[0], state.atoms[0]);
    assert_eq!(action.polarity, state.polarity);
}

#[test]
fn sk_action_atom_keeps_roles_out_of_its_words_and_lowercases() {
    let sk = skeleton(&one("The System shall store the Report in the Archive.")).unwrap();
    assert_eq!(sk.atoms[0].words, vec!["store"]);
    // Round 2, change 2: `object_head` became `objects` (all heads); round
    // 3, change 3 (skeleton v3): each object digest carries its quantifier.
    assert_eq!(
        sk.atoms[0].objects,
        vec![semantics::ObjectSkeleton {
            quantifier: semantics::Quantifier::Definite,
            head: "report".into(), full: "report".into()
        }]
    );
    assert_eq!(sk.subject.head, "System", "subject skeleton keeps surface casing");
    // Backticked heads survive (lowercased inside the backticks).
    let sk = skeleton(&one("The system shall record the `Will`.")).unwrap();
    assert_eq!(
        sk.atoms[0].objects,
        vec![semantics::ObjectSkeleton {
            quantifier: semantics::Quantifier::Definite,
            head: "`will`".into(), full: "`will`".into()
        }]
    );
}

#[test]
fn sk_restrictor_and_scope() {
    let sk = skeleton(&one("Each failed request shall be logged.")).unwrap();
    assert_eq!(sk.subject.restrictor, vec!["failed".to_string()]);
    assert_eq!(sk.subject.head, "request");
    // No skeleton for definitions or coordinated subjects.
    assert!(skeleton(&one("A timeout means that the request expires.")).is_none());
    assert!(skeleton(&one("The pump and the valve shall stop.")).is_none());
    // A negated recommendation keeps its act and force.
    let sk = skeleton(&one("The client should not retry.")).unwrap();
    assert_eq!(sk.act, SpeechAct::Recommendation);
    assert_eq!(sk.force, Some(Force::Recommended));
    assert_eq!(sk.polarity, Polarity::Negative);
}

// ====================================================================================
// 8. Totality of the new syntax (seeded LCG fuzz — no external crates)
// ====================================================================================

/// A seeded linear congruential generator (Knuth MMIX constants).
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }
}

/// Assert that `parse` returns without panicking; when it accepts, the
/// canonical render must itself parse and be a render fixpoint (canonical
/// form is stable).
fn total_and_render_stable(input: &str) {
    let outcome = catch_unwind(AssertUnwindSafe(|| parse(input).map(|s| s.render())));
    let rendered = match outcome {
        Ok(result) => result,
        Err(_) => panic!("parse panicked on input: {input:?}"),
    };
    let Ok(rendered) = rendered else { return };
    let reparsed = catch_unwind(AssertUnwindSafe(|| parse(&rendered)));
    match reparsed {
        Ok(Ok(spec)) => assert_eq!(
            spec.render(),
            rendered,
            "render is not a fixpoint for accepted input {input:?}"
        ),
        Ok(Err(error)) => panic!(
            "canonical render {rendered:?} of accepted input {input:?} does not re-parse: {error}"
        ),
        Err(_) => panic!("parse panicked on render {rendered:?} of {input:?}"),
    }
}

/// Vocabulary biased toward the round-1 constructs: locatives, comparison
/// openers, conjunctions, backtick variants, `means`/`that`, and enough glue
/// to form near-sentences.
const FUZZ_VOCAB: &[&str] = &[
    // locatives and comparison material
    "in", "on", "at", "under", "over", "above", "below", "least", "most", "exactly",
    "between", "greater", "less", "than", "equal",
    // coordination
    "and", "or", "both", "either",
    // frames, definition, clause skeleton
    "means", "that", "who", "when", "while", "where", "if", "then", "unless", "so",
    "shall", "must", "may", "should", "is", "are", "remains", "not", "never", "always",
    "be", "of", "will",
    // backtick escape-hatch variants: matched, unmatched, empty, multibyte
    "`will`", "`while`", "`and`", "`or`", "`at`", "`in`", "`means`", "`is`", "`not`",
    "`no`", "`least`", "`", "``", "```", "`x", "x`", "`日本語`", "`🔥`", "`5`",
    // determiners and numbers
    "the", "a", "an", "no", "each", "every", "all", "any", "3", "5.5", "zero", "ten",
    // open-class filler
    "pump", "valve", "report", "archive", "owner", "file", "system", "order", "payment",
    "depot", "logs", "out", "stop", "store", "run", "clears", "ships",
    // role preps and punctuation fragments
    "to", "from", "into", "via", "using", "within", "for", "per", "before", "after",
    ",", ".", "x,", "x.", ",x",
];

#[test]
fn fuzz_lcg_soups_of_new_syntax_never_panic_and_render_stably() {
    let mut rng = Lcg::new(0x00A7_7AC4_2026_0707);
    for _ in 0..5_000 {
        let len = rng.below(28);
        let mut words = Vec::with_capacity(len);
        for _ in 0..len {
            words.push(FUZZ_VOCAB[rng.below(FUZZ_VOCAB.len())]);
        }
        let mut soup = words.join(" ");
        match rng.below(4) {
            0 => soup.push('.'),
            1 => soup.push(','),
            2 => soup.insert(0, '`'),
            _ => {}
        }
        total_and_render_stable(&soup);
    }
}

#[test]
fn fuzz_lcg_backtick_flood() {
    // Dense backtick noise around a plausible sentence spine.
    let mut rng = Lcg::new(0x00BA_CC1C_C0DE);
    let ticks = ["`", "``", "`will`", "`will", "will`", "`日`", "`.`,", "`,`"];
    for _ in 0..1_500 {
        let len = rng.below(20);
        let mut words: Vec<&str> = Vec::with_capacity(len + 4);
        words.push("the");
        for _ in 0..len {
            words.push(ticks[rng.below(ticks.len())]);
        }
        words.push("shall");
        words.push(ticks[rng.below(ticks.len())]);
        words.push("stop.");
        total_and_render_stable(&words.join(" "));
    }
}

#[test]
fn fuzz_valid_construct_combinations_roundtrip_exactly() {
    // Canonical-form building blocks; every combination must parse, render to
    // itself modulo nothing (all blocks are canonical), and re-parse equal.
    let guards = [
        "the pump runs",
        "the valve is open",
        // Round 2, change 3: one event per `and` trigger group — the second
        // conjunct is a state so the guard stays legal under When/If.
        "the order ships and the payment is cleared",
        "the pump runs or the valve is open",
        "the owner of the file logs out",
        "the pump and the valve are open",
        "the `will` executes",
    ];
    let cores = [
        "the system shall store the report in the archive",
        "the daemon shall run in the container",
        "the report shall be in the archive",
        "the retry count is at most 3",
        "the system shall record the `will`",
        "no request is logged",
        "the client may retry",
        "the daemon shall write the log into the store on the node within 5 seconds",
    ];
    // Round 11 (fail-closed verb boundary): `retains control` is the
    // ambiguous class now, so the purpose blocks carry a determiner on the
    // object.
    let tails = [
        "",
        ", unless the override is active",
        ", so that the operator retains the control",
        ", unless the override is active, so that the operator retains the control",
    ];
    let mut rng = Lcg::new(0x5EED_2026_0707);
    for _ in 0..600 {
        let mut input = String::new();
        if rng.below(2) == 0 {
            input.push_str(&format!("Where {}, ", guards[rng.below(guards.len())]));
        }
        if rng.below(2) == 0 {
            input.push_str(&format!("While {}, ", guards[rng.below(guards.len())]));
        }
        match rng.below(3) {
            0 => input.push_str(&format!("When {}, ", guards[rng.below(guards.len())])),
            1 => input.push_str(&format!("If {}, then ", guards[rng.below(guards.len())])),
            _ => {}
        }
        input.push_str(cores[rng.below(cores.len())]);
        input.push_str(tails[rng.below(tails.len())]);
        input.push('.');
        let s = one(&input);
        assert_eq!(s.render(), input, "canonical combination must render to itself");
        let r = one(&s.render());
        assert_eq!(
            (&s.frames, &s.core, &s.exception, &s.purpose),
            (&r.frames, &r.core, &r.exception, &r.purpose),
            "round trip drifted for {input:?}"
        );
    }
}
