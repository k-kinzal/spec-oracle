//! Conformance pins for improvement round 3 (IMPROVE-SPEC-3):
//!
//! 1. clause verbal bodies carry thematic roles (frames are where
//!    assumptions live), including `before`/`after` sequencing;
//! 2. particle verbs — the closed particle slot (`out`, `down`, `up`, `off`);
//! 3. skeleton v3 — object/role quantifiers, `any` legislated universal;
//! 4. the formula layer — symbolic applicability/claim/contract formulas;
//! 5. `semantics::subject_keys` — tentative textual identity keys.

use so_lang::ast::*;
use so_lang::formula::{applicability, claim_formula, contract_formula, AtomRef, Formula};
use so_lang::parse::{parse, ParseError};
use so_lang::semantics::*;

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("expected {input:?} to parse, got {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

/// Render must be a fixpoint that re-parses to the same tree.
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

// ====================================================================================
// 1. Clause verbal bodies gain thematic roles
// ====================================================================================

#[test]
fn clause_roles_sequence_pattern() {
    // THE sequencing answer: a trigger event stated relative to another
    // event. Conjunction of events stays rejected (see below); `after` is
    // how protocols order occurrences.
    let input =
        "When the payment clears after the order ships, the system shall issue the receipt.";
    let s = one(input);
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    assert_eq!(trigger.kind, TriggerKind::Event);
    let clause = &trigger.clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["payment"]);
    let (verb, particle, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "clears");
    assert_eq!(particle, None);
    assert!(object.is_none());
    match &roles[0] {
        RolePp::After(after) => {
            assert_eq!(after.subject.heads(), vec!["order"]);
            let (verb, _, object, roles) = verbal(&after.body);
            assert_eq!(verb, "ships");
            assert!(object.is_none());
            assert!(roles.is_empty());
        }
        other => panic!("expected After role, got {other:?}"),
    }
    assert_eq!(s.render(), input, "canonical input renders to itself");
    roundtrip(input);
}

#[test]
fn clause_event_conjunction_stays_rejected() {
    // The sequence pattern above is the supported form; `and` over two
    // occurrences is still simultaneity with no single reading.
    assert_eq!(
        parse("When the payment clears and the order ships, the system shall issue the receipt."),
        Err(ParseError::MultipleEventConjuncts)
    );
}

#[test]
fn clause_roles_cover_the_vp_role_inventory() {
    // Channel/source/destination/timing material in a frame clause.
    let input = "While the relay sends the report to the auditor via the queue \
                 from the depot within 5 seconds, the daemon shall wait.";
    let s = one(input);
    let clause = &s.frames.states[0].clause.items[0];
    let (verb, _, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "sends");
    assert_eq!(object.as_ref().unwrap().heads(), vec!["report"]);
    assert!(matches!(&roles[0], RolePp::Recipient(np) if np.heads() == vec!["auditor"]));
    assert!(
        matches!(&roles[1], RolePp::Means { marker: MeansMarker::Via, np } if np.heads() == vec!["queue"])
    );
    assert!(matches!(&roles[2], RolePp::Source(np) if np.heads() == vec!["depot"]));
    assert!(matches!(
        &roles[3],
        RolePp::Deadline(Measure::Quantity { number, unit })
            if number == "5" && unit.as_deref() == Some("seconds")
    ));
    roundtrip(input);
}

#[test]
fn exception_clause_carries_roles() {
    let s = one("The pump shall stop, unless the pump runs at the depot.");
    let (verb, _, object, roles) = verbal(&s.exception.as_ref().unwrap().body);
    assert_eq!(verb, "runs");
    assert!(object.is_none());
    assert!(matches!(
        &roles[0],
        RolePp::Location { preposition, np } if preposition == "at" && np.heads() == vec!["depot"]
    ));
    // SUPERSEDED PIN (round 5, change 5): the passive agent `by` is now a
    // first-class part of the copular clause — the predicate stays, the
    // agent is recorded — instead of being swallowed into the predicate
    // words (round 3 had pinned the swallow as documented-unsupported).
    let s = one("The pump shall stop, unless the override is engaged by the operator.");
    match &s.exception.as_ref().unwrap().body {
        ClauseBody::Copular {
            predicate: Predicate::Words { words },
            agent,
            ..
        } => {
            assert_eq!(words, &["engaged"]);
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["operator"]);
        }
        other => panic!("expected words predicate with agent, got {other:?}"),
    }
}

#[test]
fn purpose_clause_carries_roles() {
    let s = one("The pump shall stop, so that the water drains into the tank.");
    match &s.purpose {
        Some(Purpose::SoThat(clause)) => {
            let (verb, _, object, roles) = verbal(&clause.body);
            assert_eq!(verb, "drains");
            assert!(object.is_none());
            assert!(matches!(&roles[0], RolePp::Goal(np) if np.heads() == vec!["tank"]));
        }
        other => panic!("expected so-that purpose, got {other:?}"),
    }
    roundtrip("The pump shall stop, so that the water drains into the tank.");
}

#[test]
fn definiens_clause_carries_roles() {
    let s = one("A flush means that the buffer drains into the sink.");
    match &s.core {
        Core::Definition {
            definiens: Definiens::Clause(clause),
            ..
        } => {
            let (verb, _, _, roles) = verbal(&clause.body);
            assert_eq!(verb, "drains");
            assert!(matches!(&roles[0], RolePp::Goal(np) if np.heads() == vec!["sink"]));
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
    roundtrip("A flush means that the buffer drains into the sink.");
}

#[test]
fn relative_bodies_carry_roles_since_round7() {
    // SUPERSEDED PIN (round 7, change 5): relatives now carry the FULL
    // verbal tail, so a role after a relative's object attaches to the
    // RELATIVE's verb — innermost attachment, legislated ("the session
    // that holds the lock in the vault" locates the HOLDING). The round-3
    // pin gave the role to the enclosing verb phrase only because the
    // relative had no role slot to claim it; with role-bearing relatives
    // the innermost verb is the deterministic owner, mirroring the
    // temporal-clause inner-attachment doctrine. Write the outer reading
    // as `close the session that holds the lock, …` reordered or with the
    // role before the object.
    let s = one("The daemon shall close the session that holds the lock in the vault.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            let object = match vp.single().unwrap().object.as_ref().unwrap() {
                NpGroup::Single(np) => np,
                other => panic!("expected single object, got {other:?}"),
            };
            match &object.relative.as_ref().unwrap().body {
                RelativeBody::Verbal {
                    verb,
                    object: Some(_),
                    roles,
                    ..
                } => {
                    assert_eq!(verb, "holds");
                    assert!(matches!(
                        &roles[0],
                        RolePp::Location { preposition, .. } if preposition == "in"
                    ));
                }
                other => panic!("expected verbal relative, got {other:?}"),
            }
            assert!(
                vp.single().unwrap().roles.is_empty(),
                "the relative claimed the role"
            );
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
}

#[test]
fn nested_before_after_clauses_hit_the_depth_bound_not_the_stack() {
    // `after` inside a clause recurses through parse_clause; the shared
    // depth budget must bound it (a totality guarantee, not a panic).
    let deep = format!(
        "When the pump runs {}, the system shall stop.",
        "after the pump runs ".repeat(80).trim_end()
    );
    assert_eq!(parse(&deep), Err(ParseError::PhraseTooDeep { limit: 64 }));
    // Shallow nesting is fine.
    let ok = one(
        "When the pump runs after the valve opens after the tank fills, the system shall stop.",
    );
    let clause = &ok.frames.trigger.as_ref().unwrap().clause.items[0];
    let (_, _, _, roles) = verbal(&clause.body);
    assert!(matches!(&roles[0], RolePp::After(_)));
}

// ====================================================================================
// 2. Particle verbs
// ====================================================================================

#[test]
fn particle_with_deadline_role() {
    let input = "The session shall time out within 30 seconds.";
    let s = one(input);
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "time");
            assert_eq!(vp.single().unwrap().particle.as_deref(), Some("out"));
            assert!(vp.single().unwrap().object.is_none());
            assert!(matches!(
                &vp.single().unwrap().roles[0],
                RolePp::Deadline(Measure::Quantity { number, unit })
                    if number == "30" && unit.as_deref() == Some("seconds")
            ));
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
    assert_eq!(s.render(), "the session shall time out within 30 seconds.");
    roundtrip(input);
}

#[test]
fn particle_plus_object_in_a_frame_clause() {
    let input = "While the operator shuts down the server, the daemon shall wait.";
    let s = one(input);
    let clause = &s.frames.states[0].clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["operator"]);
    let (verb, particle, object, roles) = verbal(&clause.body);
    assert_eq!(verb, "shuts");
    assert_eq!(particle, Some("down"));
    assert_eq!(object.as_ref().unwrap().heads(), vec!["server"]);
    assert!(roles.is_empty());
    roundtrip(input);
}

#[test]
fn particle_in_a_plain_subject_trigger_clause() {
    let s = one("When the user logs out, the session shall end.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["user"]);
    let (verb, particle, object, _) = verbal(&clause.body);
    assert_eq!(verb, "logs");
    assert_eq!(particle, Some("out"));
    assert!(object.is_none());
    roundtrip("When the user logs out, the session shall end.");
}

#[test]
fn bare_particle_verbs_in_the_core() {
    for (input, verb, particle) in [
        ("The system shall shut down.", "shut", "down"),
        ("The exporter shall back off.", "back", "off"),
        ("The daemon shall start up.", "start", "up"),
    ] {
        let s = one(input);
        match &s.core {
            Core::Deontic { vp, .. } => {
                assert_eq!(vp.single().unwrap().verb, verb, "verb of {input:?}");
                assert_eq!(
                    vp.single().unwrap().particle.as_deref(),
                    Some(particle),
                    "particle of {input:?}"
                );
                assert!(vp.single().unwrap().object.is_none());
            }
            other => panic!("expected deontic core, got {other:?}"),
        }
        roundtrip(input);
    }
}

#[test]
fn particle_followed_by_of_is_legislated_unattached() {
    // LEGISLATED (round 3, change 2): a particle never combines with a
    // following `of` — there is no `out of` chain. `out` reads as the
    // particle and the dangling `of` is stray material.
    assert_eq!(
        parse("The pump shall run out of water."),
        Err(ParseError::UnexpectedTokens { token: "of".into() })
    );
}

#[test]
fn be_takes_no_particle() {
    // `shall be off` is the state `off` (a complement), not a particle verb.
    let s = one("The pump shall be off.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "be");
            assert_eq!(vp.single().unwrap().particle, None);
            assert_eq!(
                vp.single().unwrap().complement,
                Some(Predicate::Words {
                    words: vec!["off".into()]
                })
            );
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
}

#[test]
fn backticked_particle_stays_an_object() {
    // The escape hatch: a backticked token never matches the closed list.
    let s = one("The daemon shall log `out`.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "log");
            assert_eq!(vp.single().unwrap().particle, None);
            assert_eq!(
                vp.single().unwrap().object.as_ref().unwrap().heads(),
                vec!["`out`"]
            );
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
}

#[test]
fn in_and_on_are_not_particles() {
    // `in`/`on` open Location roles; hyphenation stays the workaround for
    // `logs in`-style verbs.
    assert_eq!(
        parse("The user shall log in."),
        Err(ParseError::UnexpectedTokens {
            token: "end of sentence".into()
        }),
        "a bare `in` opens a Location role that then lacks its noun phrase"
    );
    let s = one("The user shall log-in.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "log-in");
            assert_eq!(vp.single().unwrap().particle, None);
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
}

// ====================================================================================
// 3. Skeleton v3: object/role quantifiers; `any` legislated universal
// ====================================================================================

#[test]
fn object_quantifiers_reach_the_skeleton() {
    let sk3 = |input: &str| skeleton(&one(input)).unwrap();
    // The pair that used to share a skeleton now differs in the object's
    // quantifier (and ONLY there — polarity stays subject-ruled).
    let no = sk3("The daemon shall log no request.");
    let the = sk3("The daemon shall log the request.");
    assert_ne!(no.atoms[0].objects, the.atoms[0].objects);
    assert_eq!(no.polarity, the.polarity);
    assert_eq!(
        no.atoms[0].objects,
        vec![ObjectSkeleton {
            quantifier: Quantifier::Negative,
            head: "request".into(),
            full: "request".into()
        }]
    );
    // Coordination: one entry per item, each with its own quantifier.
    let k = sk3("The daemon shall log each request and a response.");
    assert_eq!(
        k.atoms[0].objects,
        vec![
            ObjectSkeleton {
                quantifier: Quantifier::Universal,
                head: "request".into(),
                full: "request".into()
            },
            ObjectSkeleton {
                quantifier: Quantifier::Existential,
                head: "response".into(),
                full: "response".into()
            },
        ]
    );
}

#[test]
fn any_is_legislated_universal() {
    // Requirements-English convention: `any` quantifies universally, on
    // subjects and objects alike; `a`/`an` stay existential.
    let sk3 = |input: &str| skeleton(&one(input)).unwrap();
    assert_eq!(
        sk3("Any request is logged.").subject.quantifier,
        Quantifier::Universal
    );
    assert_eq!(
        sk3("Any request is logged.").subject.quantifier,
        sk3("Every request is logged.").subject.quantifier
    );
    // SUPERSEDED PIN (round 5, change 2): behavioral subject `a`/`an` and
    // bare subjects are the generic reading — Universal (round 3 had kept
    // them existential). Object `a`/`an` is unchanged (existential).
    assert_eq!(
        sk3("A request is logged.").subject.quantifier,
        Quantifier::Universal
    );
    assert_eq!(
        sk3("The daemon shall log a request.").atoms[0].objects[0].quantifier,
        Quantifier::Existential
    );
    assert_eq!(
        sk3("The daemon shall log any request.").atoms[0].objects[0].quantifier,
        Quantifier::Universal
    );
}

#[test]
fn role_values_carry_quantifiers() {
    let sk3 = |input: &str| skeleton(&one(input)).unwrap();
    let k = sk3("The daemon shall send the report to each subscriber.");
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
    // `send to a subscriber` vs `send to each subscriber` now differ.
    let a = sk3("The daemon shall send the report to a subscriber.");
    assert_ne!(k.atoms[0].roles, a.atoms[0].roles);
}

#[test]
fn guard_clause_skeletons_carry_role_digests() {
    // Change 1's clause roles must show up in guard/exception digests.
    let k = skeleton(&one(
        "When the payment clears after the order ships, the system shall issue the receipt.",
    ))
    .unwrap();
    let trigger = k.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.clauses[0].words, vec!["clears"]);
    assert_eq!(trigger.clauses[0].roles.len(), 1);
    assert_eq!(trigger.clauses[0].roles[0].kind, RoleKind::After);
    // Round 8, change 1 (pin updated): clausal role values carry the full
    // nested skeleton + full render, not the flat {subject_head, words}.
    match &trigger.clauses[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.subject_head, "order");
            assert_eq!(skeleton.words, vec!["ships"]);
            assert_eq!(full, "the order ships");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    // Exception digests carry them too.
    let k = skeleton(&one(
        "The pump shall stop, unless the pump runs at the depot.",
    ))
    .unwrap();
    let exception = k.exception.as_ref().unwrap();
    assert_eq!(exception.words, vec!["runs"]);
    assert_eq!(exception.roles.len(), 1);
    assert_eq!(exception.roles[0].kind, RoleKind::Location);
    // Copular guard digests have no roles.
    let k = skeleton(&one("While the pump is active, the daemon shall wait.")).unwrap();
    assert!(k.guards.states[0].roles.is_empty());
}

#[test]
fn particle_atoms_include_verb_and_particle() {
    // Change 2, semantics: the atom is verb + particle (two words), so
    // `time out` and `time` are different behaviors.
    let sk = skeleton(&one("The session shall time out within 30 seconds.")).unwrap();
    assert_eq!(sk.atoms[0].words, vec!["time", "out"]);
    let sk = skeleton(&one("The session shall time the request.")).unwrap();
    assert_eq!(sk.atoms[0].words, vec!["time"]);
    // Clause digests carry verb + particle too.
    let sk = skeleton(&one("When the user logs out, the session shall end.")).unwrap();
    let trigger = sk.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.clauses[0].words, vec!["logs", "out"]);
}

// ====================================================================================
// 4. The formula layer
// ====================================================================================

/// The guard atom's clause digest, for shape assertions.
fn guard_head(formula: &Formula) -> &str {
    match formula {
        Formula::Atom {
            atom: AtomRef::Guard { clause, .. },
        } => clause.subject_head.as_str(),
        other => panic!("expected guard atom, got {other:?}"),
    }
}

#[test]
fn applicability_of_an_ubiquitous_sentence_is_top() {
    assert_eq!(applicability(&one("The pump shall stop.")), Formula::Top);
}

#[test]
fn applicability_conjoins_frames_and_negates_the_exception() {
    // scopes ∧ states ∧ trigger ∧ ¬exception.
    let s = one(
        "Where the premium plan is enabled, While the pump is active, \
         When the order ships, the daemon shall pack, unless the override is active.",
    );
    match applicability(&s) {
        Formula::And { items } => {
            assert_eq!(items.len(), 4);
            assert_eq!(guard_head(&items[0]), "plan");
            assert_eq!(guard_head(&items[1]), "pump");
            assert_eq!(guard_head(&items[2]), "order");
            match &items[3] {
                Formula::Not { inner } => assert_eq!(guard_head(inner), "override"),
                other => panic!("expected negated exception, got {other:?}"),
            }
        }
        other => panic!("expected conjunction, got {other:?}"),
    }
}

#[test]
fn applicability_preserves_group_disjunction() {
    // An `or` trigger group stays an Or INSIDE the applicability.
    let s = one("If the disk fails or the link drops, then the daemon shall alert.");
    match applicability(&s) {
        Formula::Or { items } => {
            assert_eq!(items.len(), 2);
            assert_eq!(guard_head(&items[0]), "disk");
            assert_eq!(guard_head(&items[1]), "link");
        }
        other => panic!("expected disjunction, got {other:?}"),
    }
    // An `and` state group stays an And.
    let s = one("While the pump runs and the valve is open, the daemon shall wait.");
    match applicability(&s) {
        Formula::And { items } => assert_eq!(items.len(), 2),
        other => panic!("expected conjunction, got {other:?}"),
    }
}

#[test]
fn claim_formula_places_the_negation_outside_the_atom() {
    // Affirmative: the bare behavior atom.
    match claim_formula(&one("The pump shall stop.")).unwrap() {
        Formula::Atom {
            atom: AtomRef::Behavior { behavior },
        } => {
            assert_eq!(behavior.subject.head, "pump");
            assert_eq!(behavior.atom.words, vec!["stop"]);
            assert_eq!(behavior.force, Some(Force::Binding));
            assert_eq!(behavior.act, SpeechAct::Obligation);
        }
        other => panic!("expected behavior atom, got {other:?}"),
    }
    // Negative combined polarity: Not(atom) — the polarity is formula
    // structure, not atom content.
    match claim_formula(&one("The daemon shall not store derived views.")).unwrap() {
        Formula::Not { inner } => {
            assert!(matches!(
                *inner,
                Formula::Atom {
                    atom: AtomRef::Behavior { .. }
                }
            ));
        }
        other => panic!("expected negated behavior atom, got {other:?}"),
    }
    // Double negation composes to affirmative BEFORE the formula is built.
    assert!(matches!(
        claim_formula(&one("No request shall not be logged.")).unwrap(),
        Formula::Atom { .. }
    ));
    // Definitions have no claim.
    assert!(claim_formula(&one("A session means a sequence of requests.")).is_none());
}

#[test]
fn contract_formula_is_the_sentence_internal_conditional() {
    // Unconditional: guarantee = claim (Top applicability simplified away).
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    assert_eq!(c.assumption, Formula::Top);
    assert!(matches!(&c.guarantee, Formula::Atom { .. }));
    // Framed: guarantee = Or(Not(applicability), claim).
    let c = contract_formula(&one("When the order ships, the daemon shall pack.")).unwrap();
    match &c.guarantee {
        Formula::Or { items } => {
            assert_eq!(items.len(), 2);
            match &items[0] {
                Formula::Not { inner } => assert_eq!(guard_head(inner), "order"),
                other => panic!("expected negated applicability, got {other:?}"),
            }
            assert!(matches!(
                &items[1],
                Formula::Atom {
                    atom: AtomRef::Behavior { .. }
                }
            ));
        }
        other => panic!("expected conditional guarantee, got {other:?}"),
    }
    // Saturation: with the ingest assumption Top, G ∨ ¬A is G itself.
    assert_eq!(c.saturated(), c.guarantee);
    // Round 5: `ContractFormula` carries its typed sources (empty when
    // hand-built without pairing).
    let paired = so_lang::formula::ContractFormula {
        assumption: c.guarantee.clone(),
        guarantee: Formula::Top,
        sources: Vec::new(),
    };
    match paired.saturated() {
        Formula::Or { items } => {
            assert_eq!(items[0], Formula::Top);
            assert!(matches!(&items[1], Formula::Not { .. }));
        }
        other => panic!("expected saturated disjunction, got {other:?}"),
    }
}

#[test]
fn contract_formula_scope() {
    // Definitions AND permissions have no lone contract formula (settled:
    // a permission admits rather than constrains).
    assert!(contract_formula(&one("A session means a sequence of requests.")).is_none());
    assert!(contract_formula(&one("The client may retry.")).is_none());
    // But a permission still has a CLAIM formula (its admissible behavior).
    assert!(claim_formula(&one("The client may retry.")).is_some());
    // Descriptions and recommendations have contract formulas.
    assert!(contract_formula(&one("Requests are logged.")).is_some());
    assert!(contract_formula(&one("The pump should stop.")).is_some());
}

// ====================================================================================
// 5. subject_keys
// ====================================================================================

#[test]
fn subject_keys_are_lowercased_dotted_of_chains() {
    // LEGISLATED (round 3, change 5): the of-chain join character is `.`.
    assert_eq!(subject_keys(&one("The pump shall stop.")), vec!["pump"]);
    assert_eq!(
        subject_keys(&one("The owner of the file shall approve the change.")),
        vec!["owner.file"]
    );
    assert_eq!(
        subject_keys(&one("The size of the log of the daemon is at most 3.")),
        vec!["size.log.daemon"]
    );
    // One key per coordinated item.
    assert_eq!(
        subject_keys(&one("The pump and the valve of the tank shall stop.")),
        vec!["pump", "valve.tank"]
    );
    // SUPERSEDED PIN (round 5, change 4): keys now CARRY lowercased
    // modifiers (`the backup daemon` must not collide with `the daemon`);
    // round 3 had dropped them. Determiners are still dropped.
    assert_eq!(
        subject_keys(&one("Each failed Request shall be logged.")),
        vec!["failed.request"]
    );
    // Definitions have no responsible subject.
    assert_eq!(
        subject_keys(&one("A session means a sequence of requests.")),
        Vec::<String>::new()
    );
    // Descriptions and permissions have subjects like obligations do.
    assert_eq!(subject_keys(&one("The client may retry.")), vec!["client"]);
    assert_eq!(subject_keys(&one("Requests are logged.")), vec!["requests"]);
}
