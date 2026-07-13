//! The acceptance corpus: the binding examples from the language spec, held
//! green as the grammar evolves.

use so_lang::ast::*;
use so_lang::parse::{parse, ParseError};
use so_reason::semantics::{self, Force, SpeechAct};

/// Parse an input expected to hold exactly one sentence.
fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

/// The subject of a deontic or description core.
fn subject(sentence: &Sentence) -> &NpGroup {
    match &sentence.core {
        Core::Deontic { subject, .. } | Core::Description { subject, .. } => subject,
        Core::Definition { .. } => panic!("definition has no subject group"),
    }
}

/// The verb phrase of a deontic core.
fn vp(sentence: &Sentence) -> &Vp {
    match &sentence.core {
        Core::Deontic { vp, .. } => vp.single().expect("single vp fixture"),
        other => panic!("expected deontic core, got {other:?}"),
    }
}

// ---- parse-ok items -----------------------------------------------------------

#[test]
fn c01_simple_obligation() {
    let s = one("The pump shall stop.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Obligation);
    assert_eq!(subject(&s).heads(), vec!["pump"]);
    let vp = vp(&s);
    assert_eq!(vp.verb, "stop");
    assert!(vp.object.is_none());
    assert_eq!(s.source, "The pump shall stop.");
}

#[test]
fn c02_terminator_is_optional() {
    let s = one("The pump shall stop");
    assert_eq!(s.source, "The pump shall stop");
    assert_eq!(vp(&s).verb, "stop");
}

#[test]
fn c03_description_with_always_and_comparison() {
    let s = one("The sales amount is always greater than zero.");
    match &s.core {
        Core::Description {
            adverb, predicate, ..
        } => {
            assert_eq!(*adverb, Some(DescriptionAdverb::Always));
            assert_eq!(
                *predicate,
                Predicate::Comparison(Comparison {
                    op: ComparisonOp::GreaterThan,
                    value: Measure::Quantity {
                        number: "zero".into(),
                        unit: None
                    },
                    upper: None,
                })
            );
        }
        other => panic!("expected description, got {other:?}"),
    }
}

#[test]
fn c04_event_trigger() {
    let s = one("When the order is submitted, the system shall record the total.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Event);
    assert_eq!(trigger.clause.items[0].subject.heads(), vec!["order"]);
    match &trigger.clause.items[0].body {
        ClauseBody::Copular {
            copula: ClauseCopula::Is,
            predicate,
            ..
        } => {
            assert_eq!(
                *predicate,
                Predicate::Words {
                    words: vec!["submitted".into()]
                }
            );
        }
        other => panic!("expected copular clause, got {other:?}"),
    }
    assert!(matches!(s.core, Core::Deontic { .. }));
}

#[test]
fn c05_contingency_with_then() {
    let s = one("If the balance is negative, then the account shall be frozen.");
    assert_eq!(
        s.frames.trigger.as_ref().unwrap().kind,
        TriggerKind::Contingency
    );
    let vp = vp(&s);
    assert_eq!(vp.verb, "be");
    assert_eq!(
        vp.complement,
        Some(Predicate::Words {
            words: vec!["frozen".into()]
        })
    );
}

#[test]
fn c06_then_is_optional() {
    let with = one("If the balance is negative, then the account shall be frozen.");
    let without = one("If the balance is negative, the account shall be frozen.");
    assert_eq!(with.frames, without.frames);
    assert_eq!(with.core, without.core);
}

#[test]
fn c07_state_frame_plus_trigger() {
    let s = one(
        "While the engine is running, when the temperature exceeds the limit, \
         the controller shall open the valve.",
    );
    assert_eq!(s.frames.states.len(), 1);
    assert_eq!(s.frames.states[0].keyword, "While");
    let trigger = s.frames.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Event);
    assert_eq!(trigger.keyword, "when", "surface casing kept");
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "exceeds");
            assert_eq!(object.as_ref().unwrap().heads(), vec!["limit"]);
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
}

#[test]
fn c08_scoped_definition() {
    let s = one("where the premium plan is enabled, a workspace means a shared folder.");
    assert_eq!(s.frames.scopes.len(), 1);
    assert_eq!(
        s.frames.scopes[0].keyword, "where",
        "surface casing preserved"
    );
    match &s.core {
        Core::Definition { term, definiens } => {
            assert_eq!(term.det, Some(Det::A));
            assert_eq!(term.head, "workspace");
            match definiens {
                Definiens::Np { np, roles } => {
                    assert_eq!(np.heads(), vec!["folder"]);
                    assert!(roles.is_empty());
                }
                other => panic!("expected np definiens, got {other:?}"),
            }
        }
        other => panic!("expected definition, got {other:?}"),
    }
}

#[test]
fn c09_definition_with_of_chain_and_source_role() {
    let s = one("A session means a sequence of requests from one client.");
    match &s.core {
        Core::Definition { term, definiens } => {
            assert_eq!(term.head, "session");
            match definiens {
                Definiens::Np {
                    np: NpGroup::Single(np),
                    roles,
                } => {
                    assert_eq!(np.det, Some(Det::A));
                    assert_eq!(np.head, "sequence");
                    assert_eq!(np.of.as_ref().unwrap().head, "requests");
                    match roles.as_slice() {
                        [RolePp::Source(source)] => {
                            let heads = source.heads();
                            assert_eq!(heads, vec!["client"]);
                            match source {
                                NpGroup::Single(np) => {
                                    assert_eq!(np.det, None);
                                    assert_eq!(np.modifiers, vec!["one".to_string()]);
                                }
                                other => panic!("expected single np, got {other:?}"),
                            }
                        }
                        other => panic!("expected one source role, got {other:?}"),
                    }
                }
                other => panic!("expected np definiens, got {other:?}"),
            }
        }
        other => panic!("expected definition, got {other:?}"),
    }
}

#[test]
fn c10_permission() {
    let s = one("The client may retry.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Permission);
}

#[test]
fn c11_prohibition() {
    let s = one("The daemon shall not store derived views.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Prohibition);
    assert!(matches!(s.core, Core::Deontic { negated: true, .. }));
}

#[test]
fn c12_recommendation_with_coordinated_object() {
    let s = one("The tracing library should install TraceContext and Baggage propagators.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Recommendation);
    match vp(&s).object.as_ref().unwrap() {
        NpGroup::Coordinated {
            conj: Conj::And,
            marker: None,
            items,
        } => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0].head, "TraceContext");
            assert_eq!(items[1].modifiers, vec!["Baggage".to_string()]);
            assert_eq!(items[1].head, "propagators");
        }
        other => panic!("expected coordination, got {other:?}"),
    }
}

#[test]
fn c13_deadline_role() {
    let s = one("When an order is submitted, the system shall record the order within 5 seconds.");
    assert_eq!(
        vp(&s).roles,
        vec![RolePp::Deadline(Measure::Quantity {
            number: "5".into(),
            unit: Some("seconds".into()),
        })]
    );
}

#[test]
fn c14_recipient_and_means_roles() {
    let s = one("The gateway shall send the receipt to the customer via TLS.");
    let vp = vp(&s);
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["receipt"]);
    match vp.roles.as_slice() {
        [RolePp::Recipient(recipient), RolePp::Means {
            marker: MeansMarker::Via,
            np,
        }] => {
            assert_eq!(recipient.heads(), vec!["customer"]);
            assert_eq!(np.heads(), vec!["TLS"]);
        }
        other => panic!("expected recipient + means, got {other:?}"),
    }
}

#[test]
fn c15_topic_role() {
    let s = one("The system shall notify the operator about the failure.");
    match vp(&s).roles.as_slice() {
        [RolePp::Topic(topic)] => assert_eq!(topic.heads(), vec!["failure"]),
        other => panic!("expected topic role, got {other:?}"),
    }
}

#[test]
fn c16_each_with_passive_be() {
    let s = one("Each request shall be logged.");
    match subject(&s) {
        NpGroup::Single(np) => assert_eq!(np.det, Some(Det::Each)),
        other => panic!("expected single np, got {other:?}"),
    }
    let vp = vp(&s);
    assert_eq!(vp.verb, "be");
    assert_eq!(
        vp.complement,
        Some(Predicate::Words {
            words: vec!["logged".into()]
        })
    );
}

#[test]
fn c17_framed_description_with_pp_predicate() {
    let s = one("While the engine is running, the temperature is always below the limit.");
    assert_eq!(s.frames.states.len(), 1);
    match &s.core {
        Core::Description {
            predicate: Predicate::Pp { preposition, np },
            ..
        } => {
            assert_eq!(preposition, "below");
            assert_eq!(np.heads(), vec!["limit"]);
        }
        other => panic!("expected pp description, got {other:?}"),
    }
}

#[test]
fn c18_exception() {
    let s = one("The pump shall stop, unless the override is active.");
    let exception = s.exception.as_ref().unwrap();
    assert_eq!(exception.subject.heads(), vec!["override"]);
}

#[test]
fn c19_purpose_so_that() {
    let s = one("The daemon shall persist the node, so that the auditor traces the decision.");
    match &s.purpose {
        Some(Purpose::SoThat(clause)) => {
            assert_eq!(clause.subject.heads(), vec!["auditor"]);
            assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "traces"));
        }
        other => panic!("expected so-that purpose, got {other:?}"),
    }
}

#[test]
fn c20_purpose_in_order_to() {
    let s = one("The system shall log each request, in order to preserve the audit trail.");
    match &s.purpose {
        Some(Purpose::InOrderTo(vp)) => {
            assert_eq!(vp.verb, "preserve");
            assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["trail"]);
        }
        other => panic!("expected in-order-to purpose, got {other:?}"),
    }
}

#[test]
fn c21_no_determiner_and_url_recipient() {
    let s = one(
        "When no OTLP endpoint is configured, the tracing library should default \
         OTLP HTTP export to http://192.168.10.4:4318.",
    );
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].subject {
        NpGroup::Single(np) => {
            assert_eq!(np.det, Some(Det::No));
            assert_eq!(np.modifiers, vec!["OTLP".to_string()]);
            assert_eq!(np.head, "endpoint");
        }
        other => panic!("expected single np, got {other:?}"),
    }
    match vp(&s).roles.as_slice() {
        [RolePp::Recipient(recipient)] => {
            assert_eq!(recipient.heads(), vec!["http://192.168.10.4:4318"]);
        }
        other => panic!("expected recipient role, got {other:?}"),
    }
}

#[test]
fn c22_relative_clause_in_subject() {
    let s = one("The user who is authenticated may open the session.");
    match subject(&s) {
        NpGroup::Single(np) => {
            assert_eq!(np.head, "user");
            let relative = np.relative.as_ref().unwrap();
            assert_eq!(relative.marker, RelMarker::Who);
            match &relative.body {
                RelativeBody::Copular {
                    copula: ClauseCopula::Is,
                    predicate,
                    ..
                } => {
                    assert_eq!(
                        *predicate,
                        Predicate::Words {
                            words: vec!["authenticated".into()]
                        }
                    );
                }
                other => panic!("expected copular relative, got {other:?}"),
            }
        }
        other => panic!("expected single np, got {other:?}"),
    }
}

#[test]
fn c23_at_most_comparison() {
    let s = one("The retry count is at most 3.");
    match &s.core {
        Core::Description { predicate, .. } => assert_eq!(
            *predicate,
            Predicate::Comparison(Comparison {
                op: ComparisonOp::AtMost,
                value: Measure::Quantity {
                    number: "3".into(),
                    unit: None
                },
                upper: None,
            })
        ),
        other => panic!("expected description, got {other:?}"),
    }
}

#[test]
fn c24_between_with_unit_on_upper() {
    let s = one("The delay is between 5 and 30 seconds.");
    match &s.core {
        Core::Description { predicate, .. } => assert_eq!(
            *predicate,
            Predicate::Comparison(Comparison {
                op: ComparisonOp::Between,
                value: Measure::Quantity {
                    number: "5".into(),
                    unit: None
                },
                upper: Some(Measure::Quantity {
                    number: "30".into(),
                    unit: Some("seconds".into())
                }),
            })
        ),
        other => panic!("expected description, got {other:?}"),
    }
}

#[test]
fn c25_bare_plural_description() {
    let s = one("Requests are logged.");
    match &s.core {
        Core::Description {
            subject,
            copula: Copula::Are,
            adverb: None,
            predicate,
            ..
        } => {
            match subject {
                NpGroup::Single(np) => {
                    assert_eq!(np.det, None);
                    assert_eq!(np.head, "Requests");
                }
                other => panic!("expected single np, got {other:?}"),
            }
            assert_eq!(
                *predicate,
                Predicate::Words {
                    words: vec!["logged".into()]
                }
            );
        }
        other => panic!("expected description, got {other:?}"),
    }
}

#[test]
fn c26_multi_sentence_and_references() {
    let spec = parse(
        "A session means a sequence of requests. \
         When a session expires, the system shall close the session.",
    )
    .unwrap();
    assert_eq!(spec.sentences.len(), 2);
    let refs = semantics::references(&spec);
    let session = refs.iter().find(|r| r.head == "session").unwrap();
    assert!(
        matches!(session.resolution, semantics::Resolution::Unique { .. }),
        "same-head introductions deduplicate to the most recent: {session:?}"
    );
}

#[test]
fn c27_case_insensitive_modal() {
    let s = one("the pump SHALL stop.");
    assert!(matches!(
        s.core,
        Core::Deontic {
            modal: Modal::Shall,
            ..
        }
    ));
}

#[test]
fn c28_multibyte_open_class() {
    let s = one("The café shall serve crêpes.");
    assert_eq!(subject(&s).heads(), vec!["café"]);
    assert_eq!(vp(&s).object.as_ref().unwrap().heads(), vec!["crêpes"]);
}

// ---- locative roles (improvement round 1, change 1) ---------------------------------

#[test]
fn l01_locative_does_not_fold_into_the_object() {
    // Previously misparsed with object head "archive" (the locative silently
    // folded into the object noun phrase).
    let s = one("The system shall store the report in the archive.");
    let vp = vp(&s);
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["report"]);
    match vp.roles.as_slice() {
        [RolePp::Location { preposition, np }] => {
            assert_eq!(preposition, "in");
            assert_eq!(np.heads(), vec!["archive"]);
        }
        other => panic!("expected [Location(in)], got {other:?}"),
    }
    // Canonical render: closed-class words in lowercase, the location kept.
    assert_eq!(
        s.render(),
        "the system shall store the report in the archive."
    );
}

#[test]
fn l02_at_location_without_object() {
    let s = one("The pump shall run at the depot.");
    let vp = vp(&s);
    assert!(vp.object.is_none());
    match vp.roles.as_slice() {
        [RolePp::Location { preposition, np }] => {
            assert_eq!(preposition, "at");
            assert_eq!(np.heads(), vec!["depot"]);
        }
        other => panic!("expected [Location(at)], got {other:?}"),
    }
}

#[test]
fn l03_at_least_most_stay_comparisons_and_quantifiers() {
    // `at most 3` is a comparison, never a location.
    let s = one("The retry count is at most 3.");
    assert!(matches!(
        &s.core,
        Core::Description { predicate: Predicate::Comparison(c), .. }
            if c.op == ComparisonOp::AtMost
    ));
    // `at least 3 copies` is a quantified object, never a location.
    let s = one("The daemon shall retain at least 3 copies.");
    let vp = vp(&s);
    match vp.object.as_ref().unwrap() {
        NpGroup::Single(np) => assert_eq!(np.det, Some(Det::AtLeast { n: 3 })),
        other => panic!("expected quantified object, got {other:?}"),
    }
    assert!(vp.roles.is_empty());
}

#[test]
fn l04_location_composes_with_other_roles_and_round_trips() {
    let s = one("The gateway shall send the receipt to the customer in the branch.");
    let vp = vp(&s);
    assert!(matches!(
        vp.roles.as_slice(),
        [RolePp::Recipient(_), RolePp::Location { .. }]
    ));
    for input in [
        "The system shall store the report in the archive.",
        "The pump shall run at the depot.",
        "The service shall hold the lease under the quota.",
    ] {
        let parsed = parse(input).unwrap();
        let rendered = parsed.render();
        assert_eq!(
            parse(&rendered).unwrap().sentences[0].core,
            parsed.sentences[0].core
        );
    }
}

#[test]
fn l05_clause_locatives_open_location_roles() {
    // SUPERSEDED PIN (round 3, change 1): clause verbal bodies now carry the
    // same thematic roles as verb phrases — frames are where assumptions
    // live, and location/channel/timing are exactly the material environment
    // assumptions are made of. The former rejection
    // (`UnexpectedTokens { token: "in"/"at" }`) is gone.
    let s = one("When the clerk stores the report in the archive, the pump shall stop.");
    match &s.frames.trigger.as_ref().unwrap().clause.items[0].body {
        ClauseBody::Verbal {
            verb,
            object,
            roles,
            ..
        } => {
            assert_eq!(verb, "stores");
            assert_eq!(object.as_ref().unwrap().heads(), vec!["report"]);
            assert!(matches!(
                &roles[0],
                RolePp::Location { preposition, np }
                    if preposition == "in" && np.heads() == vec!["archive"]
            ));
        }
        other => panic!("expected verbal body with a location role, got {other:?}"),
    }
    let s = one("When the pump runs at the depot, the valve shall close.");
    match &s.frames.trigger.as_ref().unwrap().clause.items[0].body {
        ClauseBody::Verbal {
            verb,
            object,
            roles,
            ..
        } => {
            assert_eq!(verb, "runs");
            assert!(object.is_none());
            assert!(matches!(
                &roles[0],
                RolePp::Location { preposition, np }
                    if preposition == "at" && np.heads() == vec!["depot"]
            ));
        }
        other => panic!("expected verbal body with a location role, got {other:?}"),
    }
}

#[test]
fn l06_predicate_pps_unchanged() {
    // A prepositional predicate is not a Location role.
    let s = one("The temperature is below the limit.");
    assert!(matches!(
        &s.core,
        Core::Description { predicate: Predicate::Pp { preposition, .. }, .. }
            if preposition == "below"
    ));
    // A `be`-complement locative stays a predicate PP as well.
    let s = one("The account shall be in flight mode.");
    let vp = vp(&s);
    assert!(matches!(
        vp.complement,
        Some(Predicate::Pp { ref preposition, .. }) if preposition == "in"
    ));
    assert!(vp.roles.is_empty());
}

// ---- `means that <clause>` (improvement round 1, change 2) ---------------------------

#[test]
fn mt01_means_that_forces_the_verbal_clause_reading() {
    let s = one("A timeout means that the request expires.");
    match &s.core {
        Core::Definition {
            term,
            definiens: Definiens::Clause(clause),
        } => {
            assert_eq!(term.head, "timeout");
            assert_eq!(clause.subject.heads(), vec!["request"]);
            assert!(
                matches!(&clause.body, ClauseBody::Verbal { verb, object: None, .. } if verb == "expires")
            );
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
}

#[test]
fn mt02_bare_means_keeps_the_documented_np_reading() {
    // Without `that` the deterministic NP reading is unchanged (see the x01
    // pin in attack_conformance: `DET WORD WORD` is one shape).
    let s = one("A timeout means the request expires.");
    match &s.core {
        Core::Definition {
            definiens: Definiens::Np { np, .. },
            ..
        } => {
            assert_eq!(np.heads(), vec!["expires"]);
        }
        other => panic!("expected np definiens, got {other:?}"),
    }
}

#[test]
fn mt03_means_that_copular_clause() {
    let s = one("A session means that a token is issued.");
    match &s.core {
        Core::Definition {
            definiens: Definiens::Clause(clause),
            ..
        } => {
            assert_eq!(clause.subject.heads(), vec!["token"]);
            assert!(matches!(
                &clause.body,
                ClauseBody::Copular { copula: ClauseCopula::Is, predicate, ..  }
                    if *predicate == Predicate::Words { words: vec!["issued".into()] }
            ));
        }
        other => panic!("expected copular clause definiens, got {other:?}"),
    }
}

#[test]
fn mt04_clause_definiens_renders_with_that_and_round_trips() {
    // A copular definiens parsed WITHOUT the marker renders WITH it and
    // re-parses to the same tree.
    let parsed = parse("A valid token means the signature is correct.").unwrap();
    let rendered = parsed.render();
    assert_eq!(
        rendered,
        "a valid token means that the signature is correct."
    );
    assert_eq!(
        parse(&rendered).unwrap().sentences[0].core,
        parsed.sentences[0].core
    );
    // The explicit form round-trips to itself.
    let parsed = parse("A timeout means that the request expires.").unwrap();
    let rendered = parsed.render();
    assert_eq!(rendered, "a timeout means that the request expires.");
    assert_eq!(
        parse(&rendered).unwrap().sentences[0].core,
        parsed.sentences[0].core
    );
}

// ---- clause coordination inside frames (improvement round 1, change 3) ---------------

#[test]
fn g01_joint_event_guard() {
    // SUPERSEDED IN PART (round 2, change 3): the original `ships and
    // clears` guard held two events under `and` — the simultaneity ambiguity
    // the single-trigger rule legislates away. A joint guard now keeps one
    // event; the other conjuncts are states read at the trigger instant.
    let s =
        one("When the order ships and the payment is cleared, the system shall issue the receipt.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Event);
    let group = &trigger.clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 2);
    assert_eq!(group.items[0].subject.heads(), vec!["order"]);
    assert!(matches!(&group.items[0].body, ClauseBody::Verbal { verb, .. } if verb == "ships"));
    assert_eq!(group.items[1].subject.heads(), vec!["payment"]);
    assert!(matches!(&group.items[1].body, ClauseBody::Copular { .. }));
}

#[test]
fn g02_alternative_state_guard() {
    let s = one("While the pump runs or the valve is open, the system shall alert the operator.");
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::Or));
    assert_eq!(group.items.len(), 2);
    assert!(matches!(&group.items[0].body, ClauseBody::Verbal { verb, .. } if verb == "runs"));
    assert!(matches!(
        &group.items[1].body,
        ClauseBody::Copular { copula: ClauseCopula::Is, predicate, ..  }
            if *predicate == Predicate::Words { words: vec!["open".into()] }
    ));
}

#[test]
fn g03_mixed_conjunctions_in_one_frame_reject() {
    assert_eq!(
        parse(
            "When the order ships and the payment clears or the invoice posts, \
             the pump shall stop."
        ),
        Err(ParseError::MixedCoordination)
    );
}

#[test]
fn g04_np_coordination_in_a_subject_stays_one_clause() {
    // The exact NP-vs-clause pin: no prefix before `and` is a complete
    // clause, so this is ONE clause with a coordinated subject.
    let s = one("When the pump and the valve are open, the system shall alert the operator.");
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, None);
    assert_eq!(group.items.len(), 1);
    match &group.items[0].subject {
        NpGroup::Coordinated {
            conj: Conj::And,
            marker: None,
            items,
        } => {
            assert_eq!(items[0].head, "pump");
            assert_eq!(items[1].head, "valve");
        }
        other => panic!("expected coordinated subject, got {other:?}"),
    }
    assert!(matches!(
        &group.items[0].body,
        ClauseBody::Copular {
            copula: ClauseCopula::Are,
            ..
        }
    ));
}

#[test]
fn g05_clause_group_render_round_trips() {
    for input in [
        // Round 2, change 3: one event per `and` trigger group.
        "When the order ships and the payment is cleared, the system shall issue the receipt.",
        "While the pump runs or the valve is open, the system shall alert the operator.",
        "When the pump and the valve are open, the system shall alert the operator.",
    ] {
        let parsed = parse(input).unwrap();
        let rendered = parsed.render();
        let reparsed = parse(&rendered)
            .unwrap_or_else(|e| panic!("render of {input:?} must re-parse; {rendered:?}: {e}"));
        assert_eq!(reparsed.sentences[0].frames, parsed.sentences[0].frames);
        assert_eq!(reparsed.sentences[0].core, parsed.sentences[0].core);
    }
}

// ---- of-chain subjects in verbal frame clauses (improvement round 1, change 4) --------

#[test]
fn o01_of_chain_subject_in_a_verbal_frame_clause() {
    // Previously rejected: the determiner heuristic took `of` for the verb.
    let s = one("When the owner of the file logs out, the session shall end.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    match &clause.subject {
        NpGroup::Single(np) => {
            assert_eq!(np.head, "owner");
            assert_eq!(np.of.as_ref().unwrap().head, "file");
        }
        other => panic!("expected single np subject, got {other:?}"),
    }
    match &clause.body {
        ClauseBody::Verbal {
            verb,
            particle,
            object,
            ..
        } => {
            assert_eq!(verb, "logs");
            // SUPERSEDED PIN (round 3, change 2): `out` is now the verb's
            // particle from the closed list, no longer the bare-NP-object
            // approximation the earlier rounds documented.
            assert_eq!(particle.as_deref(), Some("out"));
            assert!(object.is_none());
        }
        other => panic!("expected verbal body, got {other:?}"),
    }
}

#[test]
fn o02_of_chain_subject_with_a_real_object() {
    let s = one("When the owner of the file opens the folder, the daemon shall log the access.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    match &clause.subject {
        NpGroup::Single(np) => {
            assert_eq!(np.head, "owner");
            assert_eq!(np.of.as_ref().unwrap().head, "file");
        }
        other => panic!("expected single np subject, got {other:?}"),
    }
    assert!(matches!(
        &clause.body,
        ClauseBody::Verbal { verb, object: Some(object), .. }
            if verb == "opens" && object.heads() == vec!["folder"]
    ));
}

#[test]
fn o03_plain_subjects_keep_the_determiner_heuristic() {
    // No of-chain: with a determiner-led object the boundary reading is
    // exactly what it was before the NP-first path existed.
    let s = one("When the temperature exceeds the limit, the pump shall stop.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "exceeds"));
    // SUPERSEDED READING (round 11, change 1 — fail-closed, superseding
    // the round-10 SVO scramble pinned here and the round-3 final-word
    // acceptance before it): `the temperature sensor fails` is a
    // boundary-less det-led run of three, admitting both the SVO reading
    // (subject `the temperature`, verb `sensor` — the round-10 scramble)
    // and the final-word reading (subject `the temperature sensor`, verb
    // `fails` — round 3). No lexicon-free rule picks the intended one, so
    // the class is rejected; a boundary keeps the intended reading.
    assert_eq!(
        parse("When the temperature sensor fails, the pump shall stop."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    // The rewrites: an of-chain long subject, or any role boundary.
    let s = one("When the sensor of the temperature fails, the pump shall stop.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "fails"));
    let s = one("When the temperature sensor fails at the depot, the pump shall stop.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["sensor"]);
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "fails"));
}

// ---- backtick escape hatch for reserved words (improvement round 1, change 6) ---------

#[test]
fn b01_backticked_reserved_word_as_object_head() {
    // Bare `will` is reserved everywhere (see x03 in attack_conformance);
    // backticks free it as an open-class word, kept verbatim in the tree.
    let s = one("The system shall record the `will`.");
    assert_eq!(vp(&s).object.as_ref().unwrap().heads(), vec!["`will`"]);
    // Losslessness: the render re-emits the backticks and re-parses.
    let rendered = parse("The system shall record the `will`.")
        .unwrap()
        .render();
    assert_eq!(rendered, "the system shall record the `will`.");
    assert!(parse(&rendered).is_ok());
}

#[test]
fn b02_backticked_frame_keyword_as_modifier() {
    let s = one("The `while` loop shall terminate.");
    match subject(&s) {
        NpGroup::Single(np) => {
            assert_eq!(np.modifiers, vec!["`while`".to_string()]);
            assert_eq!(np.head, "loop");
        }
        other => panic!("expected single np, got {other:?}"),
    }
    assert_eq!(vp(&s).verb, "terminate");
}

#[test]
fn b03_backticked_pivot_does_not_end_the_subject() {
    let s = one("The `shall` flag shall be set.");
    match subject(&s) {
        NpGroup::Single(np) => {
            assert_eq!(np.modifiers, vec!["`shall`".to_string()]);
            assert_eq!(np.head, "flag");
        }
        other => panic!("expected single np, got {other:?}"),
    }
    assert_eq!(vp(&s).verb, "be");
}

#[test]
fn b04_unmatched_single_backticks_are_ordinary_words() {
    let s = one("The system shall record the `will.");
    assert_eq!(vp(&s).object.as_ref().unwrap().heads(), vec!["`will"]);
    let s = one("The system shall record the will`.");
    assert_eq!(vp(&s).object.as_ref().unwrap().heads(), vec!["will`"]);
}

// ---- rejections (exact variants) ---------------------------------------------------

#[test]
fn rejects_with_exact_variants() {
    assert_eq!(parse(""), Err(ParseError::Empty));
    assert_eq!(parse("   "), Err(ParseError::Empty));
    assert_eq!(parse("."), Err(ParseError::Empty));
    assert_eq!(
        parse("The sales amount is not greater than zero."),
        Err(ParseError::NegatedDescription)
    );
    assert_eq!(
        parse("The client may not retry."),
        Err(ParseError::AmbiguousModal)
    );
    assert_eq!(
        parse("The client can retry."),
        Err(ParseError::UnsupportedModal { word: "can".into() })
    );
    assert_eq!(
        parse("When the order is submitted the system shall record the total."),
        Err(ParseError::UnterminatedFrame {
            keyword: "When".into()
        })
    );
    assert_eq!(
        parse("When , the pump shall stop."),
        Err(ParseError::EmptyFrame {
            keyword: "When".into()
        })
    );
    assert_eq!(
        parse("When the order ships, while the engine runs, the pump shall stop."),
        Err(ParseError::FrameOrder {
            keyword: "while".into(),
            after: "When".into()
        })
    );
    assert_eq!(
        parse("When x occurs, if y occurs, the pump shall stop."),
        Err(ParseError::MultipleTriggers {
            first: "When".into(),
            second: "if".into()
        })
    );
    assert_eq!(
        parse("While the engine is running, then the pump shall stop."),
        Err(ParseError::ThenWithoutIf)
    );
    assert_eq!(
        parse("While the engine is running, a workspace means a shared folder."),
        Err(ParseError::FrameOnDefinition {
            keyword: "While".into()
        })
    );
    assert_eq!(parse("The pump quickly."), Err(ParseError::MissingPivot));
    assert_eq!(parse("The shall run."), Err(ParseError::EmptySubject));
    assert_eq!(parse("The pump shall."), Err(ParseError::EmptyVp));
    assert_eq!(
        parse("The system shall record the total and or the tax."),
        Err(ParseError::MixedCoordination)
    );
    assert_eq!(
        parse("The tracing library should default export to X when no endpoint is configured."),
        Err(ParseError::MidSentenceFrame {
            keyword: "when".into()
        })
    );
}

#[test]
fn error_kinds_are_stable_names() {
    assert_eq!(ParseError::Empty.kind(), "empty");
    assert_eq!(ParseError::MissingPivot.kind(), "missing_pivot");
    assert_eq!(
        ParseError::FrameOrder {
            keyword: "x".into(),
            after: "y".into()
        }
        .kind(),
        "frame_order"
    );
}

// ---- render round-trips -------------------------------------------------------------

/// Normalize a specification for render round-trip comparison: `source` is
/// dropped (render is canonical, not verbatim) and frame keywords are folded
/// to their canonical casing, which is what render emits.
fn normalize(mut spec: Specification) -> Specification {
    for sentence in &mut spec.sentences {
        sentence.source = String::new();
        for frame in &mut sentence.frames.scopes {
            frame.keyword = "Where".to_string();
        }
        for frame in &mut sentence.frames.states {
            frame.keyword = "While".to_string();
        }
        if let Some(trigger) = &mut sentence.frames.trigger {
            trigger.keyword = match trigger.kind {
                TriggerKind::Event => "When".to_string(),
                TriggerKind::Contingency => "If".to_string(),
            };
        }
    }
    spec
}

#[test]
fn render_round_trips() {
    let corpus = [
        "The pump shall stop.",
        "The sales amount is always greater than zero.",
        "When the order is submitted, the system shall record the total.",
        "If the balance is negative, then the account shall be frozen.",
        "While the engine is running, when the temperature exceeds the limit, \
         the controller shall open the valve.",
        "A session means a sequence of requests from one client.",
        "The tracing library should install TraceContext and Baggage propagators.",
        "The gateway shall send the receipt to the customer via TLS.",
        "The pump shall stop, unless the override is active.",
        "The daemon shall persist the node, so that the auditor traces the decision.",
    ];
    for input in corpus {
        let parsed = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got {e}"));
        let rendered = parsed.render();
        let reparsed = parse(&rendered)
            .unwrap_or_else(|e| panic!("render of {input:?} must re-parse; {rendered:?} gave {e}"));
        assert_eq!(
            normalize(reparsed),
            normalize(parsed),
            "round trip diverged for {input:?} via {rendered:?}"
        );
    }
}

// ---- semantics ---------------------------------------------------------------------

#[test]
fn semantics_acts_and_projection() {
    let acts = [
        ("The pump shall stop.", SpeechAct::Obligation),
        (
            "The sales amount is always greater than zero.",
            SpeechAct::Description,
        ),
        (
            "where the premium plan is enabled, a workspace means a shared folder.",
            SpeechAct::Definition,
        ),
        ("The client may retry.", SpeechAct::Permission),
        (
            "The daemon shall not store derived views.",
            SpeechAct::Prohibition,
        ),
        (
            "The tracing library should install TraceContext and Baggage propagators.",
            SpeechAct::Recommendation,
        ),
    ];
    for (input, expected) in acts {
        assert_eq!(
            semantics::speech_act(&one(input)),
            expected,
            "for {input:?}"
        );
    }

    assert!(semantics::ingest_contract(&one(
        "where the premium plan is enabled, a workspace means a shared folder."
    ))
    .is_none());
    let contract = semantics::ingest_contract(&one("The pump shall stop.")).unwrap();
    assert_eq!(contract.assumption.render(), "⊤");

    assert_eq!(
        semantics::force(&one("The pump shall stop.")),
        Some(Force::Binding)
    );
    assert_eq!(
        semantics::force(&one("The pump must stop.")),
        Some(Force::Binding)
    );
    assert_eq!(
        semantics::force(&one("The pump should stop.")),
        Some(Force::Recommended)
    );
    assert_eq!(semantics::force(&one("The pump may stop.")), None);
    assert_eq!(semantics::force(&one("The pump is stopped.")), None);

    assert!(matches!(
        semantics::denote(&one("The client may retry.")),
        semantics::Denotation::Admissibility(_)
    ));
}

// ---- totality ----------------------------------------------------------------------

#[test]
fn totality_fixed_inputs_never_panic() {
    let inputs = [
        "€",
        "中",
        "中文",
        "南南 shall stop.",
        "🔥 shall stop",
        "th×foo shall bar",
        "When x, the×foo the pump shall stop",
        "éé shall stop.",
        "When x, 日本 the pump shall stop.",
        "×",
        "The pump shall stop..",
        "a , b",
        ",",
        "The pump shall stop, unless",
        "both and",
    ];
    for input in inputs {
        let _ = parse(input); // Ok or Err — never a panic.
    }
}

#[test]
fn totality_random_word_soups_never_panic() {
    // A tiny deterministic LCG: no dependency, reproducible failures.
    let mut state: u64 = 0x5eed_5eed_5eed_5eed;
    let mut next = move || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 33) as u32
    };
    let vocabulary = [
        "the",
        "a",
        "pump",
        "shall",
        "must",
        "may",
        "not",
        "is",
        "are",
        "means",
        "when",
        "while",
        "where",
        "if",
        "unless",
        "then",
        "so",
        "that",
        "in",
        "order",
        "to",
        "of",
        "and",
        "or",
        "both",
        "either",
        "at",
        "least",
        "most",
        "between",
        "5",
        "5.5",
        "zero",
        ",",
        ".",
        "..",
        "×",
        "café",
        "中文",
        "🔥",
        "http://192.168.10.4:4318",
        "within",
        "via",
        "per",
        "before",
        "after",
        "greater",
        "than",
        "be",
        "who",
        "remains",
    ];
    for _ in 0..1000 {
        let length = (next() % 12) as usize;
        let mut soup = String::new();
        for _ in 0..length {
            let word = vocabulary
                .get(next() as usize % vocabulary.len())
                .copied()
                .unwrap_or("pump");
            soup.push_str(word);
            if next() % 5 == 0 {
                soup.push_str(word); // occasionally glue words together
            }
            soup.push(if next() % 7 == 0 { '\t' } else { ' ' });
        }
        let _ = parse(&soup); // Ok or Err — never a panic.
    }
}

// ---- subject-level `no` in the denotation (improvement round 2, change 1) ------------

#[test]
fn n01_no_subject_prohibition_denotes_negative_action() {
    let s = one("No request shall be logged.");
    match semantics::denote(&s) {
        semantics::Denotation::Behavior(assertion) => match assertion.claim {
            semantics::Claim::Action {
                polarity: semantics::Polarity::Negative,
                force: Force::Binding,
                ..
            } => {}
            other => panic!("expected negative binding action, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    }
    // The skeleton agrees: it mirrors the claim's combined polarity.
    let sk = semantics::skeleton(&s).unwrap();
    assert_eq!(sk.polarity, semantics::Polarity::Negative);
    assert_eq!(sk.subject.quantifier, semantics::Quantifier::Negative);
}

#[test]
fn n02_no_subject_description_denotes_negative_state() {
    let s = one("No request is logged.");
    match semantics::denote(&s) {
        semantics::Denotation::Behavior(assertion) => match assertion.claim {
            semantics::Claim::State {
                polarity: semantics::Polarity::Negative,
                ..
            } => {}
            other => panic!("expected negative state, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    }
    let sk = semantics::skeleton(&s).unwrap();
    assert_eq!(sk.polarity, semantics::Polarity::Negative);
}

#[test]
fn n03_double_flip_cancels_in_the_claim() {
    // Modal `not` XOR subject `no`: the claim itself is affirmative.
    let s = one("No request shall not be logged.");
    match semantics::denote(&s) {
        semantics::Denotation::Behavior(assertion) => match assertion.claim {
            semantics::Claim::Action {
                polarity: semantics::Polarity::Affirmative,
                ..
            } => {}
            other => panic!("expected affirmative action, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    }
    assert_eq!(
        semantics::skeleton(&s).unwrap().polarity,
        semantics::Polarity::Affirmative
    );
}

#[test]
fn n04_object_no_does_not_flip_claim_polarity() {
    // Only the SUBJECT's `no` enters the denotation; `no` in object position
    // stays in the noun phrase (its scope is that phrase, not the claim).
    let s = one("The daemon shall log no request.");
    match semantics::denote(&s) {
        semantics::Denotation::Behavior(assertion) => match assertion.claim {
            semantics::Claim::Action {
                polarity: semantics::Polarity::Affirmative,
                ..
            } => {}
            other => panic!("expected affirmative action, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    }
    // The skeleton's subject rule likewise reads only the subject.
    let sk = semantics::skeleton(&s).unwrap();
    assert_eq!(sk.polarity, semantics::Polarity::Affirmative);
    assert_eq!(sk.subject.quantifier, semantics::Quantifier::Definite);
}

#[test]
fn n05_no_with_may_is_rejected() {
    assert_eq!(parse("No client may retry."), Err(ParseError::NoWithMay));
    assert_eq!(ParseError::NoWithMay.kind(), "no_with_may");
    // The message directs the author to the prohibition form.
    assert!(ParseError::NoWithMay.to_string().contains("shall not"));
    // Coordinated subjects: any item with `no` triggers it.
    assert_eq!(
        parse("The operator and no client may retry."),
        Err(ParseError::NoWithMay)
    );
    // `no` inside an of-chain is not a subject-level `no`.
    assert!(parse("The owner of no file may retry.").is_ok());
}

// ---- skeleton enrichment: roles, guards, exceptions (improvement round 2, change 2) ---

#[test]
fn e01_location_roles_distinguish_archive_from_public_bucket() {
    use semantics::{RoleKind, RoleValue};
    let archive =
        semantics::skeleton(&one("The system shall store the report in the archive.")).unwrap();
    let bucket = semantics::skeleton(&one(
        "The system shall not store the report on the public bucket.",
    ))
    .unwrap();
    // Same verb, same object digests — the pair used to collide.
    assert_eq!(archive.atoms[0].words, bucket.atoms[0].words);
    let report = vec![semantics::ObjectSkeleton {
        quantifier: semantics::Quantifier::Definite,
        head: "report".into(),
        full: "report".into(),
    }];
    assert_eq!(archive.atoms[0].objects, report);
    assert_eq!(bucket.atoms[0].objects, report);
    // The Location role digests now tell them apart.
    assert_eq!(archive.atoms[0].roles.len(), 1);
    assert_eq!(archive.atoms[0].roles[0].kind, RoleKind::Location);
    // Round 6: `full` keeps the modifiers — `public bucket`, not `bucket`.
    let loc = |head: &str, full: &str| RoleValue::Heads {
        items: vec![semantics::ObjectSkeleton {
            quantifier: semantics::Quantifier::Definite,
            head: head.into(),
            full: full.into(),
        }],
        conj: None,
    };
    assert_eq!(archive.atoms[0].roles[0].value, loc("archive", "archive"));
    assert_eq!(
        bucket.atoms[0].roles[0].value,
        loc("bucket", "public bucket")
    );
    assert_ne!(archive.atoms[0].roles, bucket.atoms[0].roles);
}

#[test]
fn e02_deadline_roles_distinguish_five_from_ten_seconds() {
    use semantics::{RoleKind, RoleValue};
    let five =
        semantics::skeleton(&one("The daemon shall flush the buffer within 5 seconds.")).unwrap();
    let ten =
        semantics::skeleton(&one("The daemon shall flush the buffer within 10 seconds.")).unwrap();
    // The pair differs ONLY in the Deadline role skeleton.
    assert_eq!(five.atoms[0].words, ten.atoms[0].words);
    assert_eq!(five.atoms[0].objects, ten.atoms[0].objects);
    assert_eq!(five.atoms[0].roles.len(), 1);
    assert_eq!(five.atoms[0].roles[0].kind, RoleKind::Deadline);
    assert_eq!(
        five.atoms[0].roles[0].value,
        RoleValue::Measure {
            number: "5".into(),
            unit: Some("seconds".into())
        }
    );
    assert_eq!(
        ten.atoms[0].roles[0].value,
        RoleValue::Measure {
            number: "10".into(),
            unit: Some("seconds".into())
        }
    );
    assert_ne!(five.atoms[0].roles, ten.atoms[0].roles);
    assert_eq!(
        (five.subject, five.polarity),
        (ten.subject.clone(), ten.polarity)
    );
}

#[test]
fn e03_guards_digest_frames() {
    let s = one("Where the cluster mode is enabled, While the pump runs, \
         When the temperature exceeds the limit, the controller shall open the valve.");
    let sk = semantics::skeleton(&s).unwrap();
    assert_eq!(sk.guards.scopes.len(), 1);
    assert_eq!(sk.guards.scopes[0].subject_head, "mode");
    assert_eq!(sk.guards.scopes[0].polarity, None);
    assert_eq!(sk.guards.scopes[0].words, vec!["enabled"]);
    assert_eq!(sk.guards.states.len(), 1);
    assert_eq!(sk.guards.states[0].subject_head, "pump");
    assert_eq!(sk.guards.states[0].words, vec!["runs"]);
    let trigger = sk.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.kind, TriggerKind::Event);
    assert_eq!(trigger.conj, None);
    assert_eq!(trigger.clauses.len(), 1);
    assert_eq!(trigger.clauses[0].subject_head, "temperature");
    assert_eq!(trigger.clauses[0].words, vec!["exceeds"]);
    // A subject `no` in a guard clause is its negation site.
    let s = one("When no endpoint is configured, the library shall use the default.");
    let sk = semantics::skeleton(&s).unwrap();
    let trigger = sk.guards.trigger.as_ref().unwrap();
    assert_eq!(
        trigger.clauses[0].polarity,
        Some(semantics::Polarity::Negative)
    );
    // An unframed sentence digests to empty guards.
    let sk = semantics::skeleton(&one("The pump shall stop.")).unwrap();
    assert_eq!(sk.guards, semantics::Guards::default());
    assert_eq!(sk.exception, None);
}

#[test]
fn e04_exception_digest() {
    let s = one("The pump shall stop, unless the override is active.");
    let sk = semantics::skeleton(&s).unwrap();
    let exception = sk.exception.as_ref().unwrap();
    assert_eq!(exception.subject_head, "override");
    assert_eq!(exception.polarity, None);
    assert_eq!(exception.words, vec!["active"]);
}

#[test]
fn e05_multi_object_coordination_heads() {
    let sk =
        semantics::skeleton(&one("The system shall store the report and the invoice.")).unwrap();
    let objects: Vec<String> = sk.atoms[0].objects.iter().map(|o| o.head.clone()).collect();
    assert_eq!(objects, vec!["report", "invoice"]);
    // State claims have no objects and no roles.
    let sk = semantics::skeleton(&one("The retry count is at most 3.")).unwrap();
    assert!(sk.atoms[0].objects.is_empty());
    assert!(sk.atoms[0].roles.is_empty());
}

// ---- one event per `and` trigger group (improvement round 2, change 3) ----------------

#[test]
fn t01_two_event_and_trigger_is_rejected() {
    // Conjunction of two occurrences is simultaneity — ill-defined.
    assert_eq!(
        parse("When the order ships and the payment clears, the system shall issue the receipt."),
        Err(ParseError::MultipleEventConjuncts)
    );
    assert_eq!(
        ParseError::MultipleEventConjuncts.kind(),
        "multiple_event_conjuncts"
    );
    // `If` triggers are held to the same rule.
    assert_eq!(
        parse("If the disk fails and the link drops, then the daemon shall alert."),
        Err(ParseError::MultipleEventConjuncts)
    );
    // Both rewrites from the message work: a copular conjunct …
    assert!(parse(
        "When the order ships and the payment is cleared, the system shall issue the receipt."
    )
    .is_ok());
    // … or a While frame carrying the second circumstance.
    assert!(parse(
        "While the payment clears, when the order ships, the system shall issue the receipt."
    )
    .is_ok());
}

#[test]
fn t02_one_event_plus_states_is_a_joint_guard() {
    let s = one(
        "When the order ships and the payment is cleared and the stock remains available, \
         the system shall pack.",
    );
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 3);
    assert!(matches!(&group.items[0].body, ClauseBody::Verbal { .. }));
    assert!(matches!(&group.items[1].body, ClauseBody::Copular { .. }));
    assert!(matches!(&group.items[2].body, ClauseBody::Copular { .. }));
}

#[test]
fn t03_or_trigger_groups_are_exempt_alternation_is_well_defined() {
    // Disjunction of events is alternation: either occurrence triggers.
    let s = one("When the order ships or the payment clears, the system shall issue the receipt.");
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::Or));
    assert!(group
        .items
        .iter()
        .all(|c| matches!(c.body, ClauseBody::Verbal { .. })));
    assert!(parse("If the disk fails or the link drops, then the daemon shall alert.").is_ok());
}

#[test]
fn t04_while_and_where_groups_are_unrestricted() {
    // A While frame is a state scope, not an occurrence: two verbal
    // conjuncts stay legal.
    let s = one("While the pump runs and the fan runs, the daemon shall wait.");
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert!(group
        .items
        .iter()
        .all(|c| matches!(c.body, ClauseBody::Verbal { .. })));
    assert!(parse("Where the pump runs and the fan runs, the daemon shall wait.").is_ok());
}
