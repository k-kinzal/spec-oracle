//! Round-4 changes, pinned: the manner slot, formula-bearing coordinated
//! subjects, formula-layer quantifier normalization, lossless atom anchors +
//! the Admissibility atom kind, typed pairing machinery, capability
//! (`is able to`), and `until` roles.

use so_lang::ast::*;
use so_lang::formula::{
    applicability, claim_formula, contract_formula, AssumptionSource, AtomRef, BehaviorAtom,
    ContractFormula, EdgeKind, Formula,
};
use so_lang::parse::{parse, ParseError};
use so_lang::semantics::{
    denote, force, ingest_contract, skeleton, speech_act, Claim, Denotation, Polarity, Quantifier,
    RoleKind, RoleValue, SpeechAct,
};

/// Parse an input expected to hold exactly one sentence.
fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn deontic_vp(s: &Sentence) -> &Vp {
    match &s.core {
        Core::Deontic { vp, .. } => vp.single().expect("single vp fixture"),
        other => panic!("expected deontic core, got {other:?}"),
    }
}

/// Render must be a fixpoint and re-parse to the same tree.
fn render_round_trips(s: &Sentence) {
    let rendered = s.render();
    let r = one(&rendered);
    assert_eq!(
        (&s.frames, &s.core, &s.exception, &s.purpose),
        (&r.frames, &r.core, &r.exception, &r.purpose),
        "render {rendered:?} must re-parse to the same tree"
    );
    assert_eq!(
        r.render(),
        rendered,
        "render must be a fixpoint for {rendered:?}"
    );
}

// ====================================================================================
// 1. The manner slot
// ====================================================================================

#[test]
fn bare_postverbal_ly_word_is_manner_not_object() {
    // The motivating sentence: `immediately` was previously the OBJECT head.
    let s = one("The pump shall stop immediately.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "stop");
    assert_eq!(vp.manner, vec!["immediately"]);
    assert!(vp.object.is_none(), "a manner adverb is not an object");
    assert!(vp.roles.is_empty());
    render_round_trips(&s);
}

#[test]
fn clause_final_ly_word_is_manner_not_the_verb() {
    // The motivating clause: `successfully` was previously the clause VERB.
    let s = one("When the export completes successfully, the daemon shall archive the export.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal {
            verb,
            particle,
            manner,
            object,
            roles,
            ..
        } => {
            assert_eq!(verb, "completes");
            assert_eq!(particle, &None);
            assert_eq!(manner, &vec!["successfully".to_string()]);
            assert!(object.is_none());
            assert!(roles.is_empty());
        }
        other => panic!("expected verbal clause body, got {other:?}"),
    }
    assert_eq!(trigger.clause.items[0].subject.heads(), vec!["export"]);
    render_round_trips(&s);
}

#[test]
fn manner_composes_with_particle_and_deadline() {
    let s = one("The daemon shall shut down gracefully within 5 seconds.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "shut");
    assert_eq!(vp.particle.as_deref(), Some("down"));
    assert_eq!(vp.manner, vec!["gracefully"]);
    assert!(vp.object.is_none());
    assert!(matches!(vp.roles.as_slice(), [RolePp::Deadline(_)]));
    render_round_trips(&s);

    // Manner + particle in a clause, with the boundary heuristic (a role
    // preposition follows).
    let s = one("When the user logs out quickly before the timer expires, the session shall end.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal {
            verb,
            particle,
            manner,
            roles,
            ..
        } => {
            assert_eq!(verb, "logs");
            assert_eq!(particle.as_deref(), Some("out"));
            assert_eq!(manner, &vec!["quickly".to_string()]);
            assert!(matches!(roles.as_slice(), [RolePp::Before(_)]));
        }
        other => panic!("expected verbal clause body, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn ly_words_inside_noun_phrases_stay_untouched() {
    // As an NP head after a determiner.
    let s = one("The system shall verify the assembly.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["assembly"]);
    // As a modifier before a head.
    let s = one("The nightly build is green.");
    match &s.core {
        Core::Description { subject, .. } => match subject {
            NpGroup::Single(np) => {
                assert_eq!(np.modifiers, vec!["nightly".to_string()]);
                assert_eq!(np.head, "build");
            }
            other => panic!("expected single subject, got {other:?}"),
        },
        other => panic!("expected description, got {other:?}"),
    }
    // `exactly` opens a quantifier, never a manner run.
    let s = one("The daemon shall retain exactly 7 copies.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(
        vp.object.as_ref().unwrap().heads(),
        vec!["copies"],
        "`exactly 7` stays the object's quantifier"
    );
}

#[test]
fn backticks_turn_a_bare_ly_word_back_into_an_object() {
    // The documented tradeoff: a bare `ly` word the author means as a noun
    // object needs backticks.
    let s = one("The system shall record `supply`.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["`supply`"]);
    render_round_trips(&s);
    // Without backticks the positional rule reads it as manner.
    let s = one("The system shall record supply.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.manner, vec!["supply"]);
    assert!(vp.object.is_none());
}

#[test]
fn juxtaposed_manner_words_only_a_conjunction_ends_the_run() {
    // Juxtaposition extends the run.
    let s = one("The daemon shall stop immediately gracefully.");
    assert_eq!(deontic_vp(&s).manner, vec!["immediately", "gracefully"]);
    render_round_trips(&s);
    // A conjunction after a manner word ends the run; the leftover has no
    // place in the grammar (legislated: `quickly and safely` unsupported).
    assert_eq!(
        parse("The pump shall stop quickly and safely."),
        Err(ParseError::UnexpectedTokens {
            token: "and".into()
        })
    );
}

#[test]
fn manner_reaches_the_skeleton_without_entering_words() {
    let sk = skeleton(&one("The pump shall stop Immediately.")).unwrap();
    assert_eq!(
        sk.atoms[0].words,
        vec!["stop"],
        "words do not absorb manner"
    );
    assert_eq!(
        sk.atoms[0].manner,
        vec!["immediately"],
        "manner is lowercased"
    );
    assert!(sk.atoms[0].objects.is_empty());
    // A manner-free atom differs from the mannered one exactly in `manner`.
    let plain = skeleton(&one("The pump shall stop.")).unwrap();
    assert!(plain.atoms[0].manner.is_empty());
    assert_eq!(plain.atoms[0].words, sk.atoms[0].words);
    assert_ne!(plain.atoms[0], sk.atoms[0]);
    // Clause digests carry manner beside (not inside) their words.
    let sk = skeleton(&one(
        "When the export completes successfully, the daemon shall archive the export.",
    ))
    .unwrap();
    let trigger = sk.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.clauses[0].words, vec!["completes"]);
    assert_eq!(trigger.clauses[0].manner, vec!["successfully"]);
}

#[test]
fn manner_serializes_in_tree_and_skeleton() {
    let s = one("The session shall time out immediately within 30 seconds.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.particle.as_deref(), Some("out"));
    assert_eq!(vp.manner, vec!["immediately"]);
    let json = serde_json::to_value(&s).unwrap();
    assert_eq!(
        json["core"]["vp"]["manner"],
        serde_json::json!(["immediately"])
    );
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
    let sk = skeleton(&s).unwrap();
    let json = serde_json::to_value(&sk).unwrap();
    assert_eq!(
        json["atoms"][0]["manner"],
        serde_json::json!(["immediately"])
    );
    render_round_trips(&s);
}

// ====================================================================================
// 2. Coordinated subjects are formula-bearing
// ====================================================================================

/// The behavior atom inside a formula that must be a bare (unnegated) atom.
fn behavior(f: &Formula) -> &BehaviorAtom {
    match f {
        Formula::Atom {
            atom: AtomRef::Behavior { behavior },
        } => behavior,
        other => panic!("expected bare behavior atom, got {other:?}"),
    }
}

/// The behavior atom inside `Not(atom)`.
fn negated_behavior(f: &Formula) -> &BehaviorAtom {
    match f {
        Formula::Not { inner } => behavior(inner),
        other => panic!("expected negated behavior atom, got {other:?}"),
    }
}

#[test]
fn coordinated_and_subject_conjoins_per_item_atoms() {
    let f = claim_formula(&one("The pump and the valve shall stop.")).unwrap();
    match &f {
        Formula::And { items } => {
            assert_eq!(items.len(), 2);
            let (pump, valve) = (behavior(&items[0]), behavior(&items[1]));
            assert_eq!(pump.subject.head, "pump");
            assert_eq!(valve.subject.head, "valve");
            // Same kernel per item.
            assert_eq!(pump.atom, valve.atom);
            assert_eq!(pump.atom.words, vec!["stop"]);
            // Per-item anchors.
            assert_eq!(pump.source, "the pump shall stop");
            assert_eq!(valve.source, "the valve shall stop");
        }
        other => panic!("expected conjunction, got {other:?}"),
    }
    // The contract exists now (superseded round-3 pin) and its guarantee is
    // the claim itself for this unconditional sentence.
    let c = contract_formula(&one("The pump and the valve shall stop.")).unwrap();
    assert_eq!(c.assumption, Formula::Top);
    assert_eq!(c.guarantee, f);
    // The skeleton (the index) stays single-subject.
    assert!(skeleton(&one("The pump and the valve shall stop.")).is_none());
}

#[test]
fn coordinated_or_subject_and_group_markers() {
    match claim_formula(&one("The pump or the valve shall stop.")).unwrap() {
        Formula::Or { items } => assert_eq!(items.len(), 2),
        other => panic!("expected disjunction, got {other:?}"),
    }
    // Markers do not change the logic: `both … and` = `… and`, `either …
    // or` = `… or` (modulo per-item anchors, which render the same items).
    assert_eq!(
        claim_formula(&one("Both the pump and the valve shall stop.")).unwrap(),
        claim_formula(&one("The pump and the valve shall stop.")).unwrap()
    );
    assert_eq!(
        claim_formula(&one("Either the pump or the valve shall stop.")).unwrap(),
        claim_formula(&one("The pump or the valve shall stop.")).unwrap()
    );
}

#[test]
fn negative_polarity_distributes_not_per_atom() {
    // `shall not run` over and-subjects = ∧ᵢ ¬run(subjectᵢ).
    match claim_formula(&one("The pump and the valve shall not run.")).unwrap() {
        Formula::And { items } => {
            assert_eq!(items.len(), 2);
            assert_eq!(negated_behavior(&items[0]).subject.head, "pump");
            assert_eq!(negated_behavior(&items[1]).subject.head, "valve");
        }
        other => panic!("expected conjunction of negations, got {other:?}"),
    }
    // The same distribution under `or`.
    match claim_formula(&one("The pump or the valve shall not run.")).unwrap() {
        Formula::Or { items } => {
            assert_eq!(negated_behavior(&items[0]).subject.head, "pump");
            assert_eq!(negated_behavior(&items[1]).subject.head, "valve");
        }
        other => panic!("expected disjunction of negations, got {other:?}"),
    }
}

#[test]
fn coordinated_contract_serializes() {
    let c = contract_formula(&one(
        "When the order ships, the pump and the valve shall stop.",
    ))
    .unwrap();
    let json = serde_json::to_value(&c).unwrap();
    let back: ContractFormula = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(back, c);
    assert_eq!(json["guarantee"]["items"][1]["kind"], "and");
}

// ====================================================================================
// 3. Formula-layer quantifier normalization (index vs logic)
// ====================================================================================

#[test]
fn subject_no_normalizes_to_universal_under_one_not() {
    // `No daemon shall sleep.` → Not(atom{daemon, Universal}).
    let f = claim_formula(&one("No daemon shall sleep.")).unwrap();
    let b = negated_behavior(&f);
    assert_eq!(b.subject.head, "daemon");
    assert_eq!(b.subject.quantifier, Quantifier::Universal);
    // The skeleton — the surface index — keeps Negative: the two views
    // intentionally differ on `no`.
    let sk = skeleton(&one("No daemon shall sleep.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Negative);
}

#[test]
fn double_negation_yields_bare_universal_atom() {
    // `No request shall not be logged.`: combined polarity Affirmative, so
    // the atom stands un-negated with a Universal subject — first-order
    // sound: no X: ¬P ≡ ∀X P.
    let no = claim_formula(&one("No request shall not be logged.")).unwrap();
    let each = claim_formula(&one("Each request shall be logged.")).unwrap();
    let (no_b, each_b) = (behavior(&no), behavior(&each));
    // The normalized forms agree on subject digest and kernel; only the
    // surface anchor and the pivot-read speech act still tell them apart.
    assert_eq!(no_b.subject, each_b.subject);
    assert_eq!(no_b.subject.quantifier, Quantifier::Universal);
    assert_eq!(no_b.atom, each_b.atom);
    assert_eq!(no_b.force, each_b.force);
    assert_eq!(no_b.source, "no request shall not be logged");
    assert_eq!(each_b.source, "each request shall be logged");
}

// ====================================================================================
// 4. Lossless atom anchors + the Admissibility atom kind
// ====================================================================================

#[test]
fn anchors_reparse_to_the_digested_material() {
    let s = one(
        "When the disk fails, the daemon shall alert the operator within 5 seconds, \
         unless the override is active, so that the operator reacts.",
    );
    // The behavior anchor: subject + claim, no frames/exception/purpose —
    // re-parses to a sentence whose core matches this one's.
    let c = contract_formula(&s).unwrap();
    let claim = match &c.guarantee {
        Formula::Or { items } => &items[1],
        other => panic!("expected conditional guarantee, got {other:?}"),
    };
    let b = behavior(claim);
    assert_eq!(
        b.source,
        "the daemon shall alert the operator within 5 seconds"
    );
    let reparsed = one(&format!("{}.", b.source));
    assert_eq!(
        reparsed.core, s.core,
        "the anchor re-parses to the digested core"
    );
    // The guard anchor: the clause render — re-parses (as a frame clause)
    // to the same clause.
    let app = applicability(&s);
    let guard_source = match &app {
        Formula::And { items } => match &items[0] {
            Formula::Atom {
                atom: AtomRef::Guard { source, .. },
            } => source.clone(),
            other => panic!("expected guard atom, got {other:?}"),
        },
        other => panic!("expected conjunction, got {other:?}"),
    };
    assert_eq!(guard_source, "the disk fails");
    let framed = one(&format!("When {guard_source}, the pump shall stop."));
    assert_eq!(
        framed.frames.trigger.as_ref().unwrap().clause,
        s.frames.trigger.as_ref().unwrap().clause,
        "the guard anchor re-parses to the digested clause"
    );
}

#[test]
fn permissions_produce_admissibility_atoms() {
    let f = claim_formula(&one("The client may retry.")).unwrap();
    match &f {
        Formula::Atom {
            atom: AtomRef::Admissibility { behavior },
        } => {
            assert_eq!(behavior.subject.head, "client");
            assert_eq!(behavior.atom.words, vec!["retry"]);
            assert_eq!(behavior.force, None);
            assert_eq!(behavior.source, "the client may retry");
        }
        other => panic!("expected admissibility atom, got {other:?}"),
    }
    // Still no lone contract: admissibility pairs on the environment side.
    assert!(contract_formula(&one("The client may retry.")).is_none());
    // Wire shape: its own kind tag, with the anchor visible.
    let json = serde_json::to_value(&f).unwrap();
    assert_eq!(json["atom"]["kind"], "admissibility");
    assert_eq!(json["atom"]["behavior"]["source"], "the client may retry");
    let back: Formula = serde_json::from_value(json).unwrap();
    assert_eq!(back, f);
}

#[test]
fn behavior_atoms_serialize_with_their_anchor() {
    let f = claim_formula(&one("The pump shall stop.")).unwrap();
    let json = serde_json::to_value(&f).unwrap();
    assert_eq!(json["atom"]["kind"], "behavior");
    assert_eq!(json["atom"]["behavior"]["source"], "the pump shall stop");
    let back: Formula = serde_json::from_value(json).unwrap();
    assert_eq!(back, f);
}

// ====================================================================================
// 5. Typed pairing machinery
// ====================================================================================

#[test]
fn paired_replaces_the_provisional_top_assumption() {
    let c = contract_formula(&one("The daemon shall alert.")).unwrap();
    assert_eq!(c.assumption, Formula::Top);
    let a1 = claim_formula(&one("The monitor shall detect the fault.")).unwrap();
    let a2 = claim_formula(&one("The network may drop packets.")).unwrap();
    // Round 5: sources are built through the validating constructor; the
    // pairing algebra pinned here is unchanged. Round 11 (change 3): the
    // discharge source selects its reliance EXPLICITLY — a default-relied
    // source is a permanent candidate now and never forms A.
    let target = one("The daemon shall alert.");
    let monitor = one("The monitor shall detect the fault.");
    let sources = [
        AssumptionSource::for_guarantee_with_relied(
            EdgeKind::GuaranteeDischarge,
            &monitor,
            &target,
            a1.clone(),
        )
        .unwrap(),
        AssumptionSource::from_sentence(
            EdgeKind::AdmissibilityEnvelope,
            &one("The network may drop packets."),
        )
        .unwrap(),
    ];
    let paired = c.paired(&sources);
    // The causal pair ⇒ G: assumption REPLACED (supersession, not
    // conjunction with ⊤), guarantee untouched. Round 6 (supersedes the
    // round-4/5 shape): the ENVELOPE source is compatibility data, not an
    // assumption conjunct — negating a permission under saturation would
    // misread it as a behavior-set complement — so A is the discharge
    // formula alone; the envelope stays in `sources`.
    let _ = &a2; // the envelope's formula, deliberately absent from A
    assert_eq!(paired.assumption, a1.clone());
    assert_eq!(paired.sources.len(), 2);
    assert_eq!(paired.guarantee, c.guarantee);
    // A single source stands alone.
    let single = c.paired(&sources[..1]);
    assert_eq!(single.assumption, a1);
    // Saturation over the paired contract: G ∨ ¬(∧ᵢAᵢ).
    match paired.saturated() {
        Formula::Or { items } => {
            assert_eq!(items[0], paired.guarantee);
            assert_eq!(
                items[1],
                Formula::Not {
                    inner: Box::new(paired.assumption.clone())
                }
            );
        }
        other => panic!("expected saturated disjunction, got {other:?}"),
    }
    // Empty sources: identity — still the lone (⊤, G).
    assert_eq!(c.paired(&[]), c);
}

// ====================================================================================
// 6. Capability (`is able to`) and `until`
// ====================================================================================

#[test]
fn able_to_parses_as_a_capability_predicate() {
    let s = one("The client is able to retry.");
    match &s.core {
        Core::Description {
            copula: Copula::Is,
            adverb: None,
            predicate,
            ..
        } => match predicate {
            Predicate::AbleTo { vp } => {
                assert_eq!(vp.verb, "retry");
                assert!(vp.object.is_none());
            }
            other => panic!("expected able-to predicate, got {other:?}"),
        },
        other => panic!("expected description core, got {other:?}"),
    }
    render_round_trips(&s);
    // Surface classification stays a description with no force; the
    // denotation is behavior through the capability's verb phrase.
    assert_eq!(speech_act(&s), SpeechAct::Description);
    assert_eq!(force(&s), None);
    match denote(&s) {
        Denotation::Behavior(assertion) => match assertion.claim {
            Claim::Capability { vp, .. } => assert_eq!(vp.verb, "retry"),
            other => panic!("expected capability claim, got {other:?}"),
        },
        other => panic!("expected behavior denotation, got {other:?}"),
    }
    // Like other descriptions, a capability ingests as (⊤, G).
    assert!(ingest_contract(&s).is_some());
    assert!(contract_formula(&s).is_some());
    // The skeleton digests the capability's verb phrase.
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.atoms[0].words, vec!["retry"]);
    assert_eq!(sk.act, SpeechAct::Description);
    assert_eq!(sk.force, None);
    assert_eq!(sk.polarity, Polarity::Affirmative);
}

#[test]
fn able_to_carries_the_full_verb_phrase_grammar() {
    let s = one("The daemon is able to shut down gracefully within 5 seconds.");
    match &s.core {
        Core::Description {
            predicate: Predicate::AbleTo { vp },
            ..
        } => {
            assert_eq!(vp.verb, "shut");
            assert_eq!(vp.particle.as_deref(), Some("down"));
            assert_eq!(vp.manner, vec!["gracefully"]);
            assert!(matches!(vp.roles.as_slice(), [RolePp::Deadline(_)]));
        }
        other => panic!("expected able-to predicate, got {other:?}"),
    }
    render_round_trips(&s);
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.atoms[0].words, vec!["shut", "down"]);
    assert_eq!(sk.atoms[0].manner, vec!["gracefully"]);
}

#[test]
fn no_subject_denies_the_capability() {
    let s = one("No client is able to retry.");
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.polarity, Polarity::Negative);
    assert_eq!(
        sk.subject.quantifier,
        Quantifier::Negative,
        "the index keeps the surface `no`"
    );
    // The formula: Not(atom{client, Universal}) — an ordinary Behavior atom
    // (a capability claim is a descriptive behavior property).
    let f = claim_formula(&s).unwrap();
    let b = negated_behavior(&f);
    assert_eq!(b.subject.head, "client");
    assert_eq!(b.subject.quantifier, Quantifier::Universal);
    assert_eq!(b.source, "no client is able to retry");
}

#[test]
fn able_to_needs_the_exact_postcopular_position() {
    // SUPERSEDED PIN (round 5, change 7): `is always able to <vp>` is now
    // capability with the adverb kept, not an open-word predicate (round 4
    // had pinned the fallback reading).
    let s = one("The client is always able to retry.");
    match &s.core {
        Core::Description {
            adverb: Some(DescriptionAdverb::Always),
            predicate: Predicate::AbleTo { vp },
            ..
        } => assert_eq!(vp.verb, "retry"),
        other => panic!("expected adverbed capability, got {other:?}"),
    }
    // `can` remains rejected; the hint now names the faithful rewrite.
    let err = parse("The client can retry.").unwrap_err();
    assert_eq!(err, ParseError::UnsupportedModal { word: "can".into() });
    assert!(
        err.to_string().contains("is able to"),
        "hint mentions the rewrite: {err}"
    );
    // An empty capability is an empty verb phrase.
    assert_eq!(parse("The client is able to."), Err(ParseError::EmptyVp));
}

#[test]
fn until_is_a_clausal_role() {
    let s = one("The pump shall run until the tank is empty.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "run");
    match vp.roles.as_slice() {
        [RolePp::Until(clause)] => {
            assert_eq!(clause.subject.heads(), vec!["tank"]);
            assert!(matches!(clause.body, ClauseBody::Copular { .. }));
        }
        other => panic!("expected one Until role, got {other:?}"),
    }
    render_round_trips(&s);
    // Skeleton: a clausal digest, same as before/after.
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.atoms[0].roles.len(), 1);
    assert_eq!(sk.atoms[0].roles[0].kind, RoleKind::Until);
    // Round 8, change 1 (pin updated): the clause value carries the full
    // nested skeleton + full render.
    match &sk.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.subject_head, "tank");
            assert_eq!(skeleton.words, vec!["empty"]);
            assert_eq!(full, "the tank is empty");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    // Serde tag.
    let json = serde_json::to_value(&s).unwrap();
    assert_eq!(json["core"]["vp"]["roles"][0]["role"], "until");
}

#[test]
fn until_works_in_guard_clauses_and_respects_the_depth_budget() {
    // A verbal frame clause carries `until` like any other role.
    let s = one("While the daemon runs until the queue drains, the light shall glow.");
    let state = &s.frames.states[0];
    match &state.clause.items[0].body {
        ClauseBody::Verbal { verb, roles, .. } => {
            assert_eq!(verb, "runs");
            assert!(matches!(roles.as_slice(), [RolePp::Until(_)]));
        }
        other => panic!("expected verbal guard clause, got {other:?}"),
    }
    render_round_trips(&s);
    // The same depth accounting as before/after: adversarial nesting is an
    // error, not an abort.
    let deep = format!("The pump shall run{}.", " until the pump runs".repeat(70));
    assert!(matches!(
        parse(&deep),
        Err(ParseError::PhraseTooDeep { .. })
    ));
}

#[test]
fn pairing_types_serialize() {
    // Round 5: sources carry validated provenance (act + force).
    let source = AssumptionSource::from_sentence(
        EdgeKind::OccurrenceReliance,
        &one("The clock shall tick."),
    )
    .unwrap();
    let json = serde_json::to_value(&source).unwrap();
    assert_eq!(json["kind"], "occurrence_reliance");
    assert_eq!(json["act"], "obligation");
    assert_eq!(json["force"], "binding");
    let back: AssumptionSource = serde_json::from_value(json).unwrap();
    assert_eq!(back, source);
}
