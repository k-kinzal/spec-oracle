//! Round 5 pins: validated typed pairing, generic behavioral subjects,
//! the relation engine, modifier-bearing subject keys, legislated
//! `for`/`with`/`by`, relative attachment, and adverbial capability.

use so_lang::ast::*;
use so_lang::formula::{
    claim_formula, contract_formula, AssumptionSource, AtomRef, EdgeKind, Formula,
    PairingError,
};
use so_lang::parse::{parse, ParseError};
use so_lang::semantics::{skeleton, subject_keys, Quantifier};

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap();
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

/// Render must re-parse to the same tree (source text aside) and be a
/// fixpoint.
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
// 1. Typed pairing retained and validated
// ====================================================================================

#[test]
fn pairing_matrix_allowed_and_denied_per_act() {
    use EdgeKind::*;
    // (sentence, allowed kinds, error for a denied kind)
    let cases: &[(&str, &[EdgeKind], PairingError)] = &[
        (
            "The client may retry.",
            &[AdmissibilityEnvelope],
            PairingError::PermissionOnlyEnvelope,
        ),
        (
            "The library should install propagators.",
            &[OccurrenceReliance],
            PairingError::RecommendationOnlyReliance,
        ),
        (
            "The sensor shall send the signal.",
            &[GuaranteeDischarge, OccurrenceReliance],
            PairingError::BindingNoEnvelope,
        ),
        (
            "The daemon shall not sleep.",
            &[GuaranteeDischarge, OccurrenceReliance],
            PairingError::BindingNoEnvelope,
        ),
        (
            "The buffer is empty.",
            &[OccurrenceReliance],
            PairingError::DescriptionOnlyReliance,
        ),
        (
            "The client is able to retry.",
            &[OccurrenceReliance],
            PairingError::DescriptionOnlyReliance,
        ),
    ];
    let all = [OccurrenceReliance, GuaranteeDischarge, AdmissibilityEnvelope];
    for (input, allowed, denial) in cases {
        let sentence = one(input);
        for kind in all {
            let result = AssumptionSource::from_sentence(kind, &sentence);
            if allowed.contains(&kind) {
                let source = result.unwrap_or_else(|e| panic!("{input:?} × {kind:?}: {e}"));
                assert_eq!(source.kind, kind);
                assert_eq!(source.act, so_lang::semantics::speech_act(&sentence));
            } else {
                assert_eq!(result.unwrap_err(), *denial, "{input:?} × {kind:?}");
            }
        }
    }
    // A definition is not behavioral under ANY kind.
    let definition = one("A session means a sequence of requests.");
    for kind in all {
        assert_eq!(
            AssumptionSource::from_sentence(kind, &definition).unwrap_err(),
            PairingError::NotBehavioral
        );
    }
}

#[test]
fn pairing_error_kinds_are_stable() {
    assert_eq!(PairingError::PermissionOnlyEnvelope.kind(), "permission_only_envelope");
    assert_eq!(
        PairingError::RecommendationOnlyReliance.kind(),
        "recommendation_only_reliance"
    );
    assert_eq!(PairingError::BindingNoEnvelope.kind(), "binding_no_envelope");
    assert_eq!(PairingError::DescriptionOnlyReliance.kind(), "description_only_reliance");
    assert_eq!(PairingError::NotBehavioral.kind(), "not_behavioral");
}

#[test]
fn source_formula_is_the_guarded_claim() {
    // The source formula has the same shape as a guarantee: applicability →
    // claim, with Top applicability simplified away.
    let unconditional = one("The sensor shall send the signal.");
    let source =
        AssumptionSource::from_sentence(EdgeKind::GuaranteeDischarge, &unconditional).unwrap();
    assert_eq!(source.formula, claim_formula(&unconditional).unwrap());
    let conditional = one("When the order ships, the sensor shall send the signal.");
    let source =
        AssumptionSource::from_sentence(EdgeKind::GuaranteeDischarge, &conditional).unwrap();
    assert_eq!(
        source.formula,
        contract_formula(&conditional).unwrap().guarantee,
        "a conditional source contributes its own conditional"
    );
    assert_eq!(source.force, Some(so_lang::semantics::Force::Binding));
}

#[test]
fn paired_retains_its_sources_and_saturation_is_unchanged() {
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    assert!(c.sources.is_empty(), "ingest contracts carry no sources");
    // Round 11 (change 3): the discharge selects its reliance explicitly —
    // a default-relied source is a permanent candidate and never forms A.
    let sensor = one("The sensor shall send the signal.");
    let relied =
        AssumptionSource::from_sentence(EdgeKind::GuaranteeDischarge, &sensor).unwrap().formula;
    let a1 = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::GuaranteeDischarge,
        &sensor,
        &one("The pump shall stop."),
        relied,
    )
    .unwrap();
    let a2 = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
    )
    .unwrap();
    let paired = c.paired(&[a1.clone(), a2.clone()]);
    // Sources retained, in order, with their kinds.
    assert_eq!(paired.sources, vec![a1.clone(), a2.clone()]);
    // Round 6 (supersedes the round-5 shape that conjoined the envelope):
    // an envelope WIDENS tolerated environment behavior — negating it under
    // saturation would read the permission as a behavior-set complement —
    // so the assumption is derived from the NON-envelope sources only. The
    // envelope stays in `sources` as compatibility data.
    assert_eq!(paired.assumption, a1.formula.clone());
    // Saturation negates only the non-envelope assumption: G ∨ ¬A₁.
    assert_eq!(
        paired.saturated(),
        Formula::Or {
            items: vec![
                paired.guarantee.clone(),
                Formula::Not { inner: Box::new(a1.formula.clone()) },
            ],
        }
    );
    // Empty sources: identity, sources stay empty.
    assert_eq!(c.paired(&[]), c);
}

#[test]
fn pairing_serde_round_trips_with_provenance() {
    let source = AssumptionSource::from_sentence(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
    )
    .unwrap();
    let v = serde_json::to_value(&source).unwrap();
    assert_eq!(v["kind"], "admissibility_envelope");
    assert_eq!(v["act"], "permission");
    assert_eq!(v["force"], serde_json::Value::Null);
    assert_eq!(serde_json::from_value::<AssumptionSource>(v).unwrap(), source);
    // A paired contract round-trips with its sources …
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    let paired = c.paired(std::slice::from_ref(&source));
    let v = serde_json::to_value(&paired).unwrap();
    assert_eq!(v["sources"][0]["kind"], "admissibility_envelope");
    assert_eq!(
        serde_json::from_value::<so_lang::formula::ContractFormula>(v).unwrap(),
        paired
    );
    // … and a pre-round-5 contract (no `sources` field) still deserializes.
    let old = serde_json::json!({
        "assumption": { "kind": "top" },
        "guarantee": { "kind": "top" },
    });
    let back: so_lang::formula::ContractFormula = serde_json::from_value(old).unwrap();
    assert!(back.sources.is_empty());
}

// ====================================================================================
// 3. Minimal relation engine
// ====================================================================================

mod relate {
    use super::*;
    use so_lang::relate::{contradicts, implies, refines, Ternary};

    fn contract(input: &str) -> so_lang::formula::ContractFormula {
        contract_formula(&one(input)).unwrap()
    }

    fn claim(input: &str) -> Formula {
        claim_formula(&one(input)).unwrap()
    }

    #[test]
    fn equal_sentences_imply_both_ways() {
        let a = claim("The pump shall stop.");
        assert_eq!(implies(&a, &a), Ternary::Yes);
        // Same proposition through different acts: description vs obligation.
        let described = claim("The request is logged.");
        let obliged = claim("The request shall be logged.");
        assert_eq!(implies(&described, &obliged), Ternary::Yes);
        assert_eq!(implies(&obliged, &described), Ternary::Yes);
    }

    #[test]
    fn plainly_different_claims_are_unknown() {
        let a = claim("The pump shall stop.");
        let b = claim("The valve shall open.");
        assert_eq!(implies(&a, &b), Ternary::Unknown);
        assert_eq!(contradicts(&a, &b), Ternary::Unknown, "Unknown is not No");
    }

    #[test]
    fn deadline_refinement_orders_numerically() {
        let tight = claim("The daemon shall respond within 5 seconds.");
        let loose = claim("The daemon shall respond within 10 seconds.");
        assert_eq!(implies(&tight, &loose), Ternary::Yes);
        assert_eq!(implies(&loose, &tight), Ternary::Unknown);
        // Number words parse too.
        let words = claim("The daemon shall respond within five seconds.");
        assert_eq!(implies(&words, &loose), Ternary::Yes);
    }

    #[test]
    fn unit_mismatch_is_unknown() {
        let seconds = claim("The daemon shall respond within 5 seconds.");
        let ms = claim("The daemon shall respond within 10 ms.");
        assert_eq!(implies(&seconds, &ms), Ternary::Unknown);
        let bare = claim("The daemon shall respond within 5.");
        assert_eq!(implies(&bare, &seconds), Ternary::Unknown);
    }

    #[test]
    fn retry_count_comparison_refines_end_to_end() {
        // The round-5 flagship case, through parsed description comparisons.
        let concrete = contract("The retry count is at most 3.");
        let abstract_ = contract("The retry count is at most 5.");
        assert_eq!(refines(&concrete, &abstract_), Ternary::Yes);
        assert_eq!(refines(&abstract_, &concrete), Ternary::Unknown);
        // Lower bounds refine upward.
        let concrete = contract("The replica count is at least 5.");
        let abstract_ = contract("The replica count is at least 3.");
        assert_eq!(refines(&concrete, &abstract_), Ternary::Yes);
    }

    #[test]
    fn deadline_contract_refines_on_saturated_forms() {
        let concrete = contract("When the order ships, the daemon shall respond within 5 seconds.");
        let abstract_ =
            contract("When the order ships, the daemon shall respond within 10 seconds.");
        assert_eq!(refines(&concrete, &abstract_), Ternary::Yes);
    }

    #[test]
    fn prohibition_contradicts_obligation_on_one_proposition() {
        let obliged = claim("The pump shall stop.");
        let forbidden = claim("The pump shall not stop.");
        assert_eq!(contradicts(&obliged, &forbidden), Ternary::Yes);
        assert_eq!(contradicts(&forbidden, &obliged), Ternary::Yes);
        // A claim never contradicts itself.
        assert_eq!(contradicts(&obliged, &obliged), Ternary::No);
        // Description `never` against the obligation, same proposition.
        let never = claim("The pump is never stopped.");
        let stopped = claim("The pump shall be stopped.");
        assert_eq!(contradicts(&never, &stopped), Ternary::Yes);
    }

    #[test]
    fn no_subject_normalized_pair_is_equivalent() {
        // `No request shall be logged.` ≡ `Each request shall not be logged.`
        // — the round-4 normalization, now a computed equivalence.
        let no = claim("No request shall be logged.");
        let each_not = claim("Each request shall not be logged.");
        assert_eq!(implies(&no, &each_not), Ternary::Yes);
        assert_eq!(implies(&each_not, &no), Ternary::Yes);
        // And both contradict the positive universal.
        let each = claim("Each request shall be logged.");
        assert_eq!(contradicts(&no, &each), Ternary::Yes);
    }

    #[test]
    fn boolean_structure_simplifies_syntactically() {
        let a = claim("The pump shall stop.");
        let top = Formula::Top;
        let bottom = Formula::Bottom;
        // Constant folding and idempotence.
        assert_eq!(
            implies(&Formula::And { items: vec![a.clone(), top.clone()] }, &a),
            Ternary::Yes
        );
        assert_eq!(
            implies(&Formula::Or { items: vec![a.clone(), bottom.clone()] }, &a),
            Ternary::Yes
        );
        assert_eq!(
            implies(&Formula::And { items: vec![a.clone(), a.clone()] }, &a),
            Ternary::Yes
        );
        // Bottom implies anything; anything implies Top.
        assert_eq!(implies(&bottom, &a), Ternary::Yes);
        assert_eq!(implies(&a, &top), Ternary::Yes);
        assert_eq!(implies(&top, &bottom), Ternary::No);
        // Conjunction elimination / disjunction introduction.
        let b = claim("The valve shall open.");
        let both = Formula::And { items: vec![a.clone(), b.clone()] };
        let either = Formula::Or { items: vec![a.clone(), b.clone()] };
        assert_eq!(implies(&both, &a), Ternary::Yes);
        assert_eq!(implies(&a, &either), Ternary::Yes);
        assert_eq!(implies(&both, &either), Ternary::Yes);
        assert_eq!(implies(&either, &a), Ternary::Unknown);
        // Absorption: a ∧ (a ∨ b) = a.
        let absorbed = Formula::And { items: vec![a.clone(), either.clone()] };
        assert_eq!(implies(&absorbed, &a), Ternary::Yes);
        assert_eq!(implies(&a, &absorbed), Ternary::Yes);
        // Double negation via contraposition.
        let not_not_a =
            Formula::Not { inner: Box::new(Formula::Not { inner: Box::new(a.clone()) }) };
        assert_eq!(implies(&not_not_a, &a), Ternary::Yes);
    }

    #[test]
    fn admissibility_and_behavior_atoms_never_compare() {
        // A permission's claim and an obligation's claim share words, but
        // tolerance and requirement are different modalities: Unknown.
        let permitted = claim("The client may retry.");
        let obliged = claim("The client shall retry.");
        assert_eq!(implies(&permitted, &obliged), Ternary::Unknown);
        assert_eq!(implies(&obliged, &permitted), Ternary::Unknown);
        assert_eq!(contradicts(&permitted, &obliged), Ternary::Unknown);
    }

    #[test]
    fn proposition_is_the_logical_key() {
        // proposition() strips act/force/source but keeps subject and kernel.
        let sk = |input: &str| match claim(input) {
            Formula::Atom { atom: AtomRef::Behavior { behavior } } => behavior,
            other => panic!("expected bare behavior atom, got {other:?}"),
        };
        let obliged = sk("The request shall be logged.");
        let described = sk("The request is logged.");
        assert_ne!(obliged.source, described.source);
        assert_ne!(obliged.act, described.act);
        assert_eq!(obliged.proposition(), described.proposition());
    }
}

// ====================================================================================
// 2. Generic subjects are universal in behavioral sentences
// ====================================================================================

#[test]
fn generic_behavioral_subjects_meet_at_universal() {
    let quantifier = |input: &str| skeleton(&one(input)).unwrap().subject.quantifier;
    // The trio that used to under-detect conflicts now meets.
    assert_eq!(quantifier("A request shall be logged."), Quantifier::Universal);
    assert_eq!(quantifier("Requests are logged."), Quantifier::Universal);
    assert_eq!(quantifier("Each request shall be logged."), Quantifier::Universal);
    // The generic reading covers every behavioral act: deontic, capability,
    // description, permission.
    assert_eq!(quantifier("A client is able to retry."), Quantifier::Universal);
    assert_eq!(quantifier("A client may retry."), Quantifier::Universal);
    // The formula layer's per-item subject digests agree.
    let claim = claim_formula(&one("A request shall be logged.")).unwrap();
    match claim {
        Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
            assert_eq!(behavior.subject.quantifier, Quantifier::Universal);
        }
        other => panic!("expected behavior atom, got {other:?}"),
    }
}

#[test]
fn object_and_role_indefinites_stay_existential() {
    let sk = skeleton(&one("The daemon shall create a session.")).unwrap();
    assert_eq!(sk.atoms[0].objects[0].quantifier, Quantifier::Existential);
    let sk = skeleton(&one("The daemon shall send the alert to an operator.")).unwrap();
    match &sk.atoms[0].roles[0].value {
        so_lang::semantics::RoleValue::Heads { items, .. } => {
            assert_eq!(items[0].quantifier, Quantifier::Existential);
        }
        other => panic!("expected heads, got {other:?}"),
    }
    // Bare objects stay quantifier-less.
    let sk = skeleton(&one("The daemon shall log requests.")).unwrap();
    assert_eq!(sk.atoms[0].objects[0].quantifier, Quantifier::None);
}

// ====================================================================================
// 4. subject_keys carry modifiers
// ====================================================================================

#[test]
fn subject_keys_carry_modifiers() {
    // `The backup daemon` no longer collides with `The daemon`.
    assert_eq!(subject_keys(&one("The backup daemon shall run.")), vec!["backup.daemon"]);
    assert_eq!(subject_keys(&one("The daemon shall run.")), vec!["daemon"]);
    // Modifiers in surface order, then head, lowercased.
    assert_eq!(
        subject_keys(&one("The primary backup Daemon shall run.")),
        vec!["primary.backup.daemon"]
    );
    // Of-chain links keep their modifiers too (legislated).
    assert_eq!(
        subject_keys(&one("The owner of the file shall approve the change.")),
        vec!["owner.file"]
    );
    assert_eq!(
        subject_keys(&one("The owner of the backup file shall approve the change.")),
        vec!["owner.backup.file"]
    );
    // One key per coordinated item, unchanged.
    assert_eq!(
        subject_keys(&one("The backup pump and the valve shall stop.")),
        vec!["backup.pump", "valve"]
    );
    // Relatives are still dropped: the key stays a coarse textual identity.
    assert_eq!(
        subject_keys(&one("The daemon that is active shall run.")),
        vec!["daemon"]
    );
}

// ====================================================================================
// 5. Legislated for / with / by
// ====================================================================================

#[test]
fn for_requires_a_quantity_measure() {
    // The accepted-but-wrong tree (`listen for requests` as a Duration over
    // a noun phrase) is now a rejection with rewrites.
    assert_eq!(
        parse("The daemon shall listen for requests."),
        Err(ParseError::ForRequiresMeasure)
    );
    assert_eq!(
        parse("The daemon shall wait for the grace period."),
        Err(ParseError::ForRequiresMeasure)
    );
    // In frame clauses too (verbal bodies carry the same roles).
    assert_eq!(
        parse("While the pump runs for the shift, the valve shall stay open."),
        Err(ParseError::ForRequiresMeasure)
    );
    assert_eq!(ParseError::ForRequiresMeasure.kind(), "for_requires_measure");
    // Quantities still parse — numerals and number words, with units.
    let s = one("The daemon shall retain the log for 30 days.");
    match &s.core {
        Core::Deontic { vp, .. } => assert_eq!(
            vp.single().unwrap().roles,
            vec![RolePp::Duration(Measure::Quantity {
                number: "30".into(),
                unit: Some("days".into())
            })]
        ),
        other => panic!("expected deontic, got {other:?}"),
    }
    let s = one("The pump shall run for five seconds.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Duration(Measure::Quantity { .. })));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    // `within` (Deadline) still admits a noun-phrase measure — legislation
    // covers `for` alone.
    let s = one("The daemon shall respond within the grace period.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Deadline(Measure::Np { .. })));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
}

#[test]
fn with_is_rejected_where_a_role_could_start() {
    // Previously swallowed into the object noun phrase; now a rejection.
    assert_eq!(
        parse("The daemon shall notify the user with the report."),
        Err(ParseError::WithIsAmbiguous)
    );
    assert_eq!(
        parse("The daemon shall sign with the key."),
        Err(ParseError::WithIsAmbiguous)
    );
    // Frame clauses (verbal bodies) reject it too.
    assert_eq!(
        parse("When the daemon signs with the key, the log shall grow."),
        Err(ParseError::WithIsAmbiguous)
    );
    assert_eq!(ParseError::WithIsAmbiguous.kind(), "with_is_ambiguous");
    // The rewrites stay accepted.
    let s = one("The daemon shall sign the report using the key.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert!(matches!(&vp.single().unwrap().roles[0], RolePp::Means { marker: MeansMarker::Using, .. }));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    // Round 6 (supersedes the round-5 leave-alone): the reserve now
    // applies inside PLAIN noun phrases too — `The file with the flag`
    // pinned head `flag`, accepted-but-wrong, so bare `with` is rejected
    // in every NP-collection context.
    assert_eq!(
        parse("The file with the flag shall be archived."),
        Err(ParseError::WithIsAmbiguous)
    );
}

#[test]
fn by_is_the_passive_agent_in_be_verb_phrases() {
    let s = one("The request shall be logged by the daemon.");
    match &s.core {
        Core::Deontic { vp, .. } => {
            assert_eq!(vp.single().unwrap().verb, "be");
            assert!(matches!(
                vp.single().unwrap().complement,
                Some(Predicate::Words { ref words }) if words == &["logged"]
            ));
            assert!(matches!(
                &vp.single().unwrap().roles[0],
                RolePp::Agent(np) if np.heads() == vec!["daemon"]
            ));
        }
        other => panic!("expected deontic, got {other:?}"),
    }
    // Render round-trips through the canonical form.
    assert_eq!(s.render(), "the request shall be logged by the daemon.");
    render_round_trips(&s);
    // The agent digests under RoleKind::Agent.
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.atoms[0].words, vec!["logged"]);
    assert_eq!(sk.atoms[0].roles.len(), 1);
    assert_eq!(sk.atoms[0].roles[0].kind, so_lang::semantics::RoleKind::Agent);
}

#[test]
fn by_is_the_passive_agent_in_descriptions_and_copular_clauses() {
    // Description: predicate stays, agent recorded.
    let s = one("The request is logged by the daemon.");
    match &s.core {
        Core::Description { predicate, agent, .. } => {
            assert!(matches!(predicate, Predicate::Words { words } if words == &["logged"]));
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["daemon"]);
        }
        other => panic!("expected description, got {other:?}"),
    }
    assert_eq!(s.render(), "the request is logged by the daemon.");
    render_round_trips(&s);
    // One atom across the deontic passive and the described passive.
    let described = skeleton(&s).unwrap();
    let obliged = skeleton(&one("The request shall be logged by the daemon.")).unwrap();
    assert_eq!(described.atoms[0], obliged.atoms[0]);
    // Copular guard clauses record their agent too.
    let s = one("When the request is submitted by the user, the daemon shall log the request.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    match &clause.body {
        ClauseBody::Copular { agent, .. } => {
            assert_eq!(agent.as_ref().unwrap().heads(), vec!["user"]);
        }
        other => panic!("expected copular body, got {other:?}"),
    }
    render_round_trips(&s);
    // The guard digest carries the agent as a role.
    let sk = skeleton(&s).unwrap();
    let trigger = sk.guards.trigger.as_ref().unwrap();
    assert_eq!(trigger.clauses[0].roles[0].kind, so_lang::semantics::RoleKind::Agent);
}

#[test]
fn by_outside_a_passive_site_is_rejected() {
    assert_eq!(
        parse("The daemon shall notify the user by email."),
        Err(ParseError::ByOutsidePassive)
    );
    assert_eq!(
        parse("The daemon shall respond by Friday."),
        Err(ParseError::ByOutsidePassive)
    );
    // Verbal clause bodies are active voice: no agent there.
    assert_eq!(
        parse("When the daemon runs by the dock, the valve shall open."),
        Err(ParseError::ByOutsidePassive)
    );
    assert_eq!(ParseError::ByOutsidePassive.kind(), "by_outside_passive");
}

#[test]
fn passive_agents_relate_across_acts() {
    use so_lang::relate::{implies, Ternary};
    let described = claim_formula(&one("The request is logged by the daemon.")).unwrap();
    let obliged = claim_formula(&one("The request shall be logged by the daemon.")).unwrap();
    assert_eq!(implies(&described, &obliged), Ternary::Yes);
    // A different agent is a different proposition.
    let other = claim_formula(&one("The request is logged by the gateway.")).unwrap();
    assert_eq!(implies(&described, &other), Ternary::Unknown);
}

// ====================================================================================
// 6. Relative attachment: who → chain root, that → nearest head
// ====================================================================================

#[test]
fn who_attaches_to_the_chain_root_and_that_to_the_nearest_head() {
    // `who` restricts the USER (chain root) …
    let s = one("The user of the workspace who is active shall confirm the change.");
    let np = match &s.core {
        Core::Deontic { subject: NpGroup::Single(np), .. } => np,
        other => panic!("expected single deontic subject, got {other:?}"),
    };
    assert_eq!(np.head, "user");
    let relative = np.relative.as_ref().expect("who attaches to the root");
    assert_eq!(relative.marker, RelMarker::Who);
    let of = np.of.as_ref().unwrap();
    assert_eq!(of.head, "workspace");
    assert!(of.relative.is_none(), "the inner link carries no relative");
    // … while `that` restricts the WORKSPACE (nearest head, unchanged).
    let s = one("The user of the workspace that is active shall confirm the change.");
    let np = match &s.core {
        Core::Deontic { subject: NpGroup::Single(np), .. } => np,
        other => panic!("expected single deontic subject, got {other:?}"),
    };
    assert!(np.relative.is_none(), "that never climbs to the root");
    let of = np.of.as_ref().unwrap();
    assert_eq!(of.head, "workspace");
    assert_eq!(of.relative.as_ref().unwrap().marker, RelMarker::That);
    // Deeper chains: `who` climbs to the outermost head.
    let s = one("The owner of the log of the daemon who is active shall rotate the log.");
    let np = match &s.core {
        Core::Deontic { subject: NpGroup::Single(np), .. } => np,
        other => panic!("expected single deontic subject, got {other:?}"),
    };
    assert_eq!(np.head, "owner");
    assert_eq!(np.relative.as_ref().unwrap().marker, RelMarker::Who);
    assert!(np.of.as_ref().unwrap().relative.is_none());
    assert!(np.of.as_ref().unwrap().of.as_ref().unwrap().relative.is_none());
}

#[test]
fn who_and_that_attachments_render_round_trip() {
    for input in [
        "The user of the workspace who is active shall confirm the change.",
        "The user of the workspace that is active shall confirm the change.",
        "The user who is active shall confirm the change.",
        // Both markers in one chain: `that` inner, `who` outer.
        "The user of the workspace that is shared who is active shall confirm the change.",
    ] {
        render_round_trips(&one(input));
    }
}

#[test]
fn subject_keys_ignore_relatives_in_both_attachments() {
    assert_eq!(
        subject_keys(&one("The user of the workspace who is active shall confirm the change.")),
        vec!["user.workspace"]
    );
    assert_eq!(
        subject_keys(&one("The user of the workspace that is active shall confirm the change.")),
        vec!["user.workspace"]
    );
}

// ====================================================================================
// 7. `is always/never able to` is capability
// ====================================================================================

#[test]
fn adverbed_able_to_is_capability_with_composed_polarity() {
    use so_lang::semantics::{denote, Claim, Denotation, Polarity};
    let capability = |input: &str| match denote(&one(input)) {
        Denotation::Behavior(assertion) => match assertion.claim {
            Claim::Capability { polarity, vp } => (polarity, vp),
            other => panic!("expected capability, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    };
    // `always`: capability kept, affirmative.
    let s = one("The client is always able to retry.");
    match &s.core {
        Core::Description {
            adverb: Some(DescriptionAdverb::Always),
            predicate: Predicate::AbleTo { vp },
            ..
        } => assert_eq!(vp.verb, "retry"),
        other => panic!("expected always + AbleTo, got {other:?}"),
    }
    render_round_trips(&s);
    assert_eq!(capability("The client is always able to retry.").0, Polarity::Affirmative);
    // `never`: negative capability.
    let s = one("The client is never able to retry.");
    render_round_trips(&s);
    let (polarity, vp) = capability("The client is never able to retry.");
    assert_eq!(polarity, Polarity::Negative);
    assert_eq!(vp.verb, "retry");
    // XOR with subject `no` through the shared helper: two flips cancel.
    assert_eq!(capability("No client is able to retry.").0, Polarity::Negative);
    assert_eq!(capability("No client is never able to retry.").0, Polarity::Affirmative);
    // Plain capability unchanged.
    assert_eq!(capability("The client is able to retry.").0, Polarity::Affirmative);
    // The skeleton polarity mirrors the composed claim polarity.
    let sk = skeleton(&one("The client is never able to retry.")).unwrap();
    assert_eq!(sk.polarity, so_lang::semantics::Polarity::Negative);
    assert_eq!(sk.atoms[0].words, vec!["retry"]);
}

#[test]
fn never_able_to_contradicts_the_positive_capability() {
    use so_lang::relate::{contradicts, Ternary};
    let can = claim_formula(&one("The client is able to retry.")).unwrap();
    let cannot = claim_formula(&one("The client is never able to retry.")).unwrap();
    assert_eq!(contradicts(&can, &cannot), Ternary::Yes);
}

#[test]
fn no_subject_normalization_is_unchanged() {
    // The skeleton INDEX keeps `no` as written; the formula layer still
    // normalizes it to Universal with the negation on the Not wrapper.
    let sk = skeleton(&one("No request is logged.")).unwrap();
    assert_eq!(sk.subject.quantifier, Quantifier::Negative);
    match claim_formula(&one("No request is logged.")).unwrap() {
        Formula::Not { inner } => match *inner {
            Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
                assert_eq!(behavior.subject.quantifier, Quantifier::Universal);
            }
            other => panic!("expected behavior atom, got {other:?}"),
        },
        other => panic!("expected negated atom, got {other:?}"),
    }
}
