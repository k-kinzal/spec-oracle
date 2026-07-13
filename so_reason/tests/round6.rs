//! Round 6 — behaviors introduced by the sixth improvement round, pinned.
//!
//! 1. Lossiness-aware propositions: no false Yes when only the coarse
//!    digests match.
//! 2. Target-aware pairing (`AssumptionSource::for_guarantee`).
//! 3. Envelope sources stay out of the paired assumption formula.
//! 4. Force-aware relation outcomes (`relate::assess`).
//! 5. Structured comparisons and interval reasoning.
//! 6. VP alternatives: `either <vp> or <vp>`.
//! 7. Plain-NP `with` is rejected.
//! 8. Bounded durations (`for at least 30 days`).

use so_lang::ast::Sentence;
use so_lang::parse::parse;
use so_reason::formula::{
    claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula, PairingError,
    SubjectRelation,
};
use so_reason::relate::{assess, contradicts, implies, Outcome, Ternary};

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn claim(input: &str) -> Formula {
    claim_formula(&one(input)).expect("behavioral sentence has a claim formula")
}

fn guarantee(input: &str) -> Formula {
    contract_formula(&one(input))
        .expect("contract-bearing sentence")
        .guarantee
}

// ---- change 1: lossiness-aware propositions -----------------------------------------

/// The motivating pair: relatives differ, coarse digests collide. The old
/// proposition identity dropped the relative, producing a false
/// contradiction; round 6 carries the full renders, so the honest answer is
/// Unknown — never Yes (the restrictions differ) and never No (their
/// disjointness is not provable syntactically).
#[test]
fn authenticated_vs_unauthenticated_requests_do_not_falsely_contradict() {
    let a = claim("Each request that is authenticated shall be accepted.");
    let b = claim("Each request that is unauthenticated shall not be accepted.");
    assert_eq!(contradicts(&a, &b), Ternary::Unknown);
    assert_eq!(implies(&a, &b), Ternary::Unknown);
    assert_eq!(implies(&b, &a), Ternary::Unknown);
}

/// `of`-chain distinction: same head (`owner`), different chain — Unknown,
/// not a contradiction.
#[test]
fn of_chain_distinguishes_subjects() {
    let file = claim("The owner of the file shall sign.");
    let bucket = claim("The owner of the bucket shall not sign.");
    assert_eq!(contradicts(&file, &bucket), Ternary::Unknown);
    assert_eq!(implies(&file, &bucket), Ternary::Unknown);
}

/// Identical full renders still meet: the sharpening only removes false
/// positives, never true ones.
#[test]
fn identical_full_identity_still_yields_yes() {
    let a = claim("Each request that is authenticated shall be accepted.");
    let b = claim("Each request that is authenticated shall be accepted.");
    assert_eq!(implies(&a, &b), Ternary::Yes);
    let denial = claim("Each request that is authenticated shall not be accepted.");
    assert_eq!(contradicts(&a, &denial), Ternary::Yes);
    // And the guarantee-level judgment agrees.
    assert_eq!(
        contradicts(
            &guarantee("Each request that is authenticated shall be accepted."),
            &guarantee("Each request that is authenticated shall not be accepted."),
        ),
        Ternary::Yes
    );
}

/// Object noun phrases carry full identity too: `the owner of the file` vs
/// `the owner of the bucket` in object position must not meet.
#[test]
fn object_of_chains_do_not_collide() {
    let a = claim("The daemon shall notify the owner of the file.");
    let b = claim("The daemon shall not notify the owner of the bucket.");
    assert_eq!(contradicts(&a, &b), Ternary::Unknown);
    let denial = claim("The daemon shall not notify the owner of the file.");
    assert_eq!(contradicts(&a, &denial), Ternary::Yes);
}

// ---- change 2: target-aware pairing -------------------------------------------------

/// A source about the target's own subject is a self-reliance RED FLAG.
/// SUPERSEDED (round 10, change 6 — the round-6 SameSubject rejection is
/// removed): subject keys are tentative textual identity, so the collision
/// is RECORDED as `SubjectRelation::SharedKeys` and the source rides as a
/// candidate (never contract-forming) instead of failing construction.
#[test]
fn same_subject_pairing_is_recorded_not_rejected() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The daemon is available.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    assert!(!shared.contract_forming());
    // Keys carry modifiers (round 5): `the backup daemon` is a DIFFERENT
    // subject from `the daemon`, so it is disjoint — and forms A once its
    // reliance is selected explicitly (round 11, change 3: the
    // default-relied construction is a permanent candidate).
    let other = one("The backup daemon is available.");
    let ok = AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &other, &target)
        .expect("disjoint subjects pair");
    assert_eq!(ok.subject_relation, SubjectRelation::DisjointKeys);
    assert!(
        !ok.contract_forming(),
        "default reliance: candidate only (round 11)"
    );
    let explicit = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &other,
        &target,
        ok.formula.clone(),
    )
    .unwrap();
    assert!(explicit.contract_forming());
    // A coordinated source sharing ANY key with the target is SharedKeys.
    let coordinated = one("The daemon and the scheduler are available.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &coordinated, &target)
            .unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
}

/// The act × kind matrix of `from_sentence` is intact under `for_guarantee`,
/// and definitions are NotBehavioral on either side.
#[test]
fn for_guarantee_keeps_the_act_kind_matrix() {
    let target = one("The daemon shall flush the buffer.");
    let permission = one("The client may retry.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &permission, &target)
            .unwrap_err(),
        PairingError::PermissionOnlyEnvelope
    );
    AssumptionSource::for_guarantee(EdgeKind::AdmissibilityEnvelope, &permission, &target)
        .expect("permission pairs as an envelope");
    let recommendation = one("The scheduler should rotate the logs.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &recommendation, &target)
            .unwrap_err(),
        PairingError::RecommendationOnlyReliance
    );
    let definition = one("A session means a sequence of requests.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &definition, &target)
            .unwrap_err(),
        PairingError::NotBehavioral
    );
    // A definition TARGET is just as non-behavioral.
    let source = one("The scheduler is ready.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &definition)
            .unwrap_err(),
        PairingError::NotBehavioral
    );
}

/// The advisory reliance check is `relate::implies` over the source formula:
/// conservative, three-valued, advisory only.
#[test]
fn advisory_reliance_check_is_conservative_implication() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let a =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    // The source discharges exactly its own claim…
    assert_eq!(a.advisory_reliance_check(&a.formula), Ternary::Yes);
    // …and an unrelated reliance is honestly Unknown.
    let unrelated = claim("The clock is skewed.");
    assert_eq!(a.advisory_reliance_check(&unrelated), Ternary::Unknown);
}

// ---- change 3: envelope sources leave the saturated assumption ----------------------

/// Mixed pairing: the assumption is derived from the non-envelope sources
/// only; the envelope stays in `sources` as compatibility data and is never
/// negated by saturation.
#[test]
fn envelope_sources_stay_out_of_the_assumption_formula() {
    let target = one("The daemon shall respond.");
    let c = contract_formula(&target).unwrap();
    // Round 11 (change 3): the reliance is selected explicitly so it
    // forms A; a default-relied source would ride as a candidate.
    let clock = one("The clock is monotonic.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &clock, &target).unwrap();
    let reliance = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &clock,
        &target,
        default.formula.clone(),
    )
    .unwrap();
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
        &target,
    )
    .unwrap();
    let paired = c.paired(&[reliance.clone(), envelope.clone()]);
    // Sources retained, both of them.
    assert_eq!(paired.sources, vec![reliance.clone(), envelope.clone()]);
    // Assumption excludes the envelope: it is the reliance formula alone.
    assert_eq!(paired.assumption, reliance.formula);
    // Saturation negates the reliance only — the permission never appears
    // as a negated conjunct (it is no behavior-set complement).
    assert_eq!(
        paired.saturated(),
        Formula::Or {
            items: vec![
                paired.guarantee.clone(),
                Formula::Not {
                    inner: Box::new(reliance.formula.clone())
                },
            ],
        }
    );
}

/// Envelope-only pairing keeps the trivial assumption: nothing is assumed,
/// the guarantee is unconditional, saturation is the guarantee itself.
#[test]
fn envelope_only_pairing_keeps_assumption_top() {
    let target = one("The daemon shall respond.");
    let c = contract_formula(&target).unwrap();
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
        &target,
    )
    .unwrap();
    let paired = c.paired(std::slice::from_ref(&envelope));
    assert_eq!(paired.assumption, Formula::Top);
    assert_eq!(paired.sources, vec![envelope]);
    assert_eq!(paired.saturated(), paired.guarantee);
}

// ---- change 4: force-aware relation outcomes ----------------------------------------

/// A recommendation crossing an obligation is tension, never a hard
/// contradiction — the force-blind `implies` (round-5 caveat) is now
/// complemented by the force-aware `assess`.
#[test]
fn should_vs_shall_conflict_is_advisory_tension() {
    let a = one("The pump should stop.");
    let b = one("The pump shall not stop.");
    assert_eq!(assess(&a, &b), Outcome::AdvisoryTension);
    assert_eq!(assess(&b, &a), Outcome::AdvisoryTension);
}

/// Binding × binding conflict is the hard one.
#[test]
fn binding_conflict_is_hard_contradiction() {
    let a = one("The pump shall stop.");
    let b = one("The pump shall not stop.");
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
    let must = one("The pump must not stop.");
    assert_eq!(assess(&a, &must), Outcome::HardContradiction);
}

/// A description crossing a prohibition is a descriptive conflict: the
/// system as described violates the norm.
#[test]
fn description_vs_prohibition_is_descriptive_conflict() {
    let described = one("The request is logged.");
    let forbidden = one("The request shall not be logged.");
    assert_eq!(assess(&described, &forbidden), Outcome::DescriptiveConflict);
    assert_eq!(assess(&forbidden, &described), Outcome::DescriptiveConflict);
}

/// Equivalence requires SAME force: `shall`/`must` meet, `should`/`shall`
/// do not (legislated Unknown — subsumption of the weaker force is graph
/// policy, not language fact). Complements the round-5 force-blind
/// mutual-implication pin.
#[test]
fn assess_equivalent_only_for_same_force_pairs() {
    let shall = one("The pump shall stop.");
    let must = one("The pump must stop.");
    assert_eq!(assess(&shall, &must), Outcome::Equivalent);
    let should = one("The pump should stop.");
    assert_eq!(assess(&shall, &should), Outcome::Unknown);
    assert_eq!(assess(&should, &shall), Outcome::Unknown);
    // Descriptions carry no force; two mutually implying descriptions are
    // same-force (None) and equivalent (the generic subject reads
    // universal — round 5).
    let is_a = one("A request is logged.");
    let is_b = one("Each request is logged.");
    assert_eq!(assess(&is_a, &is_b), Outcome::Equivalent);
}

/// Refinement reports its direction.
#[test]
fn assess_reports_refinement_direction() {
    let tight = one("The daemon shall flush the buffer within 5 seconds.");
    let loose = one("The daemon shall flush the buffer within 10 seconds.");
    assert_eq!(
        assess(&tight, &loose),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
    assert_eq!(
        assess(&loose, &tight),
        Outcome::Refinement {
            concrete_is_a: false
        }
    );
}

/// Definitions and permissions have no head-to-head assessment: Unknown,
/// documented (permissions participate via pairing).
#[test]
fn definitions_and_permissions_assess_unknown() {
    let definition = one("A session means a sequence of requests.");
    let permission = one("The client may retry.");
    let obligation = one("The client shall retry.");
    assert_eq!(assess(&definition, &obligation), Outcome::Unknown);
    assert_eq!(assess(&permission, &obligation), Outcome::Unknown);
    assert_eq!(assess(&obligation, &permission), Outcome::Unknown);
}

/// Outcome serializes with the crate's serde discipline.
#[test]
fn outcome_serializes() {
    let json = serde_json::to_value(Outcome::Refinement {
        concrete_is_a: true,
    })
    .unwrap();
    assert_eq!(json["kind"], "refinement");
    assert_eq!(json["concrete_is_a"], true);
    let back: Outcome = serde_json::from_value(json).unwrap();
    assert_eq!(
        back,
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
}

// ---- change 5: structured comparisons + interval reasoning --------------------------

/// Disjoint intervals contradict: `at most 3` vs `at least 5` cannot both
/// hold of one measured subject.
#[test]
fn disjoint_intervals_contradict() {
    let a = claim("The retry count is at most 3.");
    let b = claim("The retry count is at least 5.");
    assert_eq!(contradicts(&a, &b), Ternary::Yes);
    // Descriptions carry no force: the assessment names it a descriptive
    // conflict, not a hard contradiction.
    assert_eq!(
        assess(
            &one("The retry count is at most 3."),
            &one("The retry count is at least 5.")
        ),
        Outcome::DescriptiveConflict
    );
    // The binding `be`-complement forms meet at the same intervals — and
    // binding × binding conflict is the hard one.
    assert_eq!(
        assess(
            &one("The retry count shall be at most 3."),
            &one("The retry count shall be at least 5."),
        ),
        Outcome::HardContradiction
    );
}

/// Closed endpoints touch: `at most 3` and `at least 3` are compatible at
/// exactly 3 — NOT a contradiction. Open bounds do exclude the endpoint.
#[test]
fn touching_closed_bounds_do_not_contradict() {
    let at_most = claim("The depth is at most 3.");
    let at_least = claim("The depth is at least 3.");
    assert_eq!(contradicts(&at_most, &at_least), Ternary::Unknown);
    // `less than 3` is open at 3: disjoint from `at least 3`.
    let less = claim("The depth is less than 3.");
    assert_eq!(contradicts(&less, &at_least), Ternary::Yes);
    let greater = claim("The depth is greater than 3.");
    assert_eq!(contradicts(&at_most, &greater), Ternary::Yes);
}

/// Containment refinements across operators: intervals, not operator
/// pairs, decide.
#[test]
fn interval_containment_refines_across_operators() {
    let c = |i: &str| claim(i);
    // A point is contained in its closed bound.
    assert_eq!(
        implies(
            &c("The count is equal to 3."),
            &c("The count is at most 3.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The count is equal to 3."),
            &c("The count is at least 3.")
        ),
        Ternary::Yes
    );
    // between ⊆ at least / between ⊆ between.
    assert_eq!(
        implies(
            &c("The latency is between 4 and 6."),
            &c("The latency is at least 2.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The latency is between 4 and 6."),
            &c("The latency is between 3 and 7.")
        ),
        Ternary::Yes
    );
    // Overlap without containment stays Unknown.
    assert_eq!(
        implies(
            &c("The latency is between 4 and 6."),
            &c("The latency is between 5 and 7.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &c("The latency is between 4 and 6."),
            &c("The latency is between 5 and 7.")
        ),
        Ternary::Unknown
    );
    // Disjoint between intervals do contradict.
    assert_eq!(
        contradicts(
            &c("The latency is between 1 and 2."),
            &c("The latency is between 4 and 6.")
        ),
        Ternary::Yes
    );
}

/// Units gate everything: mismatch (or a written unit vs none) is Unknown,
/// and a `between` with two DIFFERENT written units cannot be grounded.
#[test]
fn interval_reasoning_requires_one_unit() {
    let c = |i: &str| claim(i);
    assert_eq!(
        contradicts(
            &c("The latency is at most 3 seconds."),
            &c("The latency is at least 5 ms."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        implies(
            &c("The count is equal to 3 items."),
            &c("The count is at most 3.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        implies(
            &c("The latency is between 1 seconds and 3 ms."),
            &c("The latency is between 1 and 5 seconds."),
        ),
        Ternary::Unknown
    );
    // Number words ground exactly like numerals.
    assert_eq!(
        contradicts(
            &c("The depth is at most three."),
            &c("The depth is at least five.")
        ),
        Ternary::Yes
    );
}

// ---- change 6: VP alternatives (`either <vp> or <vp>`) ------------------------------

/// The motivating sentence: a genuine alternative obligation, one sentence,
/// one claim, disjunctive formula.
#[test]
fn vp_alternatives_parse_render_and_derive() {
    use so_lang::ast::{Core, VpGroup};
    let s = one("The server shall either accept the request or reject the request.");
    let Core::Deontic {
        vp: VpGroup::Alternatives { items },
        negated: false,
        ..
    } = &s.core
    else {
        panic!("expected alternatives, got {:?}", s.core);
    };
    assert_eq!(items.len(), 2);
    assert_eq!(items[0].verb, "accept");
    assert_eq!(items[1].verb, "reject");
    // Canonical render round-trips.
    assert_eq!(
        s.render(),
        "the server shall either accept the request or reject the request.",
        "closed-class words render lowercase in canonical form"
    );
    let again = one(&s.render());
    assert_eq!(again.core, s.core);
    // The skeleton indexes BOTH alternatives: one atom each.
    let sk = so_reason::semantics::skeleton(&s).unwrap();
    assert_eq!(sk.atoms.len(), 2);
    assert_eq!(sk.atoms[0].words, vec!["accept"]);
    assert_eq!(sk.atoms[1].words, vec!["reject"]);
    // The claim formula is the alternatives' Or, with per-alternative
    // anchors that re-parse as single-vp cores.
    let Formula::Or { items: disjuncts } = claim_formula(&s).unwrap() else {
        panic!("expected Or over alternatives");
    };
    assert_eq!(disjuncts.len(), 2);
    let anchor = |f: &Formula| match f {
        Formula::Atom {
            atom: so_reason::formula::AtomRef::Behavior { behavior },
        } => behavior.source.clone(),
        other => panic!("expected behavior atom, got {other:?}"),
    };
    assert_eq!(anchor(&disjuncts[0]), "the server shall accept the request");
    assert_eq!(anchor(&disjuncts[1]), "the server shall reject the request");
    // Three alternatives work; `be` is a valid item.
    let s = one("The daemon shall either be idle or run the job or stop.");
    let sk = so_reason::semantics::skeleton(&s).unwrap();
    assert_eq!(sk.atoms.len(), 3);
    assert_eq!(sk.atoms[0].words, vec!["idle"]);
}

/// Negated alternatives are rejected at ingest (legislated: write two
/// prohibitions — no De Morgan surprises).
#[test]
fn negated_alternatives_are_rejected() {
    assert_eq!(
        parse("The server shall not either accept the request or reject the request."),
        Err(so_lang::parse::ParseError::NegatedAlternatives)
    );
    assert_eq!(
        so_lang::parse::ParseError::NegatedAlternatives.kind(),
        "negated_alternatives"
    );
    let message = so_lang::parse::ParseError::NegatedAlternatives.to_string();
    assert!(
        message.contains("two prohibitions"),
        "message directs the rewrite: {message}"
    );
}

/// Disambiguation, pinned both ways: after a modal, `either` + verb opens
/// VP alternatives; `either` + determiner stays the NP marker path (and the
/// verb position rejects it, exactly as before round 6). In OBJECT position
/// `either` keeps being the NP group marker.
#[test]
fn either_disambiguation_is_deterministic() {
    use so_lang::ast::{Conj, Core, GroupMarker, NpGroup, VpGroup};
    // Object position: unchanged NP coordination.
    let s = one("The daemon shall notify either the admin or the owner.");
    let Core::Deontic {
        vp: VpGroup::Single(vp),
        ..
    } = &s.core
    else {
        panic!("expected single vp");
    };
    match vp.object.as_ref().unwrap() {
        NpGroup::Coordinated {
            conj: Conj::Or,
            marker: Some(GroupMarker::Either),
            items,
        } => {
            assert_eq!(items.len(), 2);
        }
        other => panic!("expected either-coordination, got {other:?}"),
    }
    // After the modal, `either` + determiner: NP marker path, rejected at
    // verb position — pinned error, not silent misreading.
    assert_eq!(
        parse("The server shall either the admin or the owner."),
        Err(so_lang::parse::ParseError::UnexpectedTokens {
            token: "either".into()
        })
    );
    // `either` with no `or` alternation: the marker convention error.
    assert_eq!(
        parse("The server shall either stop."),
        Err(so_lang::parse::ParseError::MixedCoordination)
    );
    // Backtracking: an `or` inside an item's own either-coordination stays
    // inside the item.
    let s = one(
        "The daemon shall either accept either the copy or the original or reject the request.",
    );
    let Core::Deontic {
        vp: VpGroup::Alternatives { items },
        ..
    } = &s.core
    else {
        panic!("expected alternatives");
    };
    assert_eq!(items.len(), 2);
    assert_eq!(items[0].verb, "accept");
    assert_eq!(items[1].verb, "reject");
}

/// Permissions take alternatives through the same deontic slot; capability
/// (`is able to`) does not — alternatives are deontic-only in v0.2.
#[test]
fn alternatives_are_deontic_only() {
    use so_lang::ast::{Core, VpGroup};
    let s = one("The client may either retry or abort.");
    assert!(matches!(
        &s.core,
        Core::Deontic {
            vp: VpGroup::Alternatives { .. },
            ..
        }
    ));
    // The permission's claim formula is an Or over ADMISSIBILITY atoms.
    let Formula::Or { items } = claim_formula(&s).unwrap() else {
        panic!("expected Or");
    };
    assert!(items.iter().all(|f| matches!(
        f,
        Formula::Atom {
            atom: so_reason::formula::AtomRef::Admissibility { .. }
        }
    )));
    // Capability keeps a single verb phrase: `either` is not a verb there.
    assert!(parse("The client is able to either retry or abort.").is_err());
}

/// A single obligation refines the alternative: doing A discharges
/// `either A or B`.
#[test]
fn single_vp_refines_its_alternative() {
    let single = one("The server shall accept the request.");
    let alternative = one("The server shall either accept the request or reject the request.");
    assert_eq!(
        implies(
            &claim_formula(&single).unwrap(),
            &claim_formula(&alternative).unwrap()
        ),
        Ternary::Yes
    );
    assert_eq!(
        assess(&single, &alternative),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
}

/// Alternatives serialize and round-trip (sentence, skeleton, formula).
#[test]
fn vp_alternatives_serialize() {
    let s = one("The server shall either accept the request or reject the request.");
    let json = serde_json::to_value(&s).unwrap();
    assert_eq!(json["core"]["vp"]["kind"], "alternatives");
    assert_eq!(json["core"]["vp"]["items"][0]["verb"], "accept");
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
    let sk = so_reason::semantics::skeleton(&s).unwrap();
    let json = serde_json::to_value(&sk).unwrap();
    assert_eq!(json["atoms"][1]["words"], serde_json::json!(["reject"]));
    let back: so_reason::semantics::Skeleton = serde_json::from_value(json).unwrap();
    assert_eq!(back, sk);
    // A single vp serializes with its `single` tag and round-trips.
    let s = one("The pump shall stop.");
    let json = serde_json::to_value(&s).unwrap();
    assert_eq!(json["core"]["vp"]["kind"], "single");
    assert_eq!(json["core"]["vp"]["verb"], "stop");
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
}

// ---- change 7: plain-NP `with` is rejected ------------------------------------------

/// Bare `with` inside ANY noun phrase is the same legislated ambiguity as
/// at role positions — no more silent folding into modifiers.
#[test]
fn with_inside_plain_nps_is_rejected() {
    use so_lang::parse::ParseError;
    // Subject position — the round-5 accepted-but-wrong tree (head `flag`).
    assert_eq!(
        parse("The file with the flag shall be archived."),
        Err(ParseError::WithIsAmbiguous)
    );
    // Frame-clause subject.
    assert_eq!(
        parse("When the user with the token logs out, the session shall end."),
        Err(ParseError::WithIsAmbiguous)
    );
    // Predicate Pp noun phrase.
    assert_eq!(
        parse("The pump is below the tank with the valve."),
        Err(ParseError::WithIsAmbiguous)
    );
    // The supported restriction forms stay accepted.
    let s = one("The file that carries the flag shall be archived.");
    assert!(matches!(&s.core, so_lang::ast::Core::Deontic { .. }));
    let s = one("The owner of the flag shall be notified.");
    assert!(matches!(&s.core, so_lang::ast::Core::Deontic { .. }));
    // The backtick escape keeps noun uses of the word itself, and the
    // message teaches it.
    let s = one("The `with` clause shall be documented.");
    assert!(matches!(&s.core, so_lang::ast::Core::Deontic { .. }));
    let message = ParseError::WithIsAmbiguous.to_string();
    assert!(
        message.contains("`with`"),
        "message teaches the backtick escape: {message}"
    );
    assert!(
        message.contains("using"),
        "message keeps the instrument rewrite: {message}"
    );
}

// ---- change 8: bounded durations ----------------------------------------------------

/// `for at least 30 days` parses as a bounded Duration measure, renders
/// canonically, and round-trips.
#[test]
fn bounded_durations_parse_and_render() {
    use so_lang::ast::{ComparisonOp, Core, Measure, RolePp};
    let s = one("The daemon shall retain the log for at least 30 days.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("expected deontic")
    };
    let vp = vp.single().unwrap();
    assert_eq!(
        vp.roles[0],
        RolePp::Duration(Measure::Bounded {
            op: ComparisonOp::AtLeast,
            number: "30".into(),
            unit: Some("days".into()),
            upper: None,
        })
    );
    assert_eq!(
        s.render(),
        "the daemon shall retain the log for at least 30 days."
    );
    assert_eq!(one(&s.render()).core, s.core);
    // `between` shares one unit, written after either bound.
    let s = one("The pump shall run for between 5 and 10 seconds.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("expected deontic")
    };
    assert_eq!(
        vp.single().unwrap().roles[0],
        RolePp::Duration(Measure::Bounded {
            op: ComparisonOp::Between,
            number: "5".into(),
            unit: Some("seconds".into()),
            upper: Some("10".into()),
        })
    );
    assert_eq!(one(&s.render()).core, s.core);
    // Other bounds parse too; the skeleton digests the bound structurally.
    let s = one("The cache shall hold the entry for less than two hours.");
    let sk = so_reason::semantics::skeleton(&s).unwrap();
    assert_eq!(
        sk.atoms[0].roles[0].value,
        so_reason::semantics::RoleValue::BoundedMeasure {
            op: ComparisonOp::LessThan,
            number: "two".into(),
            unit: Some("hours".into()),
            upper: None,
        }
    );
    // Serde round trip.
    let json = serde_json::to_value(&s).unwrap();
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
    // The documented surface forms all parse and render-round-trip.
    for input in [
        "The service shall retain the log for at least 30 days.",
        "The pump shall run for at most 5 seconds.",
        "The daemon shall keep the lease for greater than 3 days.",
        "The cache shall hold the entry for less than 2 hours.",
        "The pump shall run for between 5 and 10 seconds.",
    ] {
        let s = one(input);
        assert_eq!(
            one(&s.render()).core,
            s.core,
            "{input:?} must render-round-trip"
        );
    }
}

/// The rejections that remain: `for` still requires a quantity, bounded or
/// plain — bounded noun phrases and `equal to` are not readings.
#[test]
fn bounded_duration_rejections() {
    use so_lang::parse::ParseError;
    assert_eq!(
        parse("The daemon shall wait for at least the grace period."),
        Err(ParseError::ForRequiresMeasure)
    );
    assert_eq!(
        parse("The daemon shall listen for requests."),
        Err(ParseError::ForRequiresMeasure)
    );
    // `for equal to 5 seconds` has no reading: `for 5 seconds` says it.
    assert_eq!(
        parse("The pump shall run for equal to 5 seconds."),
        Err(ParseError::ForRequiresMeasure)
    );
    // Two written units that disagree: the second is stray material.
    assert!(parse("The pump shall run for between 5 seconds and 10 ms.").is_err());
    // Matching written units are fine.
    let s = one("The pump shall run for between 5 seconds and 10 seconds.");
    assert_eq!(
        s.render(),
        "the pump shall run for between 5 and 10 seconds."
    );
}

/// Interval logic covers Duration bounds, composed with the round-5 plain
/// direction: retaining longer implies retaining shorter.
#[test]
fn bounded_durations_relate_by_interval() {
    let c = |i: &str| claim(i);
    // Bounded vs bounded.
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for at least 30 days."),
            &c("The daemon shall retain the log for at least 10 days."),
        ),
        Ternary::Yes
    );
    // Plain composes with bounded: `for 30 days` reads `[30, ∞)` (round-5
    // direction), so it meets `for at least 10 days`.
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for 30 days."),
            &c("The daemon shall retain the log for at least 10 days."),
        ),
        Ternary::Yes
    );
    // The round-5 plain-plain direction is unchanged.
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for 30 days."),
            &c("The daemon shall retain the log for 10 days."),
        ),
        Ternary::Yes
    );
    // No containment → Unknown; unit mismatch → Unknown.
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for at most 5 days."),
            &c("The daemon shall retain the log for at least 10 days."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for at least 30 days."),
            &c("The daemon shall retain the log for at least 10 weeks."),
        ),
        Ternary::Unknown
    );
    // `between` durations refine by containment.
    assert_eq!(
        implies(
            &c("The pump shall run for between 5 and 10 seconds."),
            &c("The pump shall run for at least 5 seconds."),
        ),
        Ternary::Yes
    );
}

/// Pairing artifacts round-trip, `subject_relation` included (round 10).
#[test]
fn for_guarantee_sources_serialize() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let a =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let json = serde_json::to_value(&a).unwrap();
    let back: AssumptionSource = serde_json::from_value(json).unwrap();
    assert_eq!(back, a);
}
