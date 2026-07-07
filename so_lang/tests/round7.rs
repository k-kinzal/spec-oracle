//! Round 7: guard-aware relations, relied formulas on pairing edges,
//! count-quantifier entailment, content complements, role-bearing
//! relatives, envelope compatibility, and role-measure exclusion.
//!
//! 1. Guard-aware relations: conditional contradictions through the guard.
//! 2. Pairing edges carry the relied formula.
//! 3. Count-quantifier entailment (`at least 5` refines `at least 3`).
//! 4. Content complements: `<verb> that <clause>`.
//! 5. Role-bearing relatives.
//! 6. Envelope compatibility (`may` vs `shall not`).
//! 7. Role-measure exclusion (disjoint durations contradict).

use so_lang::ast::Sentence;
use so_lang::formula::{
    claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula, PairingError,
};
use so_lang::parse::parse;
use so_lang::relate::{assess, contradicts, implies, refines, Outcome, Ternary};

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("parse {input:?}: {e}"));
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

fn guarantee(input: &str) -> so_lang::formula::Formula {
    contract_formula(&one(input)).expect("contract-bearing sentence").guarantee
}

// =====================================================================================
// Change 1 — guard-aware relations
// =====================================================================================

/// THE MOTIVATING PAIR: the same When-guarded obligation and prohibition
/// contradict — a conditional contradiction, in force whenever the shared
/// guard holds. Before round 7 the guarantees (`¬guard ∨ claim`) hid the
/// conflict inside the `Or` and the pair was Unknown.
#[test]
fn equal_guards_with_contradicting_claims_are_a_hard_contradiction() {
    let a = one("When the order ships, the system shall issue the receipt.");
    let b = one("When the order ships, the system shall not issue the receipt.");
    assert_eq!(assess(&a, &b), Outcome::HardContradiction);
    assert_eq!(assess(&b, &a), Outcome::HardContradiction);
}

/// Framed vs unframed: a Top-guarded prohibition contradicts a When-guarded
/// obligation — Top is the everywhere-guard, so the When-guard's own region
/// is the overlap.
#[test]
fn top_guard_witnesses_the_other_guards_region() {
    let unframed = one("The system shall not issue the receipt.");
    let framed = one("When the order ships, the system shall issue the receipt.");
    assert_eq!(assess(&unframed, &framed), Outcome::HardContradiction);
    assert_eq!(assess(&framed, &unframed), Outcome::HardContradiction);
    // A While guard against Top works the same way.
    let stateful = one("While the store is open, the system shall issue the receipt.");
    assert_eq!(assess(&unframed, &stateful), Outcome::HardContradiction);
}

/// Differing guards never witness an overlap: two different When-guards
/// with contradicting claims stay Unknown — never Yes (the overlap's
/// satisfiability is not provable syntactically).
#[test]
fn differing_guards_stay_unknown() {
    let a = one("When the order ships, the system shall issue the receipt.");
    let b = one("When the payment clears, the system shall not issue the receipt.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
    assert_eq!(assess(&b, &a), Outcome::Unknown);
    // A one-way guard implication (an extra `and` conjunct) is containment,
    // not an overlap witness: still Unknown, legislated.
    let both = one(
        "When the order ships and the store is open, the system shall issue the receipt.",
    );
    let loose = one("When the order ships, the system shall not issue the receipt.");
    assert_eq!(assess(&both, &loose), Outcome::Unknown);
}

/// Guards equal and claims imply: the guarantees imply (through the shared
/// `¬guard` disjunct), pinned at the formula layer.
#[test]
fn equal_guards_with_implying_claims_imply() {
    let tight = guarantee("When the order ships, the system shall issue the receipt within 5 seconds.");
    let loose = guarantee("When the order ships, the system shall issue the receipt within 10 seconds.");
    assert_eq!(implies(&tight, &loose), Ternary::Yes);
    assert_eq!(implies(&loose, &tight), Ternary::Unknown);
}

/// Guard-equal refinement via deadline containment: the tighter deadline
/// refines the looser one under the same guard, end to end.
#[test]
fn guard_equal_refinement_via_deadline_containment() {
    let tight = one("When the order ships, the system shall issue the receipt within 5 seconds.");
    let loose = one("When the order ships, the system shall issue the receipt within 10 seconds.");
    assert_eq!(
        refines(
            &contract_formula(&tight).unwrap(),
            &contract_formula(&loose).unwrap()
        ),
        Ternary::Yes
    );
    assert_eq!(assess(&tight, &loose), Outcome::Refinement { concrete_is_a: true });
    assert_eq!(assess(&loose, &tight), Outcome::Refinement { concrete_is_a: false });
}

/// The guard-aware rule respects force: a recommended side names the
/// conditional conflict advisory tension, a described side a descriptive
/// conflict.
#[test]
fn conditional_conflicts_keep_force_classification() {
    let should = one("When the order ships, the system should issue the receipt.");
    let shall_not = one("When the order ships, the system shall not issue the receipt.");
    assert_eq!(assess(&should, &shall_not), Outcome::AdvisoryTension);
    let described = one("When the order ships, the receipt is issued.");
    let forbidden = one("When the order ships, the receipt shall not be issued.");
    assert_eq!(assess(&described, &forbidden), Outcome::DescriptiveConflict);
}

/// The claim-level pieces are exposed: claim formulas of the guarded pair
/// contradict even though the assembled guarantees do not (structurally).
#[test]
fn claim_formulas_carry_the_conditional_conflict() {
    let a = one("When the order ships, the system shall issue the receipt.");
    let b = one("When the order ships, the system shall not issue the receipt.");
    let ca = claim_formula(&a).unwrap();
    let cb = claim_formula(&b).unwrap();
    assert_eq!(contradicts(&ca, &cb), Ternary::Yes);
    // The assembled guarantees alone still cannot see it — the rule lives
    // in the decomposition, not in a rewrite of `contradicts`.
    let ga = contract_formula(&a).unwrap().guarantee;
    let gb = contract_formula(&b).unwrap().guarantee;
    assert_eq!(contradicts(&ga, &gb), Ternary::Unknown);
}

// =====================================================================================
// Change 2 — pairing edges carry the relied formula
// =====================================================================================

/// The default reliance is the source formula, in both constructors —
/// SUPERSEDED CONSEQUENCE (round 11, change 3): a default reliance is no
/// longer an explicit selection, so the source is a PERMANENT CANDIDATE
/// and pairing leaves A at Top (the round-6/7 shape required the explicit
/// entry point now).
#[test]
fn relied_defaults_to_the_source_formula() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    let s =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert_eq!(s.relied, s.formula);
    assert!(!s.explicit_relied, "default reliance is not an explicit selection");
    assert!(!s.contract_forming(), "round 11: candidate only");
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&s));
    assert_eq!(paired.assumption, Formula::Top, "a candidate never forms A");
    assert_eq!(paired.sources.len(), 1, "retained as visible evidence");
    // The explicit selection of the SAME formula restores the round-6
    // assumption shape exactly.
    let explicit = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        s.formula.clone(),
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&explicit));
    assert_eq!(paired.assumption, explicit.formula);
}

/// An explicit reliance the source provably entails is accepted, and A is
/// built from the RELIED formula, not the source formula.
#[test]
fn explicit_relied_shapes_the_paired_assumption() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event within 5 seconds.");
    let relied = contract_formula(&one("The gateway shall deliver the event within 10 seconds."))
        .unwrap()
        .guarantee;
    let s = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::GuaranteeDischarge,
        &source,
        &target,
        relied.clone(),
    )
    .unwrap();
    assert_eq!(s.relied, relied);
    assert_ne!(s.relied, s.formula, "the reliance narrows the evidence");
    let paired = contract_formula(&target).unwrap().paired(&[s]);
    assert_eq!(paired.assumption, relied, "A is built from the reliances");
}

/// An Unknown entailment is accepted (conservative, documented); a proven
/// non-entailment is rejected as SourceDoesNotSupportRelied.
#[test]
fn relied_validation_accepts_unknown_and_rejects_no() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event.");
    // Unrelated reliance: implies is Unknown — allowed.
    let unrelated = contract_formula(&one("The gateway shall open the channel."))
        .unwrap()
        .guarantee;
    assert!(AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        unrelated,
    )
    .is_ok());
    // The negation of what the source claims: implies is No — rejected.
    let negated = contract_formula(&one("The gateway shall not deliver the event."))
        .unwrap()
        .guarantee;
    let err = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        negated,
    )
    .unwrap_err();
    assert_eq!(err, PairingError::SourceDoesNotSupportRelied);
    assert_eq!(err.kind(), "source_does_not_support_relied");
    // The act × kind and subject rules still gate first.
    assert_eq!(
        AssumptionSource::for_guarantee_with_relied(
            EdgeKind::GuaranteeDischarge,
            &one("The gateway may deliver the event."),
            &target,
            Formula::Top,
        )
        .unwrap_err(),
        PairingError::PermissionOnlyEnvelope
    );
}

/// Multiple reliances conjoin into A; envelope sources stay out of A
/// (round 6 doctrine unchanged), relied or not.
#[test]
fn paired_assumption_conjoins_relied_formulas() {
    let target = one("The daemon shall process the event.");
    // Round 11 (change 3): the reliances are selected explicitly.
    let explicit = |kind, text: &str| {
        let source = one(text);
        let default = AssumptionSource::for_guarantee(kind, &source, &target).unwrap();
        AssumptionSource::for_guarantee_with_relied(kind, &source, &target, default.formula)
            .unwrap()
    };
    let a = explicit(EdgeKind::OccurrenceReliance, "The gateway shall deliver the event.");
    let b = explicit(EdgeKind::GuaranteeDischarge, "The scheduler shall start the worker.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(&[
        a.clone(),
        b.clone(),
        envelope,
    ]);
    assert_eq!(
        paired.assumption,
        Formula::And { items: vec![a.relied.clone(), b.relied.clone()] }
    );
    assert_eq!(paired.sources.len(), 3, "envelope retained as compatibility data");
}

/// Serde: `relied` round-trips, and pre-round-7 JSON without the field
/// deserializes with `relied` defaulted to the source formula.
#[test]
fn relied_serde_round_trip_and_back_compat() {
    let target = one("The daemon shall process the event.");
    let source = one("The gateway shall deliver the event within 5 seconds.");
    let relied = contract_formula(&one("The gateway shall deliver the event within 10 seconds."))
        .unwrap()
        .guarantee;
    let s = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::GuaranteeDischarge,
        &source,
        &target,
        relied,
    );
    let s = s.unwrap();
    let json = serde_json::to_value(&s).unwrap();
    assert!(json.get("relied").is_some());
    let back: AssumptionSource = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(back, s);
    // Pre-round-7 JSON: drop the field — relied defaults to formula.
    let mut old = json;
    old.as_object_mut().unwrap().remove("relied");
    let back: AssumptionSource = serde_json::from_value(old).unwrap();
    assert_eq!(back.relied, back.formula);
}

// =====================================================================================
// Change 3 — count-quantifier entailment
// =====================================================================================

fn claim(input: &str) -> so_lang::formula::Formula {
    claim_formula(&one(input)).expect("behavioral sentence")
}

/// THE REPLICA PAIR: `at least 5` refines `at least 3` — subject-position
/// count quantifiers judged as intervals.
#[test]
fn at_least_five_refines_at_least_three() {
    let five = one("At least 5 replicas shall run.");
    let three = one("At least 3 replicas shall run.");
    assert_eq!(implies(&claim("At least 5 replicas shall run."), &claim("At least 3 replicas shall run.")), Ternary::Yes);
    assert_eq!(implies(&claim("At least 3 replicas shall run."), &claim("At least 5 replicas shall run.")), Ternary::Unknown);
    assert_eq!(assess(&five, &three), Outcome::Refinement { concrete_is_a: true });
}

/// `exactly n` bridges both directions: it implies the containing `at
/// least` and `at most` bounds.
#[test]
fn exactly_bridges_at_least_and_at_most() {
    assert_eq!(
        implies(&claim("Exactly 4 replicas shall run."), &claim("At least 3 replicas shall run.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&claim("Exactly 4 replicas shall run."), &claim("At most 7 replicas shall run.")),
        Ternary::Yes
    );
    assert_eq!(
        implies(&claim("At least 3 replicas shall run."), &claim("Exactly 4 replicas shall run.")),
        Ternary::Unknown
    );
}

/// Disjoint count intervals EXCLUDE: `at least 5` vs `at most 3` is a
/// contradiction; touching closed bounds stay compatible.
#[test]
fn disjoint_counts_contradict() {
    assert_eq!(
        contradicts(&claim("At least 5 replicas shall run."), &claim("At most 3 replicas shall run.")),
        Ternary::Yes
    );
    assert_eq!(
        assess(&one("At least 5 replicas shall run."), &one("At most 3 replicas shall run.")),
        Outcome::HardContradiction
    );
    // `at most 3` and `at least 3` meet at 3: not disjoint.
    assert_eq!(
        contradicts(&claim("At most 3 replicas shall run."), &claim("At least 3 replicas shall run.")),
        Ternary::Unknown
    );
}

/// Object-position counts ground too, when the subjects fully match.
#[test]
fn object_position_counts_entail_and_exclude() {
    assert_eq!(
        implies(
            &claim("The daemon shall keep at least 5 replicas."),
            &claim("The daemon shall keep at least 3 replicas."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &claim("The daemon shall keep at least 5 replicas."),
            &claim("The daemon shall keep at most 3 replicas."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &claim("The daemon shall keep at least 5 replicas."),
            &claim("The daemon shall keep at least 3 snapshots."),
        ),
        Ternary::Unknown
    );
}

// =====================================================================================
// Change 4 — content complements: <verb> that <clause>
// =====================================================================================

/// THE MOTIVATING SENTENCE: `shall ensure that <clause>` parses, renders
/// canonically, and round-trips.
#[test]
fn content_complement_parses_and_round_trips() {
    for input in [
        "The server shall ensure that the token is valid.",
        "The system shall verify within 5 seconds that the token is valid.",
        "The auditor shall verify that the daemon retains the log for 30 days.",
        "The monitor shall ensure that no request is dropped.",
        "The server shall either ensure that the token is valid or reject the request.",
    ] {
        let s = one(input);
        let rendered = s.render();
        let re = one(&rendered);
        assert_eq!(re.render(), rendered, "canonical form re-parses: {input}");
    }
}

/// The verb phrase carries the clause: shape of ensure/verify content, and
/// roles must PRECEDE the content (content is final).
#[test]
fn content_shapes_and_role_order() {
    let s = one("The system shall verify within 5 seconds that the token is valid.");
    let so_lang::ast::Core::Deontic { vp, .. } = &s.core else { panic!("deontic") };
    let vp = vp.single().unwrap();
    assert_eq!(vp.verb, "verify");
    assert_eq!(vp.roles.len(), 1, "the deadline role precedes the content");
    let content = vp.content.as_ref().expect("content clause");
    assert_eq!(content.subject.heads(), vec!["token"]);
    // The skeleton digests the content with its full identity.
    let sk = so_lang::semantics::skeleton(&s).unwrap();
    let content = sk.atoms[0].content.as_ref().expect("content digest");
    assert_eq!(content.clause.subject_head, "token");
    assert_eq!(content.full, "the token is valid");
}

/// LEGISLATED (round 7, pinned both ways): after a NOUN, `that` is that
/// noun's restrictive relative — `record the fact that the token is
/// valid` keeps the relative reading (which has no clause body there, so
/// the sentence is rejected, not silently re-read as content); a relative
/// that IS well-formed after a head still parses as a relative; content-
/// `that` triggers only where a relative cannot attach (directly after
/// the verb, or after a measure role).
#[test]
fn relative_that_wins_after_a_noun() {
    // The relative reading claims the `that` and rejects the determiner at
    // its verb position — never a content complement of `record`.
    // (Superseded pin, recorded: before the round-7 attack fix the relative
    // accepted verb `the` and failed later, on `is`, as UnexpectedTokens;
    // the DeterminerAsVerb gate now fires at the true fault site — a
    // determiner can only open a noun phrase, never a behavior.)
    assert!(matches!(
        parse("The daemon shall record the fact that the token is valid."),
        Err(so_lang::parse::ParseError::DeterminerAsVerb { .. })
    ));
    // A well-formed relative after a head stays a relative.
    let s = one("The daemon shall record the fact that carries the flag.");
    let so_lang::ast::Core::Deontic { vp, .. } = &s.core else { panic!("deontic") };
    let vp = vp.single().unwrap();
    assert!(vp.content.is_none(), "the noun claimed the `that`");
    let object = vp.object.as_ref().unwrap();
    match object {
        so_lang::ast::NpGroup::Single(np) => assert!(np.relative.is_some()),
        other => panic!("expected single object, got {other:?}"),
    }
}

/// SUPERSEDED LEGISLATION (round 9, recorded — twice superseded): round 7
/// kept clause bodies (frames) content-free and this test pinned the
/// motivating guard as a rejection. Round 9 revised the legislation on
/// new grounds — assumptions depend on observed/asserted content, so
/// dependency statements belong in guards — and the verbal CLAUSE body
/// now carries the same final content slot a verb phrase does. The pin
/// flips: the guard parses, with the `that`-clause as the guard verb's
/// content (see tests/round9.rs for the full shape pins). RELATIVE bodies
/// remain content-free in v0.2.
#[test]
fn content_is_unavailable_in_frames() {
    let spec =
        parse("When the monitor ensures that the token is valid, the pump shall stop.").unwrap();
    let sentence = &spec.sentences[0];
    let trigger = sentence.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        so_lang::ast::ClauseBody::Verbal { verb, content, .. } => {
            assert_eq!(verb, "ensures");
            assert!(content.is_some(), "the guard's `that`-clause is content now");
        }
        other => panic!("expected verbal guard body with content, got {other:?}"),
    }
}

/// Content is identity (the lossiness rule): the clause digest drops a
/// verbal body's object, but the full identity string keeps the two
/// contents apart — Unknown, never Yes; equal contents still meet.
#[test]
fn content_identity_is_full_fidelity() {
    let limit = claim("The monitor shall ensure that the reading exceeds the limit.");
    let threshold = claim("The monitor shall ensure that the reading exceeds the threshold.");
    assert_eq!(implies(&limit, &threshold), Ternary::Unknown);
    assert_eq!(implies(&threshold, &limit), Ternary::Unknown);
    assert_eq!(contradicts(&limit, &threshold), Ternary::Unknown);
    // Same content: one claim.
    assert_eq!(
        assess(
            &one("The monitor shall ensure that the reading exceeds the limit."),
            &one("The monitor must ensure that the reading exceeds the limit."),
        ),
        Outcome::Equivalent
    );
    // Content-bearing vs content-free atoms never meet.
    assert_eq!(
        implies(&limit, &claim("The monitor shall ensure the reading.")),
        Ternary::Unknown
    );
    // A prohibition over the SAME content contradicts through the guard-
    // aware claim comparison.
    assert_eq!(
        assess(
            &one("The monitor shall ensure that the reading exceeds the limit."),
            &one("The monitor shall not ensure that the reading exceeds the limit."),
        ),
        Outcome::HardContradiction
    );
}

/// The content digest serializes and round-trips on the skeleton.
#[test]
fn content_serde_round_trip() {
    let sk = so_lang::semantics::skeleton(&one(
        "The server shall ensure that the token is valid.",
    ))
    .unwrap();
    let json = serde_json::to_value(&sk).unwrap();
    let back: so_lang::semantics::Skeleton = serde_json::from_value(json).unwrap();
    assert_eq!(back, sk);
    // Pre-round-7 atoms without `content` still deserialize.
    let mut atom = serde_json::to_value(&sk.atoms[0]).unwrap();
    atom.as_object_mut().unwrap().remove("content");
    let back: so_lang::semantics::Atom = serde_json::from_value(atom).unwrap();
    assert_eq!(back.content, None);
}

// =====================================================================================
// Change 5 — role-bearing relatives
// =====================================================================================

/// THE MOTIVATING SENTENCE: `Each request that arrives from the gateway
/// shall be logged.` parses, with the Source role on the relative's verb.
#[test]
fn role_bearing_relative_parses() {
    let s = one("Each request that arrives from the gateway shall be logged.");
    let so_lang::ast::Core::Deontic { subject, .. } = &s.core else { panic!("deontic") };
    let so_lang::ast::NpGroup::Single(np) = subject else { panic!("single subject") };
    assert_eq!(np.head, "request");
    match &np.relative.as_ref().expect("relative").body {
        so_lang::ast::RelativeBody::Verbal { verb, roles, object, .. } => {
            assert_eq!(verb, "arrives");
            assert!(object.is_none());
            assert!(matches!(&roles[0], so_lang::ast::RolePp::Source(_)));
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
}

/// Relatives carry particles, manner, and locations; canonical renders
/// round-trip.
#[test]
fn relative_tails_round_trip() {
    for input in [
        "Each request that arrives from the gateway shall be logged.",
        "The daemon shall close each session that times out.",
        "Each job that completes successfully shall be archived.",
        "The daemon shall close the session that holds the lock in the vault.",
        "Each user who logs out shall be notified via email.",
        "Each packet that arrives on the public interface shall be inspected.",
    ] {
        let s = one(input);
        let rendered = s.render();
        let re = one(&rendered);
        assert_eq!(re.render(), rendered, "canonical form re-parses: {input}");
    }
}

/// The relative's roles participate in the NP full identity (lossiness):
/// two subjects differing only in the relative's role are Unknown — never
/// Yes; identical relatives still meet.
#[test]
fn relative_roles_are_subject_identity() {
    let gateway = claim("Each request that arrives from the gateway shall be logged.");
    let proxy = claim("Each request that arrives from the proxy shall be logged.");
    assert_eq!(implies(&gateway, &proxy), Ternary::Unknown);
    assert_eq!(contradicts(&gateway, &proxy), Ternary::Unknown);
    assert_eq!(
        assess(
            &one("Each request that arrives from the gateway shall be logged."),
            &one("Each request that arrives from the gateway must be logged."),
        ),
        Outcome::Equivalent
    );
    // The full identity string carries the whole tail.
    let sk = so_lang::semantics::skeleton(&one(
        "Each request that arrives from the gateway shall be logged.",
    ))
    .unwrap();
    assert_eq!(sk.subject.full, "request that arrives from the gateway");
}

/// Depth interaction: relatives nest through the shared depth budget and
/// deep chains still land on PhraseTooDeep, not a stack overflow.
#[test]
fn relative_depth_stays_bounded() {
    // A relative whose role nests a clause with its own relative parses.
    let s = one("The daemon shall log each request that arrives after the user who is active logs out.");
    assert!(parse(&s.render()).is_ok());
    // An adversarially deep of-chain in a relative's role NP is an error.
    let deep = format!(
        "Each request that arrives from the owner {} shall be logged.",
        "of the owner ".repeat(70)
    );
    assert!(matches!(
        parse(&deep),
        Err(so_lang::parse::ParseError::PhraseTooDeep { .. })
    ));
}

// =====================================================================================
// Change 6 — envelope compatibility
// =====================================================================================

/// THE MOTIVATING PAIR: `may retry` vs `shall not retry` is an envelope
/// conflict — the prohibition forbids what the permission admits.
#[test]
fn permission_against_prohibition_is_an_envelope_conflict() {
    let may = one("The client may retry.");
    let shall_not = one("The client shall not retry.");
    assert_eq!(assess(&may, &shall_not), Outcome::EnvelopeConflict);
    assert_eq!(assess(&shall_not, &may), Outcome::EnvelopeConflict);
    // A negative description bounds the same way.
    let never = one("The client is never able to retry.");
    assert_eq!(assess(&may, &never), Outcome::EnvelopeConflict);
    // Different behaviors do not conflict.
    assert_eq!(
        assess(&may, &one("The client shall not reconnect.")),
        Outcome::Unknown
    );
}

/// Guard interaction (change 1 rules): equal guards conflict, a Top guard
/// witnesses the other's region, differing guards stay Unknown.
#[test]
fn envelope_conflict_respects_guards() {
    let framed_may = one("When the queue drains, the client may retry.");
    let framed_not = one("When the queue drains, the client shall not retry.");
    assert_eq!(assess(&framed_may, &framed_not), Outcome::EnvelopeConflict);
    // Top-guarded prohibition against a framed permission: still a conflict.
    assert_eq!(
        assess(&framed_may, &one("The client shall not retry.")),
        Outcome::EnvelopeConflict
    );
    // Differing guards: no overlap witness.
    assert_eq!(
        assess(&framed_may, &one("When the link fails, the client shall not retry.")),
        Outcome::Unknown
    );
}

/// Permission × obligation over one atom: LEGISLATED Unknown (round 7) —
/// an obligation implies admissibility, so nothing conflicts, but a
/// positive compatibility certification is graph work, not a language
/// fact. Recommendations do not bound: `should not` is no envelope
/// conflict either.
#[test]
fn permission_against_obligation_and_recommendation_stay_unknown() {
    let may = one("The client may retry.");
    assert_eq!(assess(&may, &one("The client shall retry.")), Outcome::Unknown);
    assert_eq!(assess(&one("The client shall retry."), &may), Outcome::Unknown);
    assert_eq!(assess(&may, &one("The client should not retry.")), Outcome::Unknown);
    // Permission × permission stays out entirely.
    assert_eq!(assess(&may, &one("The client may retry.")), Outcome::Unknown);
}

/// The new outcome keeps a stable wire name.
#[test]
fn envelope_conflict_wire_name() {
    let json = serde_json::to_value(Outcome::EnvelopeConflict).unwrap();
    assert_eq!(json["kind"], "envelope_conflict");
    let back: Outcome = serde_json::from_value(json).unwrap();
    assert_eq!(back, Outcome::EnvelopeConflict);
}

// =====================================================================================
// Change 7 — role-measure exclusion
// =====================================================================================

/// THE SUPERSEDED CONSERVATISM: disjoint Duration intervals now contradict
/// (`for at least 30 days` vs `for less than 10 days`), end to end.
#[test]
fn disjoint_durations_contradict() {
    let a = claim("The daemon shall retain the log for at least 30 days.");
    let b = claim("The daemon shall retain the log for less than 10 days.");
    assert_eq!(contradicts(&a, &b), Ternary::Yes);
    assert_eq!(contradicts(&b, &a), Ternary::Yes);
    assert_eq!(
        assess(
            &one("The daemon shall retain the log for at least 30 days."),
            &one("The daemon shall retain the log for less than 10 days."),
        ),
        Outcome::HardContradiction
    );
    // Identical intervals under two spellings (`for at least 10` and the
    // plain `for 10` both denote [10, ∞)): not disjoint, so no exclusion —
    // and no syntactic equality either, so the honest answer is Unknown,
    // never a false Yes.
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for at least 10 days."),
            &claim("The daemon shall retain the log for 10 days."),
        ),
        Ternary::Unknown
    );
}

/// Deadline exclusion grounds through the same interval reading. The
/// grammar admits bounded measures under `for` only, so the disjoint
/// deadline pair is hand-built: a plain `within 10 seconds` — `(-∞, 10]` —
/// against a lower-bounded deadline `[30, ∞)`.
#[test]
fn disjoint_deadlines_contradict() {
    use so_lang::ast::ComparisonOp;
    use so_lang::formula::{AtomRef, Formula};
    use so_lang::semantics::{RoleValue};
    let plain = claim("The daemon shall respond within 10 seconds.");
    let Formula::Atom { atom: AtomRef::Behavior { behavior } } = &plain else {
        panic!("expected one behavior atom");
    };
    let mut bounded = behavior.clone();
    bounded.atom.roles[0].value = RoleValue::BoundedMeasure {
        op: ComparisonOp::AtLeast,
        number: "30".into(),
        unit: Some("seconds".into()),
        upper: None,
    };
    let bounded = Formula::Atom { atom: AtomRef::Behavior { behavior: bounded } };
    assert_eq!(contradicts(&plain, &bounded), Ternary::Yes);
    // Two plain deadlines are both upper bounds: never disjoint —
    // containment (refinement), not exclusion.
    assert_eq!(
        contradicts(
            &claim("The daemon shall respond within 5 seconds."),
            &claim("The daemon shall respond within 10 seconds."),
        ),
        Ternary::Unknown
    );
}

/// Mixed kinds (a Deadline against a Duration) and unit mismatches never
/// ground: Unknown, exactly as for containment.
#[test]
fn mixed_kind_and_mixed_unit_role_measures_stay_unknown() {
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log within 10 days."),
            &claim("The daemon shall retain the log for at least 30 days."),
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for at least 30 days."),
            &claim("The daemon shall retain the log for less than 10 hours."),
        ),
        Ternary::Unknown
    );
    // A second differing field (the object) blocks the rule.
    assert_eq!(
        contradicts(
            &claim("The daemon shall retain the log for at least 30 days."),
            &claim("The daemon shall retain the index for less than 10 days."),
        ),
        Ternary::Unknown
    );
}

// =====================================================================================
// Change 8 — documented readings, parse-verified
// =====================================================================================

/// Temporal-clause attachment is fixed and deterministic, and the docs
/// name the reading: a role AFTER the temporal clause is the INNER
/// reading (it belongs to the nested clause); the outer reading is
/// written with the role BEFORE the temporal clause.
#[test]
fn temporal_clause_inner_attachment_is_pinned() {
    use so_lang::ast::{Core, RolePp};
    // Inner: `using email` sits on the After-clause's verb.
    let inner = one("The system shall notify the user after the backup completes using email.");
    let Core::Deontic { vp, .. } = &inner.core else { panic!("deontic") };
    let vp = vp.single().unwrap();
    let RolePp::After(clause) = &vp.roles[0] else { panic!("expected After role") };
    match &clause.body {
        so_lang::ast::ClauseBody::Verbal { verb, roles, .. } => {
            assert_eq!(verb, "completes");
            assert!(matches!(&roles[0], RolePp::Means { .. }), "inner reading: the backup completes using email");
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    // Outer: `using email` sits on `notify`, before the After clause.
    let outer = one("The system shall notify the user using email after the backup completes.");
    let Core::Deontic { vp, .. } = &outer.core else { panic!("deontic") };
    let vp = vp.single().unwrap();
    assert!(matches!(&vp.roles[0], RolePp::Means { .. }), "outer reading: notify using email");
    assert!(matches!(&vp.roles[1], RolePp::After(_)));
}

/// Every example the round-7 docs introduce parses (parse-verified docs).
#[test]
fn round7_doc_examples_parse() {
    for input in [
        "While the session holds the lock, the daemon shall close the session in the vault.",
        "The daemon shall record the fact that carries the flag.",
        "The monitor shall ensure that no request is dropped.",
        "Each request that arrives from the gateway shall be logged.",
        "The daemon shall close each session that times out.",
        "Each job that completes successfully shall be archived.",
    ] {
        assert!(parse(input).is_ok(), "doc example must parse: {input}");
    }
}

/// Mixed quantifier kinds never ground: Universal, Definite, and
/// Existential against Count stay Unknown — never Yes, never No.
#[test]
fn mixed_quantifier_kinds_stay_unknown() {
    assert_eq!(
        implies(&claim("Each replica shall run."), &claim("At least 3 replicas shall run.")),
        Ternary::Unknown
    );
    assert_eq!(
        implies(&claim("At least 3 replicas shall run."), &claim("Each replica shall run.")),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(&claim("The replicas shall run."), &claim("At most 3 replicas shall run.")),
        Ternary::Unknown
    );
}
