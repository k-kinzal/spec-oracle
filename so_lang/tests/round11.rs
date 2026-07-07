//! Round 11: the fail-closed verb boundary, verbal-object guard digests,
//! explicit-relied contract forming, well-formedness/verification data,
//! envelope-calculus refutations, and active/passive normalization
//! candidates.

use so_lang::ast::ClauseBody;
use so_lang::formula::{
    contract_formula, AssumptionSource, ContractFormula, EdgeKind, Formula,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{assumption_satisfiable, refines, Ternary};
use so_lang::semantics::{skeleton, Quantifier};

fn one(input: &str) -> so_lang::ast::Sentence {
    parse(input).unwrap().sentences.remove(0)
}

/// An explicitly-relied source over the whole source conditional — the
/// graph-edge entry point with the identity reliance.
fn explicit_source(
    kind: EdgeKind,
    source: &so_lang::ast::Sentence,
    target: &so_lang::ast::Sentence,
) -> AssumptionSource {
    let default = AssumptionSource::for_guarantee(kind, source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(kind, source, target, default.formula.clone())
        .unwrap()
}

/// A paired contract whose formed assumption is REFUTED: two explicit,
/// proven, disjoint-key reliances with provably disjoint intervals.
fn refuted_contract() -> ContractFormula {
    let target = one("The daemon shall flush the buffer.");
    let lo = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at most 3."),
        &target,
    );
    let hi = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at least 5."),
        &target,
    );
    contract_formula(&target).unwrap().paired(&[lo, hi])
}

// ---- change 1: fail closed on the residual verb-boundary ambiguity -----------

/// The ambiguous class rejects: a boundary-less trailing run of two or
/// more bare words after the minimal subject admits both the SVO and the
/// final-word readings, and accepted-but-wrong is worse than rejection.
#[test]
fn ambiguous_class_rejects() {
    for text in [
        // The round-10 flagship (det-led, run of two after the minimal
        // subject).
        "When the client sends telemetry, the daemon shall persist the Node.",
        // The round-10 scramble shape (det-led, run of four).
        "When the backup daemon sends telemetry, the fan shall run.",
        // The round-3 o03 shape (modifier-heavy subject).
        "When the temperature sensor fails, the pump shall stop.",
        // Bare-subject run of three.
        "When clients send telemetry, the fan shall run.",
        // Every clause site: While, exception, clausal role, definiens.
        "While the client sends telemetry, the fan shall run.",
        "The pump shall stop, unless the client sends telemetry.",
        "The pump shall stop after the client sends telemetry.",
        "An upload means that the client sends telemetry.",
    ] {
        assert_eq!(parse(text), Err(ParseError::AmbiguousVerbBoundary), "{text}");
    }
    assert_eq!(ParseError::AmbiguousVerbBoundary.kind(), "ambiguous_verb_boundary");
}

/// The class is decided by SHAPE (legislated): a run in the class rejects
/// even when one of the two readings would not parse — fail closed, never
/// half-open.
#[test]
fn class_membership_is_shape_decided() {
    // `both` (a reserved group marker) in the would-be object made the
    // round-10 SVO split unparseable, and the superseded fallback silently
    // retried the final-word reading; round 11 rejects the shape outright.
    assert!(parse("When the client sends both, the fan shall run.").is_err());
}

/// The rewrites parse, each with a provable verb position.
#[test]
fn rewrites_are_boundaried() {
    // A determiner on the object.
    let s = one("When the client sends the telemetry, the fan shall run.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["client"]);
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "sends"));
    // An of-chain for a long subject.
    let s = one("When the sensor of the temperature fails, the pump shall stop.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "fails"));
    // A role boundary.
    let s = one("When the temperature sensor fails at the depot, the pump shall stop.");
    let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["sensor"]);
    assert!(matches!(&clause.body, ClauseBody::Verbal { verb, .. } if verb == "fails"));
}

/// Shapes outside the class keep their readings: 1-word runs, 2-word
/// det-led runs (the readings coincide), particle and bare-number finals,
/// reserved-word runs (SVO not admitted), and structured subjects.
#[test]
fn unchanged_shapes_still_parse() {
    for (text, verb) in [
        // Length-1 run after the minimal subject.
        ("When a session expires, the system shall close the session.", "expires"),
        // Det-led two-word run: verb-only and verb+none coincide.
        ("When the pump runs, the fan shall run.", "runs"),
        // Final particle.
        ("When the user logs out, the session shall end.", "logs"),
        // Final bare number.
        ("When the counter reaches zero, the system shall reset.", "reaches"),
        // Particle word never opens a run: SVO not admitted, final-word
        // stands.
        ("When the power up fails, the fan shall run.", "fails"),
        // A reserved word opens the run: SVO not admitted (`of` is never a
        // verb), final-word stands.
        ("When the owner of files logs, the fan shall run.", "logs"),
        // Structured (np-first) subject with a verbal tail.
        ("When the owner of the file sends telemetry, the fan shall run.", "sends"),
    ] {
        let s = one(text);
        let clause = &s.frames.trigger.as_ref().unwrap().clause.items[0];
        assert!(
            matches!(&clause.body, ClauseBody::Verbal { verb: v, .. } if v == verb),
            "{text}"
        );
    }
}

// ---- change 2: guard skeletons carry verbal objects ---------------------------

/// The motivating pair: `holds no message` and `holds the message` no
/// longer share a skeleton — the INDEX distinguishes what the anchors
/// always did.
#[test]
fn verbal_guard_digests_carry_objects() {
    let no = skeleton(&one("When the queue holds no message, the daemon shall idle.")).unwrap();
    let the = skeleton(&one("When the queue holds the message, the daemon shall idle.")).unwrap();
    assert_ne!(no.guards, the.guards);
    let clause = &no.guards.trigger.as_ref().unwrap().clauses[0];
    assert_eq!(clause.words, vec!["holds"]);
    assert_eq!(clause.objects.len(), 1);
    assert_eq!(clause.objects[0].quantifier, Quantifier::Negative);
    assert_eq!(clause.objects[0].head, "message");
    // Copular bodies stay object-free.
    let cop = skeleton(&one("While the pump is active, the fan shall run.")).unwrap();
    assert!(cop.guards.states[0].objects.is_empty());
}

/// Serde: `objects` rides on the wire when present, is skipped when empty,
/// and a pre-round-11 digest without the field loads as empty.
#[test]
fn clause_skeleton_objects_serde() {
    let k = skeleton(&one("When the queue holds the message, the daemon shall idle.")).unwrap();
    let clause = &k.guards.trigger.as_ref().unwrap().clauses[0];
    let json = serde_json::to_value(clause).unwrap();
    assert!(json.get("objects").is_some());
    let back: so_lang::semantics::ClauseSkeleton = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(&back, clause);
    // Legacy: no `objects` field loads as empty — the documented
    // pre-round-11 reading (the old digest dropped the object).
    let mut legacy = json;
    legacy.as_object_mut().unwrap().remove("objects");
    let back: so_lang::semantics::ClauseSkeleton = serde_json::from_value(legacy).unwrap();
    assert!(back.objects.is_empty());
    // Empty objects are skipped on the wire.
    let cop = skeleton(&one("While the pump is active, the fan shall run.")).unwrap();
    let json = serde_json::to_value(&cop.guards.states[0]).unwrap();
    assert!(json.get("objects").is_none());
}

// ---- change 3: contract forming requires an explicit relied formula ----------

/// `explicit_relied` is true only through the graph-edge entry point, and
/// contract forming requires it: a default-relied source is a permanent
/// candidate (migration/evidence only) and leaves A at Top.
#[test]
fn contract_forming_requires_explicit_relied() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert!(!default.explicit_relied);
    assert!(default.proven, "the default reliance is self-entailment — proven, yet");
    assert!(!default.contract_forming(), "… still a candidate: not explicit");
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&default));
    assert_eq!(paired.assumption, Formula::Top);
    assert_eq!(paired.sources.len(), 1, "retained as visible evidence");
    // from_sentence (bulk re-derivation) is a default too.
    let bulk =
        AssumptionSource::from_sentence(EdgeKind::OccurrenceReliance, &source).unwrap();
    assert!(!bulk.explicit_relied);
    assert!(!bulk.contract_forming());
    // The explicit entry point flips the gate.
    let explicit = explicit_source(EdgeKind::OccurrenceReliance, &source, &target);
    assert!(explicit.explicit_relied);
    assert!(explicit.contract_forming());
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&explicit));
    assert_eq!(paired.assumption, explicit.relied);
}

/// Serde: `explicit_relied` rides on the wire; a pre-round-11 source
/// without the field loads as `false` — the conservative direction (an old
/// edge becomes a candidate, never silently keeps the power to relieve a
/// guarantee).
#[test]
fn explicit_relied_serde_default_is_conservative() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let explicit = explicit_source(EdgeKind::OccurrenceReliance, &source, &target);
    let json = serde_json::to_value(&explicit).unwrap();
    assert_eq!(json["explicit_relied"], serde_json::json!(true));
    let back: AssumptionSource = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(back, explicit);
    let mut legacy = json;
    legacy.as_object_mut().unwrap().remove("explicit_relied");
    let back: AssumptionSource = serde_json::from_value(legacy).unwrap();
    assert!(!back.explicit_relied, "old JSON loads as a candidate");
    assert!(!back.contract_forming());
}

/// `well_formed()` summarizes the well-formed proven pairing as data: the
/// booleans quantify over non-envelope sources, the ternaries re-expose
/// the refutation-only judgments.
#[test]
fn well_formed_summarizes_the_pairing() {
    let target = one("The daemon shall flush the buffer.");
    // No sources: vacuously explicit and proven, nothing refuted.
    let bare = contract_formula(&target).unwrap();
    let w = bare.well_formed();
    assert!(w.all_contract_forming_explicit);
    assert!(w.all_proven);
    assert_eq!(w.assumption_satisfiability, Ternary::Unknown);
    assert_eq!(w.envelope_compatibility, Ternary::Unknown);
    // A default-relied candidate makes the pairing non-explicit.
    let default = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The scheduler is ready."),
        &target,
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&default)).well_formed();
    assert!(!w.all_contract_forming_explicit);
    assert!(w.all_proven, "the default reliance is still proven");
    // An envelope source does not count against the booleans.
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&envelope)).well_formed();
    assert!(w.all_contract_forming_explicit);
    assert!(w.all_proven);
    // A refuted pairing reports it.
    let w = refuted_contract().well_formed();
    assert!(w.all_contract_forming_explicit);
    assert!(w.all_proven);
    assert_eq!(w.assumption_satisfiability, Ternary::No);
}

// ---- change 4: verification status guards refines ----------------------------

/// A paired contract whose formed assumption is refuted is VACUOUS:
/// refines over it returns Unknown in both positions instead of reporting
/// a proven relation through a tautological saturated form.
#[test]
fn refines_is_unknown_over_a_refuted_assumption() {
    let refuted = refuted_contract();
    assert_eq!(assumption_satisfiable(&refuted), Ternary::No);
    let other = contract_formula(&one("The daemon shall flush the buffer.")).unwrap();
    // Without the guard, the refuted side's saturated form G ∨ ¬⊥-ish
    // would imply (and be implied) vacuously; the guard answers Unknown.
    assert_eq!(refines(&refuted, &other), Ternary::Unknown);
    assert_eq!(refines(&other, &refuted), Ternary::Unknown);
    // Even self-refinement is not certified over a vacuous contract.
    assert_eq!(refines(&refuted, &refuted), Ternary::Unknown);
}

/// The healthy path is unchanged: satisfiable (not refuted) assumptions
/// keep every round-5..10 refinement verdict.
#[test]
fn refines_healthy_path_unchanged() {
    let tight = contract_formula(&one(
        "When the order ships, the daemon shall respond within 5 seconds.",
    ))
    .unwrap();
    let loose = contract_formula(&one(
        "When the order ships, the daemon shall respond within 10 seconds.",
    ))
    .unwrap();
    assert_eq!(refines(&tight, &loose), Ternary::Yes);
    assert_eq!(refines(&loose, &tight), Ternary::Unknown);
    let stop = contract_formula(&one("The pump shall stop.")).unwrap();
    let dont = contract_formula(&one("The pump shall not stop.")).unwrap();
    assert_eq!(refines(&dont, &stop), Ternary::No);
}

// ---- change 5: envelope calculus — more refutations ---------------------------

use so_lang::relate::envelope_compatible;

/// (a) An OBLIGATION whose atom matches the admitted behavior is
/// compatible evidence — obligation implies admissibility — but the
/// judgment stays Unknown: it refutes only, never certifies.
#[test]
fn matching_obligation_never_refutes_and_never_certifies() {
    let target = one("The client shall retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

/// (b) The branch rule, route-around side: a prohibition of ONE branch of
/// an `either … or …` envelope leaves the permission exercisable through
/// the other branch — Unknown, never No.
#[test]
fn single_branch_conflict_routes_around() {
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may either retry or escalate the request."),
        &target,
    )
    .unwrap();
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::Unknown);
}

/// (b) The branch rule, all-branch side: when the guarantee forbids EVERY
/// branch's atom, the permission is entirely revoked — No. The forbidding
/// conjunction is hand-assembled (one sentence cannot prohibit two
/// different behaviors), which is exactly the shape a graph-layer derived
/// guarantee can take.
#[test]
fn all_branch_refutation_is_no() {
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may either retry or escalate the request."),
        &target,
    )
    .unwrap();
    let mut paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&envelope));
    // Conjoin the two prohibitions into one guarantee: ¬retry ∧ ¬escalate.
    let no_escalate = so_lang::formula::claim_formula(
        &one("The client shall not escalate the request."),
    )
    .unwrap();
    paired.guarantee = Formula::And { items: vec![paired.guarantee.clone(), no_escalate] };
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

/// The single-atom refutation is unchanged, and (c) a never-description
/// bounds exactly as a prohibition does.
#[test]
fn single_atom_and_never_description_refutations() {
    // Prohibition vs its own admitted atom (the round-8 rule, unchanged).
    let prohibition = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &prohibition,
    )
    .unwrap();
    let paired =
        contract_formula(&prohibition).unwrap().paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::No);
    // (c) The never-description: `is never logged` forbids what `may be
    // logged` admits — the claim shapes meet at one negated atom.
    let never = one("The client is never logged.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may be logged."),
        &never,
    )
    .unwrap();
    let paired = contract_formula(&never).unwrap().paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

// ---- change 6: active/passive candidate alignment (proposal-only) -------------

use so_lang::semantics::{normalization_candidates, NormalizationKind};

/// The motivating passive: `logged by the daemon` emits active-voice
/// candidates with subject `daemon` and the LEGISLATED stem list —
/// round 12 (change 5) order: the undoubled strip `log` leads, then the
/// round-11 strips `logg`, `logge`, then the participle itself — the
/// patient as object, and none of it claimed correct.
#[test]
fn passive_deontic_emits_active_candidates() {
    let s = one("Each request shall be logged by the daemon.");
    let candidates = normalization_candidates(&s);
    assert_eq!(candidates.len(), 4);
    let verbs: Vec<&str> =
        candidates.iter().map(|c| c.atom.words[0].as_str()).collect();
    assert_eq!(verbs, vec!["log", "logg", "logge", "logged"], "the exact legislated stripping");
    for c in &candidates {
        assert_eq!(c.kind, NormalizationKind::ActivePassive);
        assert_eq!(c.subject.head, "daemon");
        assert_eq!(c.atom.objects.len(), 1);
        assert_eq!(c.atom.objects[0].head, "request");
        assert!(c.atom.roles.is_empty(), "the Agent role does not survive into the candidate");
        assert!(!c.note.is_empty());
    }
}

/// A described passive derives the same way, keeps its non-Agent role
/// tail, and an irregular participle (`sent`) leads with its map stem
/// (round 12, change 5 — supersedes the round-11 "participle alone" pin:
/// `sent` is in the irregular map now).
#[test]
fn passive_description_candidates_and_no_strip_participle() {
    let s = one("The report is submitted by the backup daemon.");
    let candidates = normalization_candidates(&s);
    // `submitted`: undoubled strip, ed-strip, d-strip, participle.
    assert_eq!(
        candidates.iter().map(|c| c.atom.words[0].as_str()).collect::<Vec<_>>(),
        vec!["submit", "submitt", "submitte", "submitted"]
    );
    assert_eq!(candidates[0].subject.head, "daemon");
    assert_eq!(candidates[0].subject.restrictor, vec!["backup".to_string()]);
    // `sent`: the irregular-map hit `send`, then the participle itself.
    let s = one("The report shall be sent by the daemon within 5 seconds.");
    let candidates = normalization_candidates(&s);
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].atom.words, vec!["send"]);
    assert_eq!(candidates[1].atom.words, vec!["sent"]);
    // The non-Agent role tail survives into the candidate.
    assert_eq!(candidates[0].atom.roles.len(), 1);
    assert_eq!(candidates[0].atom.roles[0].kind, so_lang::semantics::RoleKind::Deadline);
}

/// A coordinated agent emits one candidate set per agent item, in surface
/// order (round 12: two stems per item — `send`, `sent`).
#[test]
fn coordinated_agent_candidates() {
    let s = one("The report shall be sent by the auditor and the owner.");
    let candidates = normalization_candidates(&s);
    assert_eq!(candidates.len(), 4);
    assert_eq!(candidates[0].subject.head, "auditor");
    assert_eq!(candidates[1].subject.head, "auditor");
    assert_eq!(candidates[2].subject.head, "owner");
    assert_eq!(candidates[3].subject.head, "owner");
}

/// Out-of-scope shapes emit nothing: active sentences, agentless
/// passives, definitions, capabilities, comparisons, and multi-word
/// predicates.
#[test]
fn non_passive_shapes_emit_nothing() {
    for text in [
        "The daemon shall persist the Node.",
        "Each request shall be logged.",
        "The report is submitted.",
        "A session means a sequence of requests.",
        "The client is able to retry.",
        "The retry count is at most 3.",
        "The record is fully archived by the daemon.",
    ] {
        assert!(
            normalization_candidates(&one(text)).is_empty(),
            "{text} must emit no candidates"
        );
    }
}
