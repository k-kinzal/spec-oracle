//! Adversarial conformance attack on the round-10 changes: responsible
//! subjects, the force gate on A, guard roles, the SVO bare-object reading,
//! and the SameSubject downgrade to candidate data.
//!
//! Every test that passes is a permanent conformance pin. The two findings
//! this attack raised (multi-word-subject SVO scramble, role-boundary SVO
//! flip) were resolved by the fixer as LEGISLATED trades — no lexicon-free
//! rule can satisfy them without breaking round 10's own pins — and their
//! tests now pin the legislated readings with the documented workarounds
//! (see the `FINDING RESOLVED AS LEGISLATED` comments).

use so_lang::ast::TriggerKind;
use so_lang::formula::{
    applicability, contract_formula, AssumptionSource, AtomRef, EdgeKind, Formula, GuardRole,
    PairingError, SubjectRelation,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{assess, assumption_satisfiable, envelope_compatible, implies, Outcome, Ternary};
use so_lang::semantics::{responsible_subject_keys, subject_keys};

fn one(input: &str) -> so_lang::ast::Sentence {
    parse(input).unwrap().sentences.remove(0)
}

fn guard_clause(sentence: &so_lang::ast::Sentence) -> &so_lang::ast::Clause {
    if let Some(trigger) = &sentence.frames.trigger {
        return &trigger.clause.items[0];
    }
    if let Some(frame) = sentence.frames.states.first() {
        return &frame.clause.items[0];
    }
    sentence.exception.as_ref().expect("a guard or exception clause")
}

fn verbal(clause: &so_lang::ast::Clause) -> (&str, Option<&str>, Option<&so_lang::ast::NpGroup>) {
    match &clause.body {
        so_lang::ast::ClauseBody::Verbal { verb, particle, object, .. } => {
            (verb.as_str(), particle.as_deref(), object.as_ref())
        }
        other => panic!("expected a verbal body, got {other:?}"),
    }
}

// =====================================================================
// change 1 — responsible subjects
// =====================================================================

/// The agent of a deontic passive is found wherever it sits in the role
/// tail, not only in first position.
#[test]
fn responsible_agent_found_after_other_roles() {
    let s = one("Each request shall be logged within 5 seconds by the daemon.");
    assert_eq!(subject_keys(&s), vec!["request"]);
    assert_eq!(responsible_subject_keys(&s), vec!["daemon"]);
}

/// Every deontic force takes the passive-agent derivation: prohibition,
/// permission, recommendation.
#[test]
fn responsible_agent_across_deontic_forces() {
    let s = one("Each request shall not be logged by the daemon.");
    assert_eq!(responsible_subject_keys(&s), vec!["daemon"]);
    let s = one("The request may be rejected by the gateway.");
    assert_eq!(responsible_subject_keys(&s), vec!["gateway"]);
    let s = one("The report should be reviewed by the auditor.");
    assert_eq!(responsible_subject_keys(&s), vec!["auditor"]);
}

/// A coordinated PATIENT keeps its per-item grammatical keys while the
/// responsible view collapses to the one stated agent.
#[test]
fn coordinated_patient_single_agent() {
    let s = one("The report and the log shall be reviewed by the auditor.");
    assert_eq!(subject_keys(&s), vec!["report", "log"]);
    assert_eq!(responsible_subject_keys(&s), vec!["auditor"]);
}

/// A coordinated agent on a described passive yields one key per item.
#[test]
fn description_coordinated_agent() {
    let s = one("The report is submitted by the daemon and the proxy.");
    assert_eq!(subject_keys(&s), vec!["report"]);
    assert_eq!(responsible_subject_keys(&s), vec!["daemon", "proxy"]);
}

/// Agent keys carry the of-chain, exactly as subject keys do (round 5).
#[test]
fn responsible_agent_of_chain_keys() {
    let s = one("Each request shall be logged by the owner of the file.");
    assert_eq!(responsible_subject_keys(&s), vec!["owner.file"]);
}

/// A capability is active: its subject acts, so the subject answers.
#[test]
fn capability_subject_is_responsible() {
    let s = one("The daemon is able to retry.");
    assert_eq!(responsible_subject_keys(&s), vec!["daemon"]);
}

/// An `either … or …` deontic derives from the FIRST alternative's agent
/// (legislated).
#[test]
fn alternatives_first_agent_decides() {
    let s = one("The report shall either be reviewed by the auditor or be archived.");
    assert_eq!(responsible_subject_keys(&s), vec!["auditor"]);
}

// =====================================================================
// change 2 — recommendations never enter A
// =====================================================================

/// A recommended source built with an EXPLICIT relied formula is proven
/// yet still candidate-only: force gates A regardless of construction path.
#[test]
fn recommended_with_explicit_relied_stays_candidate() {
    let target = one("The daemon shall persist the Node.");
    let source = one("The client should send the Node.");
    let relied = contract_formula(&target)
        .map(|_| so_lang::formula::claim_formula(&source).unwrap())
        .unwrap();
    let built = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        relied,
    )
    .unwrap();
    assert!(built.proven, "an unguarded source's claim is self-entailed");
    assert!(!built.contract_forming(), "recommended never forms A");
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&built));
    assert_eq!(paired.assumption, Formula::Top);
    assert_eq!(paired.sources.len(), 1, "candidate retained");
}

/// Round 11 (change 3): pins that exercise contract forming build their
/// sources with an EXPLICIT reliance (the whole source conditional through
/// the graph-edge entry point) — a default reliance is a permanent
/// candidate and never forms A.
fn explicit_source(
    kind: EdgeKind,
    source: &so_lang::ast::Sentence,
    target: &so_lang::ast::Sentence,
) -> AssumptionSource {
    let default = AssumptionSource::for_guarantee(kind, source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(kind, source, target, default.formula.clone())
        .unwrap()
}

/// `must` binds exactly as `shall` does — it forms A (explicit reliance,
/// round 11).
#[test]
fn must_source_forms_a() {
    let target = one("The daemon shall persist the Node.");
    let source = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The client must send the Node."),
        &target,
    );
    assert!(source.contract_forming());
}

/// A capability description is force-free and still forms A (state
/// reliance unchanged; explicit reliance, round 11).
#[test]
fn capability_source_forms_a() {
    let target = one("The daemon shall persist the Node.");
    let source = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The client is able to retry."),
        &target,
    );
    assert!(source.contract_forming());
}

/// A permission is still envelope-only: reliance and discharge reject, and
/// the envelope it does construct never forms A.
#[test]
fn permission_still_envelope_only() {
    let target = one("The daemon shall persist the Node.");
    let permission = one("The client may retry.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &permission, &target),
        Err(PairingError::PermissionOnlyEnvelope)
    );
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &permission, &target),
        Err(PairingError::PermissionOnlyEnvelope)
    );
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &permission,
        &target,
    )
    .unwrap();
    assert!(!envelope.contract_forming());
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&envelope));
    assert_eq!(paired.assumption, Formula::Top);
}

/// A recommendation still cannot discharge and is no envelope (round-5
/// matrix unchanged by the round-10 force gate).
#[test]
fn recommendation_matrix_unchanged() {
    let target = one("The daemon shall persist the Node.");
    let rec = one("The monitor should verify the Node.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &rec, &target),
        Err(PairingError::RecommendationOnlyReliance)
    );
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::AdmissibilityEnvelope, &rec, &target),
        Err(PairingError::RecommendationOnlyReliance)
    );
}

/// `assumption_satisfiable` judges exactly the A that was formed: two
/// contradicting BINDING reliances prove No; downgrading one side to a
/// recommendation removes it from A, and the verdict returns to Unknown —
/// a candidate must not poison the satisfiability of an assumption it
/// never entered.
#[test]
fn satisfiability_judges_exactly_the_formed_a() {
    let target = one("The daemon shall persist the Node.");
    let contract = contract_formula(&target).unwrap();
    // Round 11 (change 3): the binding reliances are selected explicitly.
    let lo = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue is at most 3."),
        &target,
    );
    let hi_binding = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue must be at least 5."),
        &target,
    );
    let hi_recommended = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The queue should be at least 5."),
        &target,
    );
    let both_binding = contract.paired(&[lo.clone(), hi_binding]);
    assert_eq!(assumption_satisfiable(&both_binding), Ternary::No);
    let one_recommended = contract.paired(&[lo.clone(), hi_recommended]);
    assert_eq!(assumption_satisfiable(&one_recommended), Ternary::Unknown);
    assert_eq!(one_recommended.assumption, lo.relied, "only the binding reliance formed A");
    assert_eq!(one_recommended.sources.len(), 2, "the recommended candidate is retained");
}

/// Changes 1 + 2 together: a recommended PASSIVE source's subject relation
/// is computed on its agent, and force keeps it out of A either way.
#[test]
fn recommended_passive_source_keys_and_gate() {
    let target = one("The daemon shall persist the Node.");
    let disjoint = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The Node should be sent by the client."),
        &target,
    )
    .unwrap();
    assert_eq!(disjoint.subject_relation, SubjectRelation::DisjointKeys);
    assert!(!disjoint.contract_forming(), "recommended: never A");
    let shared = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The Node should be sent by the daemon."),
        &target,
    )
    .unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    assert!(!shared.contract_forming());
}

// =====================================================================
// change 4 — guard roles
// =====================================================================

/// Where-vs-While over the same words is Unknown; each family against
/// itself still grounds the contradiction.
#[test]
fn where_vs_while_same_words_unknown() {
    assert_eq!(
        assess(
            &one("Where the mode is active, the pump shall run."),
            &one("While the mode is active, the pump shall not run."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("Where the mode is active, the pump shall run."),
            &one("Where the mode is active, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
}

/// If-vs-When over the same words is Unknown (trigger KIND is part of the
/// role); If-vs-If still grounds.
#[test]
fn if_vs_when_same_words_unknown() {
    assert_eq!(
        assess(
            &one("If the pump runs, then the fan shall not run."),
            &one("When the pump runs, the fan shall run."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("If the pump runs, then the fan shall not run."),
            &one("If the pump runs, then the fan shall run."),
        ),
        Outcome::HardContradiction
    );
}

/// Cross-role guards block implication/equivalence/refinement too, not
/// only contradiction: the same claim under While vs When is Unknown in
/// every direction.
#[test]
fn cross_role_blocks_implication_and_refinement() {
    let a = one("While the pump runs, the fan shall run.");
    let b = one("When the pump runs, the fan shall run.");
    let (ca, cb) = (contract_formula(&a).unwrap(), contract_formula(&b).unwrap());
    assert_eq!(implies(&ca.guarantee, &cb.guarantee), Ternary::Unknown);
    assert_eq!(implies(&cb.guarantee, &ca.guarantee), Ternary::Unknown);
    assert_eq!(assess(&a, &b), Outcome::Unknown);
}

/// The envelope-conflict witness gates on role equality: a While-guarded
/// permission crossed by a When-guarded prohibition of the same behavior
/// is Unknown; the same-role pair still fires.
#[test]
fn envelope_conflict_requires_matching_roles() {
    assert_eq!(
        assess(
            &one("While the pump runs, the client may retry."),
            &one("When the pump runs, the client shall not retry."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("While the pump runs, the client may retry."),
            &one("While the pump runs, the client shall not retry."),
        ),
        Outcome::EnvelopeConflict
    );
}

/// Exception atoms have their own role: two exception-guarded sentences
/// over the same carve-out still ground (same role on both sides), and an
/// exception never masquerades as a trigger.
#[test]
fn exception_role_pairs() {
    assert_eq!(
        assess(
            &one("The fan shall run, unless the pump runs."),
            &one("The fan shall not run, unless the pump runs."),
        ),
        Outcome::HardContradiction
    );
    // `unless the pump runs` vs `when the pump runs` — jointly satisfiable
    // sentences; the exception atom must not meet the trigger atom.
    assert_eq!(
        assess(
            &one("The fan shall run, unless the pump runs."),
            &one("When the pump runs, the fan shall not run."),
        ),
        Outcome::Unknown
    );
}

/// The role is part of the canonical SORT KEY: swapping the same two
/// clauses between the While and When slots is NOT a reordering of one
/// region — Unknown — while reordering WITHIN one connective still
/// normalizes and grounds.
#[test]
fn canonical_sort_carries_roles() {
    // Same clause set, roles swapped across the frame families.
    assert_eq!(
        assess(
            &one("While the pump runs, when the order ships, the fan shall run."),
            &one("While the order ships, when the pump runs, the fan shall not run."),
        ),
        Outcome::Unknown
    );
    // Identical family assignment still grounds.
    assert_eq!(
        assess(
            &one("While the pump runs, when the order ships, the fan shall run."),
            &one("While the pump runs, when the order ships, the fan shall not run."),
        ),
        Outcome::HardContradiction
    );
    // Commutative reordering within one While coordination still grounds
    // (round 9 behavior preserved under role-carrying atoms).
    assert_eq!(
        assess(
            &one("While the pump runs and the mode is active, the fan shall run."),
            &one("While the mode is active and the pump runs, the fan shall not run."),
        ),
        Outcome::HardContradiction
    );
}

/// Serde shapes for every role variant, and the legacy (pre-round-10)
/// default: a guard atom without a `role` field loads as State.
#[test]
fn guard_role_serde_variants_and_legacy_default() {
    let shape = |text: &str| {
        let f = applicability(&one(text));
        let json = serde_json::to_value(&f).unwrap();
        let back: Formula = serde_json::from_value(json.clone()).unwrap();
        assert_eq!(back, f, "{text}");
        json
    };
    let scope = shape("Where the mode is active, the pump shall run.");
    assert_eq!(scope["atom"]["role"], serde_json::json!({ "kind": "scope" }));
    let state = shape("While the pump runs, the fan shall run.");
    assert_eq!(state["atom"]["role"], serde_json::json!({ "kind": "state" }));
    let contingency = shape("If the order ships, then the fan shall run.");
    assert_eq!(
        contingency["atom"]["role"],
        serde_json::json!({ "kind": "trigger", "trigger": "contingency" })
    );
    // The exception atom sits under the applicability's Not.
    let exception = shape("The fan shall run, unless the pump runs.");
    assert_eq!(exception["inner"]["atom"]["role"], serde_json::json!({ "kind": "exception" }));
    // Legacy: strip the role from a Scope atom — it loads as State (the
    // documented pre-round-10 reading), NOT as its round-10 family.
    let mut legacy = scope;
    legacy["atom"].as_object_mut().unwrap().remove("role");
    let back: Formula = serde_json::from_value(legacy).unwrap();
    match back {
        Formula::Atom { atom: AtomRef::Guard { role, .. } } => assert_eq!(role, GuardRole::State),
        other => panic!("expected a guard atom, got {other:?}"),
    }
}

/// The If trigger's role carries its kind end-to-end.
#[test]
fn if_guard_role_is_contingency() {
    match applicability(&one("If the order ships, then the fan shall run.")) {
        Formula::Atom { atom: AtomRef::Guard { role, .. } } => {
            assert_eq!(role, GuardRole::Trigger { kind: TriggerKind::Contingency });
        }
        other => panic!("expected a guard atom, got {other:?}"),
    }
}

// =====================================================================
// change 5 — SVO bare-object clauses
// =====================================================================

/// SUPERSEDED (round 11, change 1 — fail-closed): the ambiguous class is
/// rejected in a definiens clause too; the boundaried rewrite parses.
#[test]
fn svo_in_definiens_clause() {
    assert_eq!(
        parse("An upload means that the client sends telemetry."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    let s = one("An upload means that the client sends the telemetry.");
    let so_lang::ast::Core::Definition { definiens, .. } = &s.core else {
        panic!("expected a definition");
    };
    let so_lang::ast::Definiens::Clause(clause) = definiens else {
        panic!("expected a clause definiens, got {definiens:?}");
    };
    let (verb, particle, object) = verbal(clause);
    assert_eq!((verb, particle), ("sends", None));
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
}

/// A verbal relative reads its bare two-word tail as verb + object.
#[test]
fn svo_shape_in_relative_body() {
    let s = one("Each user who sends telemetry shall authenticate.");
    let so_lang::ast::Core::Deontic { subject, .. } = &s.core else {
        panic!("expected a deontic core");
    };
    let so_lang::ast::NpGroup::Single(np) = subject else {
        panic!("expected a single subject");
    };
    let relative = np.relative.as_ref().expect("a relative clause");
    match &relative.body {
        so_lang::ast::RelativeBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "sends");
            assert_eq!(object.as_ref().unwrap().heads(), vec!["telemetry"]);
        }
        other => panic!("expected a verbal relative, got {other:?}"),
    }
}

/// A particle word never OPENS an SVO run: `the power up fails` keeps its
/// round-3 reading (subject `the power up`, verb `fails`).
#[test]
fn particle_word_never_opens_a_run() {
    let s = one("When the power up fails, the fan shall run.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["up"]);
    let (verb, particle, object) = verbal(clause);
    assert_eq!((verb, particle), ("fails", None));
    assert!(object.is_none());
}

/// SUPERSEDED (round 11, change 1 — fail-closed): `backs up telemetry` is
/// a boundary-less run whose first word is verb-capable — the ambiguous
/// class (the final-word reading `the client backs up | telemetry` also
/// existed) — so it rejects; the determiner on the object keeps the
/// particle-verb reading provable.
#[test]
fn particle_after_svo_verb_with_bare_object() {
    assert_eq!(
        parse("When the client backs up telemetry, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    let s = one("When the client backs up the telemetry, the fan shall run.");
    let (verb, particle, object) = verbal(guard_clause(&s));
    assert_eq!((verb, particle), ("backs", Some("up")));
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
}

/// The particle list decides before the ambiguity check: `logs out` is a
/// particle verb with no object (a particle final never opens the
/// ambiguous class); `logs errors` is the ambiguous class since round 11
/// and rejects — the determiner rewrite keeps verb + object.
#[test]
fn logs_out_vs_logs_errors() {
    let s = one("When the user logs out, the session shall end.");
    let (verb, particle, object) = verbal(guard_clause(&s));
    assert_eq!((verb, particle), ("logs", Some("out")));
    assert!(object.is_none());
    assert_eq!(
        parse("When the user logs errors, the session shall end."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    let s = one("When the user logs the errors, the session shall end.");
    let (verb, particle, object) = verbal(guard_clause(&s));
    assert_eq!((verb, particle), ("logs", None));
    assert_eq!(object.unwrap().heads(), vec!["errors"]);
}

/// An np-first structured subject (of-chain) is unaffected: the chain
/// stays the subject and the run after it still reads SVO.
#[test]
fn np_first_of_chain_subject_with_svo_tail() {
    let s = one("When the owner of the file sends telemetry, the fan shall run.");
    let clause = guard_clause(&s);
    let so_lang::ast::NpGroup::Single(np) = &clause.subject else {
        panic!("expected a single subject");
    };
    assert_eq!(np.head, "owner");
    assert_eq!(np.of.as_ref().unwrap().head, "file");
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "sends");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
}

/// SUPERSEDED (round 11, change 1 — fail-closed): a four-word run is the
/// ambiguous class; the boundaried rewrite keeps modifiers + head as one
/// object.
#[test]
fn svo_four_word_run() {
    assert_eq!(
        parse("When the client sends raw telemetry data, the fan shall stop."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    let s = one("When the client sends the raw telemetry data, the fan shall stop.");
    let (verb, _, object) = verbal(guard_clause(&s));
    assert_eq!(verb, "sends");
    let Some(so_lang::ast::NpGroup::Single(np)) = object else {
        panic!("expected a single object");
    };
    assert_eq!(np.modifiers, vec!["raw", "telemetry"]);
    assert_eq!(np.head, "data");
}

/// SUPERSEDED (round 11, change 1 — fail-closed): a bare (determiner-less)
/// subject run of three or more words is the ambiguous class too; a bare
/// 2-word run keeps the verb-only reading (the two readings coincide).
#[test]
fn bare_subject_runs() {
    assert_eq!(
        parse("When clients send telemetry, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    let s = one("When clients send the telemetry, the fan shall run.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["clients"]);
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "send");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
    let s = one("When telemetry arrives, the fan shall run.");
    let (verb, _, object) = verbal(guard_clause(&s));
    assert_eq!(verb, "arrives");
    assert!(object.is_none());
}

/// SUPERSEDED (round 11, change 1 — fail-closed, resolving the round-10
/// scramble this pin recorded): `the backup daemon sends telemetry` read
/// subject `the backup`, verb `daemon`, object `sends telemetry` under
/// the round-10 minimal-subject SVO trade — the exact accepted-but-wrong
/// tree the fail-closed rule exists for. The shape is structurally
/// identical (det + 4 bare words) to `the client sends raw telemetry
/// data`, whose intended reading is the opposite split, so no
/// lexicon-free rule can satisfy both — round 11 rejects the whole class
/// instead of scrambling either. The boundary workaround still keeps the
/// multi-word subject.
#[test]
fn svo_multiword_subject() {
    assert_eq!(
        parse("When the backup daemon sends telemetry, the fan shall run."),
        Err(ParseError::AmbiguousVerbBoundary)
    );
    // A determiner boundary on the object keeps the full subject: the
    // verb sits before the first determiner-led phrase.
    let s = one("When the backup daemon sends the telemetry, the fan shall run.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["daemon"], "the boundary keeps the full subject");
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "sends");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
    // A role boundary after the verb does the same.
    let s = one("When the backup daemon fails after the timer expires, the fan shall run.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["daemon"], "boundary restores the full subject");
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "fails");
    assert!(object.is_none());
}

/// FINDING RESOLVED AS LEGISLATED (fixer, round 10): a bare SVO object
/// followed by a role phrase reads by the BOUNDARY rule — `When the
/// client sends telemetry to the admin,` is subject `the client sends`,
/// verb `telemetry`, recipient `admin` — the same prefix that reads SVO
/// without the role. The finding demanded SVO extension past role-prep
/// boundaries; but the boundary rule IS round 10's documented escape
/// hatch for multi-word subjects (`the backup daemon fails after the
/// timer expires` — subject `the backup daemon`), and that shape is
/// structurally identical (det + 3 bare words + role prep) to this one,
/// so extending SVO would scramble the hatch's own example. One
/// legislation cannot serve both without a lexicon; round 10 keeps the
/// hatch, and the flip is now documented (reference.md §3.3,
/// cookbook.md) with the determiner-object workaround pinned below.
#[test]
fn svo_with_trailing_role() {
    let s = one("When the client sends telemetry to the admin, the fan shall run.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["sends"], "boundary rule — legislated");
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "telemetry");
    assert!(object.is_none());
    // The documented workaround: a determiner on the object makes it the
    // boundary, keeping the SVO shape under a role.
    let s = one("When the client sends the telemetry to the admin, the fan shall run.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["client"]);
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "sends");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
}

/// Guard-atom identity reflects the object through the lossless anchor
/// (round 11: the boundaried rewrites of the round-10 bare-object pins —
/// same digest verb, different atoms, no false grounding).
#[test]
fn guard_atom_identity_reflects_bare_object() {
    let telemetry =
        applicability(&one("When the client sends the telemetry, the fan shall run."));
    let heartbeats =
        applicability(&one("When the client sends the heartbeats, the fan shall run."));
    assert_ne!(telemetry, heartbeats, "different objects, different atoms");
    let Formula::Atom { atom: AtomRef::Guard { clause, source, .. } } = &telemetry else {
        panic!("expected a guard atom");
    };
    assert_eq!(clause.words, vec!["sends"], "the digest's verb");
    assert_eq!(source, "the client sends the telemetry", "the anchor keeps the object");
    // Different objects never ground a contradiction …
    assert_eq!(
        assess(
            &one("When the client sends the telemetry, the fan shall run."),
            &one("When the client sends the heartbeats, the fan shall not run."),
        ),
        Outcome::Unknown
    );
    // … while the same object still does.
    assert_eq!(
        assess(
            &one("When the client sends the telemetry, the fan shall run."),
            &one("When the client sends the telemetry, the fan shall not run."),
        ),
        Outcome::HardContradiction
    );
}

/// Boundaried rewrites in every clause site render back to their words and
/// re-parse to a fixed point (round 11: the round-10 bare-run texts are
/// rejection pins above; relative bodies keep their fixed verb position,
/// so `who sends telemetry` stays as written).
#[test]
fn svo_render_round_trips() {
    for text in [
        "An upload means that the client sends the telemetry.",
        "Each user who sends telemetry shall authenticate.",
        "When the client backs up the telemetry, the fan shall run.",
        "When the user logs the errors, the session shall end.",
        "When clients send the telemetry, the fan shall run.",
        "When the owner of the file sends telemetry, the fan shall run.",
        "When the client sends the raw telemetry data, the fan shall stop.",
        "The pump shall stop, unless the client sends the telemetry data.",
    ] {
        let rendered = one(text).render();
        assert!(rendered.eq_ignore_ascii_case(text), "{rendered} vs {text}");
        assert_eq!(one(&rendered).render(), rendered, "re-parse is a fixed point: {text}");
    }
}

// =====================================================================
// change 6 — SameSubject becomes candidate data
// =====================================================================

/// An explicit-relied construction with shared keys succeeds, is proven,
/// and still rides as a candidate only.
#[test]
fn shared_keys_with_explicit_relied_constructs() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The daemon is available.");
    let relied = so_lang::formula::claim_formula(&source).unwrap();
    let built = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        relied,
    )
    .unwrap();
    assert_eq!(built.subject_relation, SubjectRelation::SharedKeys);
    assert!(built.proven);
    assert!(!built.contract_forming());
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&built));
    assert_eq!(paired.assumption, Formula::Top);
}

/// `from_sentence` (no target in hand) is legislated DisjointKeys.
/// SUPERSEDED CONSEQUENCE (round 11, change 3): a `from_sentence` source
/// carries the DEFAULT reliance, so it is a permanent candidate now — the
/// pre-round-11 "it entered A" reading is retired with the default-relied
/// contract forming itself.
#[test]
fn from_sentence_legislated_disjoint() {
    let source = AssumptionSource::from_sentence(
        EdgeKind::OccurrenceReliance,
        &one("The daemon is available."),
    )
    .unwrap();
    assert_eq!(source.subject_relation, SubjectRelation::DisjointKeys);
    assert!(!source.explicit_relied);
    assert!(!source.contract_forming(), "round 11: default reliance, candidate only");
}

/// The envelope_compatible `No` arm is reachable through for_guarantee
/// now that shared keys construct (round-10 consequence update).
#[test]
fn envelope_no_arm_reachable_through_for_guarantee() {
    let target = one("The client shall not retry.");
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    assert_eq!(envelope.subject_relation, SubjectRelation::SharedKeys);
    let paired = contract_formula(&target).unwrap().paired(std::slice::from_ref(&envelope));
    assert_eq!(envelope_compatible(&paired), Ternary::No);
}

/// Shared-key exclusion feeds satisfiability: the same contradicting pair
/// proves No against a disjoint target and returns to Unknown against a
/// shared-subject target, because neither source formed A there.
#[test]
fn shared_keys_never_poison_satisfiability() {
    let lo = "The queue is at most 3.";
    let hi = "The queue must be at least 5.";
    let disjoint_target = one("The daemon shall persist the Node.");
    // Round 11 (change 3): explicit reliances, so the disjoint pair forms A.
    let build = |target: &so_lang::ast::Sentence| {
        [
            explicit_source(EdgeKind::OccurrenceReliance, &one(lo), target),
            explicit_source(EdgeKind::OccurrenceReliance, &one(hi), target),
        ]
    };
    let paired = contract_formula(&disjoint_target)
        .unwrap()
        .paired(&build(&disjoint_target));
    assert_eq!(assumption_satisfiable(&paired), Ternary::No);
    let shared_target = one("The queue shall drain.");
    let sources = build(&shared_target);
    assert!(sources.iter().all(|s| s.subject_relation == SubjectRelation::SharedKeys));
    let paired = contract_formula(&shared_target).unwrap().paired(&sources);
    assert_eq!(paired.assumption, Formula::Top);
    assert_eq!(assumption_satisfiable(&paired), Ternary::Unknown);
}

/// Modifier keys still separate: `the backup daemon` is not `the daemon`.
#[test]
fn modifier_keys_stay_disjoint() {
    let target = one("The daemon shall flush the buffer.");
    // Round 11 (change 3): explicit reliance so contract forming is
    // observable.
    let source = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The backup daemon is available."),
        &target,
    );
    assert_eq!(source.subject_relation, SubjectRelation::DisjointKeys);
    assert!(source.contract_forming());
}

/// One shared item of a coordinated source subject is enough for
/// SharedKeys.
#[test]
fn coordinated_subject_partial_share() {
    let target = one("The daemon shall flush the buffer.");
    let source = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The daemon and the proxy are available."),
        &target,
    )
    .unwrap();
    assert_eq!(source.subject_relation, SubjectRelation::SharedKeys);
    assert!(!source.contract_forming());
}

// =====================================================================
// totality — seeded fuzz over multi-word bare tails and passive agents
// =====================================================================

/// A tiny deterministic LCG; no dependency, stable across runs.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn pick<'a>(&mut self, pool: &[&'a str]) -> &'a str {
        pool[(self.next() as usize) % pool.len()]
    }
}

/// Seeded fuzz: guards, exceptions, and passives assembled from a pool
/// that mixes plain words, particles, `ly` adverbs, reserved words, and
/// numbers. Parsing must never panic; an accepted sentence must render to
/// a fixed point and survive every derived view.
#[test]
fn totality_fuzz_bare_tails_and_passive_agents() {
    let words: &[&str] = &[
        "daemon", "client", "telemetry", "data", "sends", "logs", "out", "up", "off", "down",
        "quickly", "successfully", "backup", "power", "that", "to", "by", "no", "the", "and",
        "unless", "means", "shall", "reply", "5", "zero", "of", "owner", "file",
    ];
    let dets: &[&str] = &["the", "a", "each", "no", ""];
    let mut rng = Lcg(0x5eed_1006);
    let mut accepted = 0usize;
    for i in 0..4000 {
        let d1 = rng.pick(dets);
        let (w1, w2, w3, w4) =
            (rng.pick(words), rng.pick(words), rng.pick(words), rng.pick(words));
        let np = |det: &str, w: &str| {
            if det.is_empty() { w.to_string() } else { format!("{det} {w}") }
        };
        let text = match i % 5 {
            0 => format!("When {} {w2} {w3}, the pump shall stop.", np(d1, w1)),
            1 => format!("When {} {w2} {w3} {w4}, the pump shall stop.", np(d1, w1)),
            2 => format!("The pump shall stop, unless {} {w2} {w3}.", np(d1, w1)),
            3 => format!("The {w1} shall be {w2} by {} {w4}.", np(d1, w3)),
            _ => format!("The {w1} {w2} is {w3} by the {w4}."),
        };
        let Ok(mut spec) = parse(&text) else { continue };
        accepted += 1;
        let sentence = spec.sentences.remove(0);
        // Every derived view must be total over an accepted sentence.
        let _ = subject_keys(&sentence);
        let _ = responsible_subject_keys(&sentence);
        let _ = applicability(&sentence);
        let _ = so_lang::formula::claim_formula(&sentence);
        let _ = so_lang::semantics::skeleton(&sentence);
        let _ = contract_formula(&sentence);
        let _ = assess(&sentence, &sentence);
        let rendered = sentence.render();
        let reparsed = parse(&rendered).unwrap_or_else(|e| {
            panic!("render of an accepted sentence must re-parse: {text:?} -> {rendered:?}: {e}")
        });
        assert_eq!(
            reparsed.sentences[0].render(),
            rendered,
            "render fixed point: {text:?}"
        );
    }
    assert!(accepted > 100, "the fuzz corpus must exercise accepted sentences, got {accepted}");
}
