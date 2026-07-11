//! Round 10: responsible-subject derivation, the force gate on A, guard
//! roles, the SVO reading of bare-object verbal clauses, and SubjectRelation
//! as candidate data.

use so_lang::ast::TriggerKind;
use so_lang::formula::{
    applicability, contract_formula, AssumptionSource, AtomRef, EdgeKind, Formula, GuardRole,
};
use so_lang::parse::parse;
use so_lang::relate::{assess, Outcome};
use so_lang::semantics::{responsible_subject_keys, subject_keys};

fn one(input: &str) -> so_lang::ast::Sentence {
    parse(input).unwrap().sentences.remove(0)
}

// ---- change 1: responsible-subject derivation (passives) -------------------

/// The motivating sentence: the guarantee is keyed on `request` (the
/// grammatical patient), but the responsible component is the daemon — the
/// stated passive agent.
#[test]
fn passive_deontic_responsible_subject_is_the_agent() {
    let s = one("Each request shall be logged by the daemon.");
    assert_eq!(
        subject_keys(&s),
        vec!["request"],
        "the grammatical (patient) view is unchanged"
    );
    assert_eq!(responsible_subject_keys(&s), vec!["daemon"]);
}

/// A described passive derives the same way: the dedicated agent slot wins.
#[test]
fn passive_description_responsible_subject_is_the_agent() {
    let s = one("The report is submitted by the backup daemon.");
    assert_eq!(subject_keys(&s), vec!["report"]);
    assert_eq!(
        responsible_subject_keys(&s),
        vec!["backup.daemon"],
        "agent keys carry modifiers, exactly as subject keys do (round 5)"
    );
}

/// Active sentences are unchanged: the grammatical subject answers for the
/// claim, so the two views coincide.
#[test]
fn active_sentences_keep_the_grammatical_view() {
    for text in [
        "The daemon shall persist the Node.",
        "The pump should stop.",
        "The client may retry.",
        "The retry count is at most 3.",
        "The client is able to retry.",
    ] {
        let s = one(text);
        assert_eq!(responsible_subject_keys(&s), subject_keys(&s), "{text}");
    }
}

/// An agentless passive falls back to the grammatical subject: no better
/// identity is written.
#[test]
fn agentless_passive_falls_back_to_the_subject() {
    let s = one("Each request shall be logged.");
    assert_eq!(responsible_subject_keys(&s), vec!["request"]);
    let s = one("The report is submitted.");
    assert_eq!(responsible_subject_keys(&s), vec!["report"]);
}

/// A coordinated agent yields one key per item, in surface order.
#[test]
fn coordinated_agent_yields_one_key_per_item() {
    let s = one("The report shall be reviewed by the auditor and the owner.");
    assert_eq!(responsible_subject_keys(&s), vec!["auditor", "owner"]);
}

/// A definition has no responsible subject at all.
#[test]
fn definition_has_no_responsible_subject() {
    let s = one("A session means a sequence of requests.");
    assert!(responsible_subject_keys(&s).is_empty());
}

// ---- change 2: recommendations never enter A --------------------------------

/// A PROVEN recommended reliance is retained as a visible candidate but
/// never conjoined into A: a `should` states a preference, and hardening it
/// into an environmental assumption would let saturation relieve the
/// guarantee on a promise the environment never made.
#[test]
fn proven_recommended_source_never_forms_the_assumption() {
    let target = one("The daemon shall persist the Node.");
    let recommended = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The client should send the Node."),
        &target,
    )
    .unwrap();
    assert!(
        recommended.proven,
        "the default reliance is self-entailment — proven"
    );
    assert!(
        !recommended.contract_forming(),
        "recommended: candidate only, never in A"
    );
    let contract = contract_formula(&target).unwrap();
    let paired = contract.paired(std::slice::from_ref(&recommended));
    assert_eq!(
        paired.assumption,
        Formula::Top,
        "A is unchanged by a recommended source"
    );
    assert_eq!(
        paired.sources.len(),
        1,
        "the candidate is retained, visibly recommended"
    );
}

/// A binding source still forms A — with an explicitly selected reliance
/// (round 11, change 3) — and in a mixed pairing exactly the binding
/// reliance enters the conjunction.
#[test]
fn binding_source_forms_a_recommended_rides_alongside() {
    let target = one("The daemon shall persist the Node.");
    let client = one("The client shall send the Node.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &client, &target).unwrap();
    let binding = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::GuaranteeDischarge,
        &client,
        &target,
        default.formula.clone(),
    )
    .unwrap();
    assert!(binding.contract_forming());
    let recommended = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The monitor should verify the Node."),
        &target,
    )
    .unwrap();
    let contract = contract_formula(&target).unwrap();
    let paired = contract.paired(&[binding.clone(), recommended]);
    assert_eq!(
        paired.assumption, binding.relied,
        "exactly the binding reliance stands as A; the recommended one rides as a candidate"
    );
    assert_eq!(paired.sources.len(), 2);
}

/// Force-free descriptions still qualify (state reliance is unchanged) —
/// with an explicitly selected reliance (round 11, change 3).
#[test]
fn description_source_still_forms_a() {
    let target = one("The daemon shall persist the Node.");
    let queue = one("The queue is empty.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &queue, &target).unwrap();
    assert!(
        !default.contract_forming(),
        "default reliance: candidate only (round 11)"
    );
    let description = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &queue,
        &target,
        default.formula.clone(),
    )
    .unwrap();
    assert!(description.contract_forming());
}

// ---- change 5: SVO reading for trailing bare runs of two or more -------------
// SUPERSEDED by round 11 change 1: the boundary-less two-or-more run is the
// genuinely ambiguous class (SVO vs final-word) and now FAILS CLOSED
// (ParseError::AmbiguousVerbBoundary). The pins below record the rejection
// and the boundaried rewrites; length-1 runs, particle/number finals, and
// role-boundaried shapes keep their readings.

fn guard_clause(sentence: &so_lang::ast::Sentence) -> &so_lang::ast::Clause {
    if let Some(trigger) = &sentence.frames.trigger {
        return &trigger.clause.items[0];
    }
    if let Some(frame) = sentence.frames.states.first() {
        return &frame.clause.items[0];
    }
    sentence
        .exception
        .as_ref()
        .expect("a guard or exception clause")
}

fn verbal(clause: &so_lang::ast::Clause) -> (&str, Option<&str>, Option<&so_lang::ast::NpGroup>) {
    match &clause.body {
        so_lang::ast::ClauseBody::Verbal {
            verb,
            particle,
            object,
            ..
        } => (verb.as_str(), particle.as_deref(), object.as_ref()),
        other => panic!("expected a verbal body, got {other:?}"),
    }
}

/// SUPERSEDED (round 11, change 1 — fail-closed verb boundary): the
/// round-10 flagship `the client sends telemetry` is a boundary-less bare
/// run of two after the minimal subject, which admits BOTH the SVO
/// reading (round 10) and the long-subject final-word reading (round 3).
/// Accepted-but-wrong is worse than rejection, so the class fails closed;
/// the honest form puts a determiner on the object.
#[test]
fn svo_motivating_guard() {
    assert_eq!(
        parse("When the client sends telemetry, the daemon shall persist the Node."),
        Err(so_lang::parse::ParseError::AmbiguousVerbBoundary)
    );
    // The rewrite: the determiner is the boundary, so the verb position is
    // provable, not guessed.
    let s = one("When the client sends the telemetry, the daemon shall persist the Node.");
    let clause = guard_clause(&s);
    assert_eq!(clause.subject.heads(), vec!["client"]);
    let (verb, particle, object) = verbal(clause);
    assert_eq!(verb, "sends");
    assert_eq!(particle, None);
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
}

/// SUPERSEDED (round 11, change 1): a three-word run is the same ambiguous
/// class — rejected; the boundaried rewrite keeps the modifier + head
/// object.
#[test]
fn svo_three_word_run() {
    assert_eq!(
        parse("When the client sends telemetry data, the pump shall stop."),
        Err(so_lang::parse::ParseError::AmbiguousVerbBoundary)
    );
    let s = one("When the client sends the telemetry data, the pump shall stop.");
    let clause = guard_clause(&s);
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "sends");
    let Some(so_lang::ast::NpGroup::Single(np)) = object else {
        panic!("expected a single object")
    };
    assert_eq!(np.modifiers, vec!["telemetry"]);
    assert_eq!(np.head, "data");
}

/// Particles still lift per the round-4 rules: the particle-list check runs
/// before the object split, so `logs out` stays verb + particle, and a
/// particle after the SVO verb still joins it.
#[test]
fn svo_particle_interaction() {
    let s = one("When the user logs out, the session shall end.");
    let (verb, particle, object) = verbal(guard_clause(&s));
    assert_eq!((verb, particle), ("logs", Some("out")));
    assert!(object.is_none());
    // Particle between the SVO verb and a bare object.
    let s = one("When the daemon hands off the token, the session shall end.");
    let (verb, particle, object) = verbal(guard_clause(&s));
    assert_eq!((verb, particle), ("hands", Some("off")));
    assert_eq!(object.unwrap().heads(), vec!["token"]);
}

/// Length-1 runs keep the verb-only reading, exactly as calibrated in
/// round 3.
#[test]
fn svo_length_one_runs_unchanged() {
    for (text, subject_head, verb) in [
        (
            "When a session expires, the system shall close the session.",
            "session",
            "expires",
        ),
        ("While the pump runs, the fan shall run.", "pump", "runs"),
        (
            "When no backup completes, the operator shall act.",
            "backup",
            "completes",
        ),
    ] {
        let s = one(text);
        let clause = guard_clause(&s);
        assert_eq!(clause.subject.heads(), vec![subject_head], "{text}");
        let (v, _, object) = verbal(clause);
        assert_eq!(v, verb, "{text}");
        assert!(object.is_none(), "{text}");
    }
}

/// The fail-closed rule applies uniformly wherever a clause parses (round
/// 11, superseding the round-10 uniform-SVO pin): While frames,
/// exceptions, and clausal roles all reject the ambiguous class, and all
/// accept the boundaried rewrite.
#[test]
fn svo_covers_guards_exceptions_and_clausal_roles() {
    for text in [
        "While the client sends telemetry, the fan shall run.",
        "The pump shall stop, unless the client sends telemetry.",
        "The pump shall stop after the client sends telemetry.",
    ] {
        assert_eq!(
            parse(text),
            Err(so_lang::parse::ParseError::AmbiguousVerbBoundary),
            "{text}"
        );
    }
    let s = one("While the client sends the telemetry, the fan shall run.");
    let (verb, _, object) = verbal(guard_clause(&s));
    assert_eq!(verb, "sends");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
    let s = one("The pump shall stop, unless the client sends the telemetry.");
    let (verb, _, object) = verbal(s.exception.as_ref().unwrap());
    assert_eq!(verb, "sends");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
    let s = one("The pump shall stop after the client sends the telemetry.");
    let vp = match &s.core {
        so_lang::ast::Core::Deontic { vp, .. } => vp.single().unwrap(),
        other => panic!("expected a deontic core, got {other:?}"),
    };
    let Some(so_lang::ast::RolePp::After(clause)) = vp.roles.first() else {
        panic!("expected an After role")
    };
    let (verb, _, object) = verbal(clause);
    assert_eq!(verb, "sends");
    assert_eq!(object.unwrap().heads(), vec!["telemetry"]);
}

/// Boundaried rewrites render back to the words they were parsed from.
#[test]
fn svo_render_round_trips() {
    for text in [
        "When the client sends the telemetry, the daemon shall persist the Node.",
        "When the client sends the telemetry data, the pump shall stop.",
        "While the client sends the telemetry, the fan shall run.",
        "The pump shall stop, unless the client sends the telemetry.",
        "When the daemon hands off the token, the session shall end.",
    ] {
        let rendered = one(text).render();
        // The canonical render keeps every word (case-insensitively: a
        // sentence-initial determiner renders lowercased).
        assert!(rendered.eq_ignore_ascii_case(text), "{rendered} vs {text}");
        assert_eq!(
            one(&rendered).render(),
            rendered,
            "re-parse is a fixed point"
        );
    }
}

// ---- change 6: SameSubject becomes candidate data ----------------------------

use so_lang::formula::SubjectRelation;

/// A shared-key source CONSTRUCTS (the round-6 hard rejection is removed),
/// carries `SharedKeys`, and is excluded from A — candidate only.
#[test]
fn shared_key_source_constructs_and_stays_out_of_a() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The daemon is available.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    assert!(shared.proven, "default reliance is self-entailment");
    assert!(!shared.contract_forming(), "shared keys never form A");
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&shared));
    assert_eq!(paired.assumption, Formula::Top);
    assert_eq!(paired.sources.len(), 1, "retained as a visible candidate");
}

/// A disjoint-key source forms A — with an explicitly selected reliance
/// (round 11, change 3; the default-relied construction is a candidate).
#[test]
fn disjoint_key_source_forms_a() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert_eq!(default.subject_relation, SubjectRelation::DisjointKeys);
    assert!(
        !default.contract_forming(),
        "default reliance: candidate only (round 11)"
    );
    let ok = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        default.formula.clone(),
    )
    .unwrap();
    assert!(ok.contract_forming());
    let paired = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&ok));
    assert_eq!(paired.assumption, ok.relied);
}

/// The relation is computed from RESPONSIBLE keys (change 1) on both
/// sides: a passive source whose stated AGENT is the target's subject is
/// SharedKeys even though its grammatical subject (the patient) differs —
/// and a passive TARGET compares by its agent too.
#[test]
fn subject_relation_uses_responsible_keys() {
    // Source: the daemon is the responsible agent; target: the daemon.
    let target = one("The daemon shall flush the buffer.");
    let passive_source = one("Each event is logged by the daemon.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &passive_source, &target)
            .unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    // Passive target: `each request shall be logged by the daemon` is the
    // daemon's obligation, so a source about the daemon shares keys …
    let passive_target = one("Each request shall be logged by the daemon.");
    let source = one("The daemon is available.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &passive_target)
            .unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    // … while a source about the request (the patient) is DISJOINT: the
    // grammatical view would have collided here (round-6 behavior); the
    // responsible view does not.
    let patient_source = one("The request is valid.");
    let ok = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &patient_source,
        &passive_target,
    )
    .unwrap();
    assert_eq!(ok.subject_relation, SubjectRelation::DisjointKeys);
}

/// Serde: `subject_relation` rides on the wire; a pre-round-10 source
/// without the field loads as `DisjointKeys` — the documented pre-round-10
/// reading.
#[test]
fn subject_relation_serde_default() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The daemon is available.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let json = serde_json::to_value(&shared).unwrap();
    assert_eq!(json["subject_relation"], serde_json::json!("shared_keys"));
    let back: AssumptionSource = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(back, shared);
    let mut legacy = json;
    legacy.as_object_mut().unwrap().remove("subject_relation");
    let back: AssumptionSource = serde_json::from_value(legacy).unwrap();
    assert_eq!(back.subject_relation, SubjectRelation::DisjointKeys);
}

// ---- change 4: guard atoms carry the frame role ------------------------------

/// The guard atom of each frame family carries its role.
#[test]
fn guard_atoms_carry_their_frame_role() {
    let role_of = |text: &str| match applicability(&one(text)) {
        Formula::Atom {
            atom: AtomRef::Guard { role, .. },
        } => role,
        Formula::Not { inner } => match *inner {
            Formula::Atom {
                atom: AtomRef::Guard { role, .. },
            } => role,
            other => panic!("expected a guard atom, got {other:?}"),
        },
        other => panic!("expected a guard atom, got {other:?}"),
    };
    assert_eq!(
        role_of("Where the mode is active, the pump shall run."),
        GuardRole::Scope
    );
    assert_eq!(
        role_of("While the pump runs, the fan shall run."),
        GuardRole::State
    );
    assert_eq!(
        role_of("When the order ships, the fan shall run."),
        GuardRole::Trigger {
            kind: TriggerKind::Event
        }
    );
    assert_eq!(
        role_of("If the order ships, then the fan shall run."),
        GuardRole::Trigger {
            kind: TriggerKind::Contingency
        }
    );
    assert_eq!(
        role_of("The fan shall run, unless the order ships."),
        GuardRole::Exception
    );
}

/// The motivating false overlap: `While the pump runs,` and `When the pump
/// runs,` produced EQUAL guard atoms (same clause digest, same render) and
/// grounded a contradiction. With roles in atom identity the pair is
/// Unknown — a span and an instant are different conditions.
#[test]
fn while_vs_when_same_words_is_unknown() {
    assert_eq!(
        assess(
            &one("While the pump runs, the fan shall run."),
            &one("When the pump runs, the fan shall not run."),
        ),
        Outcome::Unknown
    );
    // Same role, same words: unchanged — still grounds.
    assert_eq!(
        assess(
            &one("While the pump runs, the fan shall run."),
            &one("While the pump runs, the fan shall not run."),
        ),
        Outcome::HardContradiction
    );
    assert_eq!(
        assess(
            &one("When the pump runs, the fan shall run."),
            &one("When the pump runs, the fan shall not run."),
        ),
        Outcome::HardContradiction
    );
}

/// Exception-role atoms are distinct from state atoms: a `While X` guard
/// and an `unless X` carve-out over the same words are different atoms
/// (the exception's negation still composes in the applicability formula).
#[test]
fn exception_role_atoms_are_distinct_from_state_atoms() {
    let state = applicability(&one("While the pump runs, the fan shall run."));
    let exception = applicability(&one("The fan shall run, unless the pump runs."));
    let Formula::Not { inner } = exception else {
        panic!("an exception applicability is a negation");
    };
    assert_ne!(
        state, *inner,
        "same words, different roles — different atoms"
    );
}

/// The round-7 vacuous-region gate survives role identity: a trigger equal
/// to its own exception still proves the region empty (role-BLIND by
/// legislation — the carve-out fails wherever the sentence would apply),
/// so the vacuous pair still witnesses nothing.
#[test]
fn trigger_equal_to_its_own_exception_still_asserts_nothing() {
    assert_eq!(
        assess(
            &one("When the pump runs, the fan shall run, unless the pump runs."),
            &one("When the pump runs, the fan shall not run, unless the pump runs."),
        ),
        Outcome::Unknown,
        "two vacuous sentences must not manufacture a contradiction"
    );
}

/// Serde: the role rides on the wire; a pre-round-10 guard atom without a
/// `role` field loads as `State` — the documented legacy reading; the
/// trigger role's kind field is `"trigger"` on the wire (the enum is
/// internally tagged by `"kind"`).
#[test]
fn guard_role_serde_shapes() {
    let f = applicability(&one("When the order ships, the fan shall run."));
    let json = serde_json::to_value(&f).unwrap();
    assert_eq!(
        json["atom"]["role"],
        serde_json::json!({ "kind": "trigger", "trigger": "event" })
    );
    let back: Formula = serde_json::from_value(json).unwrap();
    assert_eq!(back, f);
    // Legacy: no role field → State, documented as the pre-round-10 reading.
    let mut legacy = serde_json::to_value(&f).unwrap();
    legacy["atom"].as_object_mut().unwrap().remove("role");
    let back: Formula = serde_json::from_value(legacy).unwrap();
    match back {
        Formula::Atom {
            atom: AtomRef::Guard { role, .. },
        } => {
            assert_eq!(role, GuardRole::State);
        }
        other => panic!("expected a guard atom, got {other:?}"),
    }
}
