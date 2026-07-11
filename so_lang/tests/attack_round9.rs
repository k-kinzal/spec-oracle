//! Adversarial conformance attack on the ROUND-9 changes.
//!
//! The code is the object under test; the round-9 spec (IMPROVE-SPEC-9) is
//! the contract. Attacked surfaces:
//!
//! 1. Locative prepositions in role identity (`in` vs `on` … across verb
//!    phrases, guard clauses, and description positions; serde shapes).
//! 2. Proven-only contract-forming pairing (`paired` conjoins only proven,
//!    non-envelope reliances; candidates and envelopes stay out of A).
//! 3. Object-gap relatives (`each request that the gateway forwards`),
//!    their false-positive guards, digests, and the recognizer's budget.
//! 4. Content complements in verbal clause bodies (guards, exceptions,
//!    `until` clauses), their digests and relate gating.
//! 5. Guard canonicalization and the interval overlap witness.
//! 6. The descending-`between` parse error.
//! 7. Totality under seeded fuzz mixing all of the above.
//!
//! Round-9 fix round: the four findings this attack surfaced (the
//! shortest-split scan rejecting modifier/quantifier-led gap subjects,
//! the exponential nested-gap blowup, and the `Measure::Np` duplicate
//! `kind` field) are fixed, their tests un-`#[ignore]`d, and the two
//! current-behavior companion pins re-pinned to the legislated fixes.
//! Everything here is a permanent pin of legislated behavior.

use so_lang::ast::*;
use so_lang::formula::{claim_formula, contract_formula, AssumptionSource, EdgeKind, Formula};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{assess, assumption_satisfiable, contradicts, implies, Outcome, Ternary};
use so_lang::semantics::{skeleton, subject_keys, ClauseSkeleton, RoleKind, RoleSkeleton};
use std::panic::{catch_unwind, AssertUnwindSafe};

fn one(input: &str) -> Sentence {
    let spec = parse(input).expect(input);
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn err(input: &str) -> ParseError {
    parse(input).expect_err(input)
}

/// Canonical render re-parses to the same tree (source aside) and is a
/// fixpoint.
fn roundtrip(input: &str) {
    let s = one(input);
    let rendered = s.render();
    let back = one(&rendered);
    assert_eq!(
        back.render(),
        rendered,
        "render must be a fixpoint for {input:?}"
    );
    let mut a = s.clone();
    a.source = String::new();
    let mut b = back;
    b.source = String::new();
    assert_eq!(
        a, b,
        "canonical form must re-parse to the same tree for {input:?}"
    );
}

/// The single atom of a behavioral sentence's skeleton.
fn atom(input: &str) -> so_lang::semantics::Atom {
    let k = skeleton(&one(input)).unwrap();
    assert_eq!(k.atoms.len(), 1, "{input:?}");
    k.atoms.into_iter().next().unwrap().clone()
}

// ====================================================================================
// 1. Locative identity: in/on/at/under/over/above/below
// ====================================================================================

const LOCATIVES: [&str; 7] = ["in", "on", "at", "under", "over", "above", "below"];

#[test]
fn all_seven_locative_prepositions_are_pairwise_distinct_in_vp_roles() {
    let atoms: Vec<_> = LOCATIVES
        .iter()
        .map(|p| atom(&format!("The crane shall move the beam {p} the platform.")))
        .collect();
    for (i, a) in atoms.iter().enumerate() {
        // Each atom carries its own preposition as the Location marker.
        let role = &a.roles[0];
        assert_eq!(role.kind, RoleKind::Location);
        assert_eq!(role.marker.as_deref(), Some(LOCATIVES[i]));
        for (j, b) in atoms.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(
                    a, b,
                    "{} vs {} must not share an atom",
                    LOCATIVES[i], LOCATIVES[j]
                );
                // The marker is the ONLY difference: the value digest matches.
                assert_eq!(a.roles[0].value, b.roles[0].value);
            }
        }
    }
}

#[test]
fn locative_pairs_relate_unknown_never_yes_never_no() {
    let in_ = claim_formula(&one("The crane shall move the beam in the platform.")).unwrap();
    let under = claim_formula(&one("The crane shall move the beam under the platform.")).unwrap();
    assert_eq!(implies(&in_, &under), Ternary::Unknown);
    assert_eq!(implies(&under, &in_), Ternary::Unknown);
    assert_eq!(contradicts(&in_, &under), Ternary::Unknown);
    assert_eq!(
        assess(
            &one("The crane shall move the beam above the platform."),
            &one("The crane shall move the beam below the platform."),
        ),
        Outcome::Unknown,
        "above vs below is Unknown — disjointness of places is not provable syntactically"
    );
}

#[test]
fn same_locative_preposition_still_matches_end_to_end() {
    assert_eq!(
        assess(
            &one("The system shall store the report under the ledge."),
            &one("The system shall store the report under the ledge."),
        ),
        Outcome::Equivalent
    );
    // Casing never splits: the marker is lowercased.
    assert_eq!(
        atom("The system shall store the report OVER the archive."),
        atom("The system shall store the report over the archive."),
    );
}

#[test]
fn locative_identity_in_guard_clause_position() {
    // Same guard except `in` vs `on`: the guards no longer witness one
    // region, so the claim conflict stays Unknown.
    assert_eq!(
        assess(
            &one("While the pump runs in the bay, the fan shall spin."),
            &one("While the pump runs on the bay, the fan shall not spin."),
        ),
        Outcome::Unknown
    );
    // Same preposition: one region, hard contradiction.
    assert_eq!(
        assess(
            &one("While the pump runs in the bay, the fan shall spin."),
            &one("While the pump runs in the bay, the fan shall not spin."),
        ),
        Outcome::HardContradiction
    );
    // The guard digest itself carries the marker.
    let k = skeleton(&one("While the pump runs in the bay, the fan shall spin.")).unwrap();
    let role = &k.guards.states[0].roles[0];
    assert_eq!(role.kind, RoleKind::Location);
    assert_eq!(role.marker.as_deref(), Some("in"));
}

#[test]
fn locative_identity_in_description_role_position() {
    // The round-8 description role tail (behind a passive agent) digests
    // Location markers too.
    let d_in = skeleton(&one("The request is logged by the daemon in the vault.")).unwrap();
    let d_on = skeleton(&one("The request is logged by the daemon on the vault.")).unwrap();
    assert_ne!(d_in.atoms[0], d_on.atoms[0]);
    assert_eq!(d_in.atoms[0].roles[1].marker.as_deref(), Some("in"));
    assert_eq!(
        assess(
            &one("The request is logged by the daemon in the vault."),
            &one("The request is logged by the daemon on the vault."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("The request is logged by the daemon in the vault."),
            &one("The request is logged by the daemon in the vault."),
        ),
        Outcome::Equivalent
    );
    // Agentless descriptions keep the preposition inside the predicate
    // words, so the pair already separates there.
    assert_eq!(
        assess(
            &one("The report is stored in the archive."),
            &one("The report is stored on the archive."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn locative_marker_serde_shape() {
    let k = skeleton(&one("The pump shall run at the depot.")).unwrap();
    let json = serde_json::to_value(&k.atoms[0].roles[0]).unwrap();
    assert_eq!(json["marker"], "at");
    // Non-locative roles carry no marker field at all (pre-round-9 shape).
    let k = skeleton(&one("The daemon shall send the report to the auditor.")).unwrap();
    let json = serde_json::to_value(&k.atoms[0].roles[0]).unwrap();
    assert!(
        json.get("marker").is_none(),
        "Recipient must serialize without a marker"
    );
    // A pre-round-9 skeleton (no marker) loads as marker: None.
    let old: RoleSkeleton = serde_json::from_value(serde_json::json!({
        "kind": "location",
        "value": { "kind": "heads", "items": [
            { "quantifier": { "kind": "definite" }, "head": "archive", "full": "archive" }
        ]}
    }))
    .unwrap();
    assert!(old.marker.is_none());
}

// ====================================================================================
// 2. Proven-only contract-forming pairing
// ====================================================================================

/// A proven reliance. Round 11 (change 3): selected EXPLICITLY (the whole
/// source conditional through the graph-edge entry point) — the default
/// reliance is a permanent candidate now and never forms A.
fn proven_source(target: &Sentence) -> AssumptionSource {
    let source = one("The gateway shall forward the record.");
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        target,
        default.formula,
    )
    .unwrap()
}

/// An UNPROVEN (candidate) reliance: the source does not provably entail
/// the relied formula (`Unknown` at construction).
fn candidate_source(target: &Sentence) -> AssumptionSource {
    AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &one("The scheduler shall start the job."),
        target,
        claim_formula(&one("The scheduler shall start the batch.")).unwrap(),
    )
    .unwrap()
}

#[test]
fn unproven_source_is_accepted_but_never_enters_the_assumption() {
    let target = one("The daemon shall persist the record.");
    let c = contract_formula(&target).unwrap();
    let b = candidate_source(&target);
    assert!(
        !b.proven,
        "an Unknown entailment must build visibly unproven"
    );
    assert!(!b.contract_forming());
    let paired = c.paired(std::slice::from_ref(&b));
    assert_eq!(
        paired.assumption,
        Formula::Top,
        "a candidate edge must not relieve G"
    );
    assert_eq!(
        paired.sources.len(),
        1,
        "the candidate is retained for the graph layer"
    );
    assert!(!paired.sources[0].proven);
    // Saturation of a candidate-only pairing is the guarantee itself:
    // nothing was assumed, so nothing relieves.
    assert_eq!(paired.saturated(), paired.guarantee);
}

#[test]
fn proven_source_enters_the_assumption_alone_and_mixed() {
    let target = one("The daemon shall persist the record.");
    let c = contract_formula(&target).unwrap();
    let a = proven_source(&target);
    assert!(a.proven, "the default reliance is self-entailment — proven");
    assert!(a.contract_forming());
    // Alone: A is the lone relied formula, not a one-item And.
    let paired = c.paired(std::slice::from_ref(&a));
    assert_eq!(paired.assumption, a.relied);
    // Mixed with a candidate and an envelope: A is STILL the lone proven
    // reliance; both others are retained as sources only.
    let b = candidate_source(&target);
    let env = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let mixed = c.paired(&[a.clone(), b, env]);
    assert_eq!(mixed.assumption, a.relied);
    assert_eq!(mixed.sources.len(), 3);
    // Saturated shape: G ∨ ¬A over exactly the proven reliance — the
    // envelope is never negated by saturation.
    match mixed.saturated() {
        Formula::Or { items } => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], mixed.guarantee);
            assert_eq!(
                items[1],
                Formula::Not {
                    inner: Box::new(a.relied.clone())
                }
            );
        }
        other => panic!("expected G ∨ ¬A, got {other:?}"),
    }
}

#[test]
fn envelope_is_proven_yet_never_contract_forming() {
    let target = one("The daemon shall persist the record.");
    let env = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    assert!(
        env.proven,
        "the default reliance is self-entailment even for envelopes"
    );
    assert!(
        !env.contract_forming(),
        "envelopes are compatibility data, not conjuncts"
    );
    let c = contract_formula(&target).unwrap();
    let paired = c.paired(std::slice::from_ref(&env));
    assert_eq!(paired.assumption, Formula::Top);
    assert_eq!(paired.saturated(), paired.guarantee);
    assert_eq!(paired.sources.len(), 1);
}

#[test]
fn two_proven_contradictory_reliances_make_a_unsatisfiable() {
    let target = one("The daemon shall drain the queue.");
    // Round 11 (change 3): both reliances are selected explicitly so they
    // form A — a default reliance never enters it.
    let explicit = |text: &str| {
        let source = one(text);
        let default =
            AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target)
                .unwrap();
        AssumptionSource::for_guarantee_with_relied(
            EdgeKind::OccurrenceReliance,
            &source,
            &target,
            default.formula,
        )
        .unwrap()
    };
    let s1 = explicit("The queue depth is at most 3.");
    let s2 = explicit("The queue depth is at least 5.");
    let c = contract_formula(&target).unwrap();
    assert_eq!(assumption_satisfiable(&c.paired(&[s1, s2])), Ternary::No);
}

#[test]
fn a_candidate_cannot_poison_assumption_satisfiability() {
    // The same contradiction, but the `at least 5` side arrives as an
    // UNPROVEN reliance of an unrelated source: it never enters A, so the
    // verdict is about the assumption actually formed — not disproven.
    let target = one("The daemon shall drain the queue.");
    let s1 = AssumptionSource::for_guarantee(
        EdgeKind::OccurrenceReliance,
        &one("The queue depth is at most 3."),
        &target,
    )
    .unwrap();
    let s2 = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &one("The sensor shall report the depth."),
        &target,
        claim_formula(&one("The queue depth is at least 5.")).unwrap(),
    )
    .unwrap();
    assert!(!s2.proven);
    let c = contract_formula(&target).unwrap();
    assert_eq!(
        assumption_satisfiable(&c.paired(&[s1, s2])),
        Ternary::Unknown
    );
}

#[test]
fn pre_round8_json_sources_load_unproven_and_stay_candidates() {
    let target = one("The daemon shall persist the record.");
    let a = proven_source(&target);
    let mut json = serde_json::to_value(&a).unwrap();
    json.as_object_mut().unwrap().remove("proven");
    json.as_object_mut().unwrap().remove("relied");
    let old: AssumptionSource = serde_json::from_value(json).unwrap();
    // relied defaults to the source formula; proven defaults to FALSE —
    // an old edge is never silently promoted.
    assert_eq!(old.relied, old.formula);
    assert!(!old.proven);
    assert!(!old.contract_forming());
    let c = contract_formula(&target).unwrap();
    let paired = c.paired(std::slice::from_ref(&old));
    assert_eq!(
        paired.assumption,
        Formula::Top,
        "an old-JSON (unproven) source must not enter A under the round-9 doctrine"
    );
    assert_eq!(paired.sources.len(), 1);
}

// ====================================================================================
// 3. Object-gap relatives
// ====================================================================================

#[test]
fn the_gateway_sentence_parses_as_an_object_gap() {
    let s = one("Each request that the gateway forwards shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!("expected deontic single subject");
    };
    let rel = np.relative.as_ref().unwrap();
    assert_eq!(rel.marker, RelMarker::That);
    match &rel.body {
        RelativeBody::ObjectGap {
            subject,
            verb,
            particle,
            manner,
            roles,
        } => {
            assert_eq!(subject.heads(), vec!["gateway"]);
            assert_eq!(verb, "forwards");
            assert!(particle.is_none());
            assert!(manner.is_empty());
            assert!(roles.is_empty());
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip("Each request that the gateway forwards shall be logged.");
}

#[test]
fn who_form_object_gap() {
    let s = one("Each user who the auditor flags shall be reviewed.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    let rel = np.relative.as_ref().unwrap();
    assert_eq!(rel.marker, RelMarker::Who);
    assert!(matches!(rel.body, RelativeBody::ObjectGap { .. }));
    roundtrip("Each user who the auditor flags shall be reviewed.");
}

#[test]
fn object_gap_with_particle_manner_and_roles() {
    // Particle + manner.
    let s = one("Each ticket that the operator closes out promptly shall be archived.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap {
            verb,
            particle,
            manner,
            ..
        } => {
            assert_eq!(verb, "closes");
            assert_eq!(particle.as_deref(), Some("out"));
            assert_eq!(manner, &vec!["promptly".to_string()]);
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip("Each ticket that the operator closes out promptly shall be archived.");
    // Roles, locatives included, attach to the GAP's verb (innermost).
    let s = one(
        "Each request that the gateway forwards at the depot within 5 seconds shall be logged.",
    );
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { roles, .. } => {
            assert!(
                matches!(&roles[0], RolePp::Location { preposition, .. } if preposition == "at")
            );
            assert!(matches!(&roles[1], RolePp::Deadline(_)));
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip(
        "Each request that the gateway forwards at the depot within 5 seconds shall be logged.",
    );
    roundtrip(
        "Each request that the gateway forwards to the auditor via the relay shall be logged.",
    );
}

#[test]
fn object_gap_subject_takes_coordination_and_of_chains() {
    let s = one("Each request that the gateway and the proxy forward shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { subject, verb, .. } => {
            assert_eq!(subject.heads(), vec!["gateway", "proxy"]);
            assert_eq!(verb, "forward");
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    roundtrip("Each request that the gateway and the proxy forward shall be logged.");
    roundtrip("Each request that the owner of the gateway forwards shall be logged.");
}

#[test]
fn object_gap_composes_with_other_positions() {
    // Core object position.
    let s = one("The daemon shall log the event that the monitor records.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!()
    };
    let NpGroup::Single(np) = vp.single().unwrap().object.as_ref().unwrap() else {
        panic!()
    };
    assert!(matches!(
        np.relative.as_ref().unwrap().body,
        RelativeBody::ObjectGap { .. }
    ));
    // A `that` after a NOUN is that noun's relative (the gap), never a
    // content complement.
    assert!(vp.single().unwrap().content.is_none());
    // Guard subject and guard object positions.
    roundtrip("When the report that the auditor files arrives, the daemon shall alert.");
    roundtrip("When the daemon logs the event that the monitor records, the alarm shall sound.");
    // Exception and description positions.
    roundtrip("The pump shall stop, unless the report that the auditor files arrives.");
    roundtrip("Each request that the gateway forwards is logged.");
}

#[test]
fn object_gap_false_positive_guards() {
    // that + copular stays copular.
    let s = one("Each request that is valid shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    assert!(matches!(
        np.relative.as_ref().unwrap().body,
        RelativeBody::Copular { .. }
    ));
    let s = one("Each user who is flagged shall be reviewed.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    assert!(matches!(
        np.relative.as_ref().unwrap().body,
        RelativeBody::Copular { .. }
    ));
    // Subject-gap verbal relatives are unchanged.
    let s = one("Each request that arrives from the gateway shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::Verbal { verb, roles, .. } => {
            assert_eq!(verb, "arrives");
            assert!(matches!(&roles[0], RolePp::Source(_)));
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
    // LEGISLATED: a BARE noun phrase after that/who keeps the round-7
    // verb + object reading — no lexicon could tell it from a gap.
    let s = one("Each daemon that holds locks shall run.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "holds");
            assert_eq!(object.as_ref().unwrap().heads(), vec!["locks"]);
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
    // The same legislated collision under `who`: `who auditors flag` reads
    // verb `auditors` + object `flag` (documented, surprising, pinned).
    let s = one("Each user who auditors flag shall be reviewed.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    assert!(matches!(
        &np.relative.as_ref().unwrap().body,
        RelativeBody::Verbal { verb, .. } if verb == "auditors"
    ));
}

#[test]
fn explicit_object_after_gap_verb_keeps_determiner_as_verb_diagnosis() {
    assert_eq!(
        err("Each request that the gateway forwards the packet shall be logged."),
        ParseError::DeterminerAsVerb { word: "the".into() }
    );
}

// ---- FINDINGS: the shortest-subject-split heuristic self-destructs ---------------------

/// FINDING (major, FIXED): an object-gap subject carrying a MODIFIER was
/// rejected — `that the backup daemon raises` split at the shortest
/// prefix (subject `the backup`, "verb" `daemon`), saw `raises` as
/// object material, and abandoned the gap. The fix makes a bare
/// non-numeric word after a candidate verb CONTINUE the split scan (a
/// longer subject may absorb it) instead of aborting; the spec admits
/// every "determiner/quantifier-led noun phrase" as the gap subject.
#[test]
fn finding_object_gap_subject_with_modifier_should_parse() {
    let s = one("Each alert that the backup daemon raises shall be recorded.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { subject, verb, .. } => {
            assert_eq!(subject.render(), "the backup daemon");
            assert_eq!(verb, "raises");
        }
        other => panic!("expected object gap, got {other:?}"),
    }
}

/// Companion pin, RE-PINNED to the fix (it previously pinned the
/// DeterminerAsVerb rejection): the modifier-subject gap round-trips,
/// and the det-led mirror of the bare-NP collision is LEGISLATED — in
/// `that the session holds locks` the grammar has no verb lexicon to
/// prefer the saturated `holds` + `locks` reading (which never parsed
/// here: a determiner cannot open a verbal tail), so the longer subject
/// `the session holds` + verb `locks` wins. An EXPLICIT object after a
/// candidate verb (det/quantifier-led, group-marked, or numeric) still
/// kills the gap at every split.
#[test]
fn modifier_gap_subject_legislation() {
    roundtrip("Each alert that the backup daemon raises shall be recorded.");
    let s = one("Each request that the session holds locks shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    match &np.relative.as_ref().unwrap().body {
        RelativeBody::ObjectGap { subject, verb, .. } => {
            assert_eq!(subject.render(), "the session holds");
            assert_eq!(verb, "locks");
        }
        other => panic!("expected object gap, got {other:?}"),
    }
    // Numeric objects are explicit objects: no gap, round-6 diagnosis.
    assert_eq!(
        err("Each request that the gateway forwards 5 packets shall be logged."),
        ParseError::DeterminerAsVerb { word: "the".into() }
    );
}

/// FINDING (major, same family, FIXED): a QUANTIFIER-led gap subject —
/// the other half of the spec's "determiner/quantifier-led" — was
/// rejected: the split read `at` / `exactly` as a bare noun-phrase head,
/// committed, and aborted. The fix starts the verb scan past the whole
/// determiner/quantifier, where the subject's head must still follow.
#[test]
fn finding_object_gap_subject_quantifier_led_should_parse() {
    let s = one("Each request that at least 3 gateways forward shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    assert!(matches!(
        &np.relative.as_ref().unwrap().body,
        RelativeBody::ObjectGap { .. }
    ));
}

/// Companion pin, RE-PINNED to the fix (it previously pinned the
/// DeterminerAsVerb rejections): quantifier-led gap subjects round-trip
/// with the quantifier structured in the subject's determiner slot.
#[test]
fn quantifier_gap_subjects_roundtrip_with_structured_quantifier() {
    for (input, n) in [
        (
            "Each request that at least 3 gateways forward shall be logged.",
            Det::AtLeast { n: 3 },
        ),
        (
            "Each request that exactly 3 gateways forward shall be logged.",
            Det::Exactly { n: 3 },
        ),
    ] {
        roundtrip(input);
        let s = one(input);
        let Core::Deontic {
            subject: NpGroup::Single(np),
            ..
        } = &s.core
        else {
            panic!()
        };
        let RelativeBody::ObjectGap {
            subject: NpGroup::Single(gap_subject),
            verb,
            ..
        } = &np.relative.as_ref().unwrap().body
        else {
            panic!("expected object gap in {input:?}")
        };
        assert_eq!(gap_subject.det, Some(n));
        assert_eq!(gap_subject.head, "gateways");
        assert_eq!(verb, "forward");
    }
}

// ---- digests, keys, serde, depth ----------------------------------------------------

#[test]
fn object_gap_enters_np_full_but_never_subject_keys() {
    let s = one("Each request that the gateway forwards shall be logged.");
    let k = skeleton(&s).unwrap();
    assert_eq!(k.subject.full, "request that the gateway forwards");
    // Relatives never enter keys (pinned).
    assert_eq!(subject_keys(&s), vec!["request".to_string()]);
    // Lossiness: differing gaps block Yes; identical gaps still meet.
    assert_eq!(
        assess(
            &one("Each request that the gateway forwards shall be logged."),
            &one("Each request that the proxy forwards shall be logged."),
        ),
        Outcome::Unknown
    );
    assert_eq!(
        assess(
            &one("Each request that the gateway forwards shall be logged."),
            &one("Each request that the gateway forwards shall be logged."),
        ),
        Outcome::Equivalent
    );
}

#[test]
fn object_gap_serde_shape_and_old_json() {
    let s = one("Each request that the gateway forwards shall be logged.");
    let Core::Deontic {
        subject: NpGroup::Single(np),
        ..
    } = &s.core
    else {
        panic!()
    };
    let body = &np.relative.as_ref().unwrap().body;
    let json = serde_json::to_value(body).unwrap();
    assert_eq!(json["kind"], "object_gap");
    // Optional slots are skipped when empty, so the wire shape stays lean.
    let keys: Vec<&String> = json.as_object().unwrap().keys().collect();
    assert!(
        !keys
            .iter()
            .any(|k| *k == "particle" || *k == "manner" || *k == "roles"),
        "{keys:?}"
    );
    let back: RelativeBody = serde_json::from_value(json).unwrap();
    assert_eq!(&back, body);
    // Pre-round-9 verbal relative JSON still loads.
    let old: RelativeBody = serde_json::from_value(serde_json::json!({
        "kind": "verbal", "verb": "arrives", "object": null
    }))
    .unwrap();
    assert!(matches!(old, RelativeBody::Verbal { ref verb, .. } if verb == "arrives"));
}

#[test]
fn object_gap_nesting_is_depth_bounded_at_small_depths() {
    // Three levels parse and round-trip.
    let mut np = String::from("the proxy");
    for i in 0..3 {
        np = format!("the node{i} that {np} monitors");
    }
    roundtrip(&format!("Each request that {np} forwards shall be logged."));
}

/// FINDING (critical, FIXED): nested object-gap relatives blew up
/// EXPONENTIALLY (~7× per level; a ~60-token nest effectively hung the
/// recognizer, the depth budget unreachable), violating the totality
/// claim. The fix memoizes exact-prefix noun-phrase parses per sentence
/// (a packrat table scoped to `parse_sentence`), making the split scans
/// polynomial: 24 levels now parse in milliseconds, and past the depth
/// budget the nested prefix fails inside the scan, so the whole shape
/// falls back to the round-6 `DeterminerAsVerb` rejection — a rejection,
/// never a hang.
#[test]
fn finding_nested_object_gaps_must_stay_polynomial() {
    let mut np = String::from("the proxy");
    for i in 0..24 {
        np = format!("the node{i} that {np} monitors");
    }
    let deep = format!("Each request that {np} forwards shall be logged.");
    assert!(parse(&deep).is_ok(), "24 gap levels must parse");
    roundtrip(&deep);
    // Past the depth budget: still total, rejected not hung.
    let mut np = String::from("the proxy");
    for i in 0..120 {
        np = format!("the node{i} that {np} monitors");
    }
    assert_eq!(
        err(&format!("Each request that {np} forwards shall be logged.")),
        ParseError::DeterminerAsVerb { word: "the".into() }
    );
}

// ====================================================================================
// 4. Content complements in verbal clause bodies
// ====================================================================================

#[test]
fn the_motivating_guard_parses_with_structured_content() {
    let s = one("When the monitor ensures that the token is valid, the daemon shall proceed.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal {
            verb,
            object,
            content,
            ..
        } => {
            assert_eq!(verb, "ensures");
            assert!(object.is_none());
            let content = content.as_ref().unwrap();
            assert_eq!(content.subject.heads(), vec!["token"]);
            assert!(matches!(content.body, ClauseBody::Copular { .. }));
        }
        other => panic!("expected verbal body with content, got {other:?}"),
    }
    roundtrip("When the monitor ensures that the token is valid, the daemon shall proceed.");
}

#[test]
fn guard_content_digest_carries_the_lossiness_anchor() {
    let k = skeleton(&one(
        "When the monitor ensures that the token is valid, the daemon shall proceed.",
    ))
    .unwrap();
    let clause = &k.guards.trigger.as_ref().unwrap().clauses[0];
    let content = clause.content.as_ref().unwrap();
    assert_eq!(content.full, "the token is valid");
    assert_eq!(content.clause.subject_head, "token");
    assert_eq!(content.clause.words, vec!["valid"]);
    // Serde: the content key appears only when present; old digests load.
    let json = serde_json::to_value(clause).unwrap();
    assert!(json.get("content").is_some());
    let old: ClauseSkeleton = serde_json::from_value(serde_json::json!({
        "subject_head": "token", "polarity": null, "words": ["valid"],
        "manner": [], "roles": []
    }))
    .unwrap();
    assert!(old.content.is_none());
    // Old ClauseBody JSON (no content field) loads too.
    let old: ClauseBody = serde_json::from_value(serde_json::json!({
        "kind": "verbal", "verb": "expires", "particle": null, "manner": [],
        "object": null, "roles": []
    }))
    .unwrap();
    assert!(matches!(old, ClauseBody::Verbal { content: None, .. }));
}

#[test]
fn guard_content_nests_and_respects_the_depth_bound() {
    roundtrip(
        "When the monitor ensures that the checker confirms that the token is valid, \
         the daemon shall proceed.",
    );
    // The shared budget: 63 nested contents parse, 64 are too deep.
    let ok = format!(
        "When {}the token is valid, the pump shall run.",
        "the monitor ensures that ".repeat(63)
    );
    assert!(parse(&ok).is_ok(), "63 levels must stay within the budget");
    let too_deep = format!(
        "When {}the token is valid, the pump shall run.",
        "the monitor ensures that ".repeat(64)
    );
    assert_eq!(err(&too_deep).kind(), "phrase_too_deep");
}

#[test]
fn content_in_exception_and_until_positions() {
    // Exception clause.
    let s = one("The daemon shall proceed, unless the monitor reports that the token is stale.");
    match &s.exception.as_ref().unwrap().body {
        ClauseBody::Verbal { verb, content, .. } => {
            assert_eq!(verb, "reports");
            assert!(content.is_some());
        }
        other => panic!("expected verbal exception with content, got {other:?}"),
    }
    roundtrip("The daemon shall proceed, unless the monitor reports that the token is stale.");
    // `until` role clause.
    let s = one("The pump shall run until the monitor confirms that the tank is full.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!()
    };
    match &vp.single().unwrap().roles[0] {
        RolePp::Until(clause) => match &clause.body {
            ClauseBody::Verbal { content, .. } => assert!(content.is_some()),
            other => panic!("expected verbal until-clause with content, got {other:?}"),
        },
        other => panic!("expected until role, got {other:?}"),
    }
    roundtrip("The pump shall run until the monitor confirms that the tank is full.");
}

#[test]
fn guard_content_is_final_and_consumes_the_tail() {
    // A deadline written after the content belongs to the INNER clause.
    let k = skeleton(&one(
        "When the monitor ensures that the token is valid within 5 seconds, \
         the pump shall run.",
    ))
    .unwrap();
    let clause = &k.guards.trigger.as_ref().unwrap().clauses[0];
    assert!(
        clause.roles.is_empty(),
        "the outer verbal body has no roles"
    );
    assert_eq!(
        clause.content.as_ref().unwrap().full,
        "the token is valid within 5 seconds"
    );
    roundtrip(
        "When the monitor ensures that the token is valid within 5 seconds, the pump shall run.",
    );
}

#[test]
fn guard_content_gates_relate_judgments() {
    // Same content: one guard region, claims conflict — hard contradiction.
    assert_eq!(
        assess(
            &one("When the monitor ensures that the token is valid, the pump shall run."),
            &one("When the monitor ensures that the token is valid, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // Differing content: the guards no longer witness one region.
    assert_eq!(
        assess(
            &one("When the monitor ensures that the token is valid, the pump shall run."),
            &one("When the monitor ensures that the badge is valid, the pump shall not run."),
        ),
        Outcome::Unknown
    );
    // Verb-phrase content lossiness (round 7, still gated): differing
    // content blocks Yes in both core judgments.
    let a = claim_formula(&one("The daemon shall ensure that the token is valid.")).unwrap();
    let b = claim_formula(&one("The daemon shall ensure that the badge is valid.")).unwrap();
    assert_eq!(implies(&a, &b), Ternary::Unknown);
    assert_eq!(contradicts(&a, &b), Ternary::Unknown);
}

#[test]
fn content_that_after_an_object_noun_stays_relative_territory() {
    // Directly after a noun, `that` belongs to the noun (here: an
    // object-gap relative), never to the clause verb as content.
    let s = one("When the daemon logs the event that the monitor records, the alarm shall sound.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal {
            verb,
            object,
            content,
            ..
        } => {
            assert_eq!(verb, "logs");
            assert!(content.is_none());
            let NpGroup::Single(np) = object.as_ref().unwrap() else {
                panic!()
            };
            assert!(matches!(
                np.relative.as_ref().unwrap().body,
                RelativeBody::ObjectGap { .. }
            ));
        }
        other => panic!("expected verbal body, got {other:?}"),
    }
    // Where the relative reading cannot parse either, the sentence is
    // REJECTED rather than reread as content (legislated; the diagnosis is
    // the relative path's).
    assert_eq!(
        err("When the monitor tells the operator that the tank is full, the daemon shall proceed."),
        ParseError::DeterminerAsVerb { word: "the".into() }
    );
}

#[test]
fn relative_verbal_arms_stay_content_free() {
    // `that ensures that …` inside a relative: the relative's verbal arm
    // carries no content slot in v0.2, so the second `that` is stray.
    assert_eq!(
        err("Each daemon that ensures that the token is valid shall run."),
        ParseError::UnexpectedTokens {
            token: "that".into()
        }
    );
}

// ====================================================================================
// 5. Guard canonicalization + the interval overlap witness
// ====================================================================================

#[test]
fn reordered_conjuncts_ground_contradictions_within_matching_roles() {
    // Commutative canonicalization still grounds when each clause keeps
    // its own frame family across the two sentences (frame ORDER is fixed
    // by the grammar — Where before While — so the reorder happens within
    // one family).
    assert_eq!(
        assess(
            &one("Where the mode is active, Where the depth is at most 5, the pump shall run."),
            &one("Where the depth is at most 5, Where the mode is active, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // SUPERSEDED (round 10, change 4): SWAPPING the families — `Where A,
    // While B` against `Where B, While A` — no longer witnesses one
    // region: the guard atom carries its GuardRole, so Scope(A)∧State(B)
    // and Scope(B)∧State(A) are different conditions (a scope is not a
    // temporal state), and the engine answers Unknown, conservatively.
    assert_eq!(
        assess(
            &one("Where the mode is active, While the depth is at most 5, the pump shall run."),
            &one("Where the depth is at most 5, While the mode is active, the pump shall not run."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn reordered_or_group_guards_ground_contradictions() {
    assert_eq!(
        assess(
            &one("When the pump starts or the valve opens, the fan shall run."),
            &one("When the valve opens or the pump starts, the fan shall not run."),
        ),
        Outcome::HardContradiction
    );
}

#[test]
fn duplicate_conjuncts_collapse_via_idempotence() {
    assert_eq!(
        assess(
            &one("Where the mode is active and the mode is active, the pump shall run."),
            &one("Where the mode is active, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // SUPERSEDED (round 10, change 4): duplicates ACROSS frame families no
    // longer collapse — the family is part of guard identity now
    // (GuardRole), so Scope(X) ∧ State(X) is not idempotence over one atom
    // and does not equal the lone Scope(X): Unknown, conservatively.
    assert_eq!(
        assess(
            &one("Where the mode is active, While the mode is active, the pump shall run."),
            &one("Where the mode is active, the pump shall not run."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn overlapping_bounded_guards_witness_and_disjoint_refuse() {
    // Contained upper bounds: intersection (-∞, 3] is nonempty.
    assert_eq!(
        assess(
            &one("While the depth is at most 5, the pump shall run."),
            &one("While the depth is at most 3, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // Overlapping between-intervals: [5, 9].
    assert_eq!(
        assess(
            &one("While the depth is between 2 and 9, the pump shall run."),
            &one("While the depth is between 5 and 20, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // Same written unit still grounds.
    assert_eq!(
        assess(
            &one("While the depth is at most 5 meters, the pump shall run."),
            &one("While the depth is at most 3 meters, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // Disjoint intervals refuse: no shared region, honest Unknown.
    assert_eq!(
        assess(
            &one("While the depth is at most 3, the pump shall run."),
            &one("While the depth is at least 5, the pump shall not run."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn boundary_touching_intervals_pin_the_legislated_answers() {
    // LEGISLATED (pinned by this suite): `at most 3` and `at least 3`
    // intersect in the single point 3 — both bounds CLOSED — and the
    // witness FIRES: the point itself satisfies both written guards, so
    // the shared region is constructively nonempty even though it has no
    // interior. (The code comment's "interior point" rationale is
    // imprecise here; the verdict is still sound.)
    assert_eq!(
        assess(
            &one("While the depth is at most 3, the pump shall run."),
            &one("While the depth is at least 3, the pump shall not run."),
        ),
        Outcome::HardContradiction
    );
    // An OPEN bound touching a closed one shares no point: refuses.
    assert_eq!(
        assess(
            &one("While the depth is less than 3, the pump shall run."),
            &one("While the depth is at least 3, the pump shall not run."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn witness_refusals_mixed_shapes_units_subjects() {
    // Mixed shapes: a lone comparison guard vs an And-guard — Unknown.
    assert_eq!(
        assess(
            &one("While the depth is at most 5, the pump shall run."),
            &one("While the depth is at most 3 and the mode is active, the pump shall not run."),
        ),
        Outcome::Unknown
    );
    // Unit mismatch never grounds.
    assert_eq!(
        assess(
            &one("While the depth is at most 5 meters, the pump shall run."),
            &one("While the depth is at most 3 seconds, the pump shall not run."),
        ),
        Outcome::Unknown
    );
    // Different subjects never ground.
    assert_eq!(
        assess(
            &one("While the depth is at most 5, the pump shall run."),
            &one("While the width is at most 3, the pump shall not run."),
        ),
        Outcome::Unknown
    );
    // Different copulas (`is` vs `remains`) keep distinct anchors: refuse.
    assert_eq!(
        assess(
            &one("While the depth is at most 5, the pump shall run."),
            &one("While the depth remains at most 3, the pump shall not run."),
        ),
        Outcome::Unknown
    );
    // A noun-phrase bound cannot ground an interval: refuse.
    assert_eq!(
        assess(
            &one("While the depth is at most the limit, the pump shall run."),
            &one("While the depth is at most 3, the pump shall not run."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn interval_witness_no_longer_crosses_frame_families() {
    // SUPERSEDED (round 10, change 4 — the round-9 pin let the interval
    // witness cross When/While): the overlap witness requires matching
    // GuardRoles, so a trigger-instant interval never witnesses against a
    // While-span interval even where the numeric intersection is nonempty
    // — Unknown, conservatively. Same-family interval witnessing is
    // unchanged (see `overlapping_bounded_guards_witness_and_disjoint_refuse`).
    assert_eq!(
        assess(
            &one("When the depth is at most 5, the pump shall run."),
            &one("While the depth is at most 3, the pump shall not run."),
        ),
        Outcome::Unknown
    );
}

#[test]
fn interval_witness_extends_to_envelope_conflicts() {
    assert_eq!(
        assess(
            &one("While the depth is at most 5, the client may retry."),
            &one("While the depth is at most 3, the client shall not retry."),
        ),
        Outcome::EnvelopeConflict
    );
}

// ====================================================================================
// 6. Descending between
// ====================================================================================

#[test]
fn descending_between_is_rejected_with_the_exact_kind() {
    let e = err("The retry count is between 6 and 4.");
    assert_eq!(
        e,
        ParseError::DescendingBetween {
            lower: "6".into(),
            upper: "4".into()
        }
    );
    assert_eq!(e.kind(), "descending_between");
}

#[test]
fn descending_between_covers_every_written_position() {
    // `be`-complement.
    assert_eq!(
        err("The delay shall be between 9 and 2 seconds."),
        ParseError::DescendingBetween {
            lower: "9".into(),
            upper: "2".into()
        }
    );
    // Guard clause.
    assert_eq!(
        err("While the depth is between 9 and 2, the pump shall stop."),
        ParseError::DescendingBetween {
            lower: "9".into(),
            upper: "2".into()
        }
    );
    // Bounded `for` measure.
    assert_eq!(
        err("The daemon shall retain the log for between 10 and 5 days."),
        ParseError::DescendingBetween {
            lower: "10".into(),
            upper: "5".into()
        }
    );
}

#[test]
fn descending_between_reads_numbers_not_lexemes() {
    // Decimals: 5.5 > 5.25 numerically (lexicographically it is not).
    assert_eq!(
        err("The delay is between 5.5 and 5.25 seconds."),
        ParseError::DescendingBetween {
            lower: "5.5".into(),
            upper: "5.25".into()
        }
    );
    // Number words: ten > two (lexicographically "ten" < "two").
    assert_eq!(
        err("The delay is between ten and two seconds."),
        ParseError::DescendingBetween {
            lower: "ten".into(),
            upper: "two".into()
        }
    );
    // Mixed word/numeral bounds still ground.
    assert_eq!(
        err("The delay is between six and 4 seconds."),
        ParseError::DescendingBetween {
            lower: "six".into(),
            upper: "4".into()
        }
    );
    // A unit on the lower bound only does not hide the check.
    assert_eq!(
        err("The delay is between 6 seconds and 4."),
        ParseError::DescendingBetween {
            lower: "6".into(),
            upper: "4".into()
        }
    );
}

#[test]
fn equal_and_np_bounds_pass_through() {
    // Equal bounds are a point interval — accepted, and the point behaves
    // as one downstream.
    roundtrip("The retry count is between 4 and 4.");
    assert_eq!(
        assess(
            &one("The retry count is between 4 and 4."),
            &one("The retry count is at least 5."),
        ),
        Outcome::DescriptiveConflict
    );
    // Noun-phrase bounds are value names: unchecked, accepted.
    roundtrip("The retry count is between the floor and the ceiling.");
    roundtrip("The delay is between the floor and 4 seconds.");
    // Ascending forms keep working, comparisons included.
    roundtrip("The daemon shall retain the log for between 5 and 10 days.");
    assert_eq!(
        assess(
            &one("The retry count is between 4 and 6."),
            &one("The retry count is at least 7."),
        ),
        Outcome::DescriptiveConflict
    );
}

// ====================================================================================
// serde round-trips of round-9 trees
// ====================================================================================

#[test]
fn round9_trees_survive_serde() {
    // Every round-9 shape EXCEPT noun-phrase measures (see the finding
    // below): object gaps, guard content, locative roles, bounded `for`,
    // point `between`.
    for input in [
        "Each request that the gateway forwards shall be logged.",
        "Each user who the auditor flags shall be reviewed.",
        "Each ticket that the operator closes out promptly shall be archived.",
        "When the monitor ensures that the token is valid, the daemon shall proceed.",
        "The daemon shall proceed, unless the monitor reports that the token is stale.",
        "The pump shall run until the monitor confirms that the tank is full.",
        "The crane shall move the beam under the platform.",
        "While the pump runs in the bay, the fan shall spin.",
        "The daemon shall retain the log for between 5 and 10 days.",
        "The retry count is between 4 and 4.",
    ] {
        let s = one(input);
        let json = serde_json::to_string(&s).unwrap();
        let back: Sentence = serde_json::from_str(&json).unwrap();
        assert_eq!(back, s, "serde round-trip must hold for {input:?}");
    }
}

/// FINDING (major, pre-existing, caught by this fuzz, FIXED): a
/// noun-phrase measure — `between the floor and the ceiling`, `within
/// the limit`, `at most the limit` — serialized with a DUPLICATE `kind`
/// field: [`Measure::Np`] was an internally-tagged NEWTYPE variant whose
/// payload ([`NpGroup`]) is itself internally tagged by `kind`, so the
/// outer and inner tags collided in one JSON object — a document
/// `serde_json` wrote without complaint and refused to read back. The
/// fix makes it a struct variant on the wire: `{ "kind": "np", "np": … }`
/// (no migration: the old shape was unreadable, so nothing valid
/// persisted).
#[test]
fn finding_np_measure_trees_must_survive_serde() {
    for input in [
        "The retry count is between the floor and the ceiling.",
        "While the depth is at most the limit, the pump shall run.",
        "The daemon shall persist the record within the limit.",
    ] {
        let s = one(input);
        let json = serde_json::to_string(&s).unwrap();
        let back: Sentence = serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("{input:?} did not round-trip: {e}"));
        assert_eq!(back, s);
    }
}

// ====================================================================================
// 7. Totality: seeded fuzz over the round-9 surface
// ====================================================================================

struct XorShift(u64);

impl XorShift {
    fn new(seed: u64) -> Self {
        XorShift(if seed == 0 {
            0x9E37_79B9_7F4A_7C15
        } else {
            seed
        })
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        items[(self.next() % items.len() as u64) as usize]
    }

    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next() % (hi - lo) as u64) as usize
    }
}

/// Parse must never panic; an accepted parse must render to a fixpoint that
/// re-parses to the same tree, survive serde, and feed every derived view
/// without panicking.
fn assault(input: &str) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        if let Ok(spec) = parse(input) {
            for s in &spec.sentences {
                let rendered = s.render();
                let re = parse(&rendered).unwrap_or_else(|e| {
                    panic!("canonical render must re-parse: {rendered:?} -> {e:?} (from {input:?})")
                });
                assert_eq!(
                    re.sentences[0].render(),
                    rendered,
                    "render must be a fixpoint for {input:?}"
                );
                // Derived views are total over accepted trees. (The tree
                // serde round-trip lives in its own test: NP measures hit
                // the duplicate-`kind` finding below, so asserting it here
                // would fail the whole fuzz on a known defect.)
                let _ = skeleton(s);
                let _ = claim_formula(s);
                let _ = contract_formula(s);
                let _ = subject_keys(s);
            }
        }
    }));
    assert!(outcome.is_ok(), "panicked on {input:?}");
}

#[test]
fn fuzz_word_soup_over_round9_vocabulary() {
    let vocab: &[&str] = &[
        "the", "each", "no", "a", "at", "least", "most", "exactly", "between", "and", "or", "that",
        "who", "shall", "is", "are", "not", "be", "ensures", "forwards", "gateway", "request",
        "monitor", "token", "valid", "in", "on", "under", "above", "below", "within", "for", "per",
        "until", "before", "after", "unless", "When", "While", "Where", "If", "then", "3", "5",
        "6", "4.5", "ten", "two", "seconds", "days", "out", "promptly", "remains", "means", "may",
        ",", ".",
    ];
    let mut rng = XorShift::new(0x5EC0_9A7C_1E11_0009);
    for _ in 0..1500 {
        let n = rng.range(3, 17);
        let mut words: Vec<&str> = Vec::with_capacity(n + 1);
        for _ in 0..n {
            words.push(rng.pick(vocab));
        }
        words.push(".");
        assault(&words.join(" "));
    }
}

#[test]
fn fuzz_templates_mixing_gaps_content_and_between() {
    let subjects = ["the gateway", "the proxy", "no relay", "each node"];
    let verbs = ["forwards", "drops", "records", "ensures"];
    let heads = ["request", "packet", "event"];
    let preps = ["in", "on", "under", "above"];
    let bounds = [
        "between 2 and 9",
        "between 9 and 2",
        "between four and four",
        "between ten and two",
        "at most 5",
        "at least 3",
        "between the floor and the ceiling",
    ];
    let mut rng = XorShift::new(0xA77A_C4B0_0009_0902);
    for _ in 0..400 {
        let s = rng.pick(&subjects);
        let v = rng.pick(&verbs);
        let h = rng.pick(&heads);
        let p = rng.pick(&preps);
        let b = rng.pick(&bounds);
        let template = rng.next() % 6;
        let input = match template {
            0 => format!("Each {h} that {s} {v} shall be logged."),
            1 => format!("When {s} {v} that the {h} is valid, the pump shall run."),
            2 => format!("While the depth is {b}, the daemon shall store the {h} {p} the vault."),
            3 => format!(
                "Each {h} that {s} {v} {p} the vault shall be logged, unless {s} {v} that the {h} is stale."
            ),
            4 => format!("The retry count is {b}."),
            5 => format!(
                "When the monitor ensures that {s} {v} the {h} {b} seconds, the pump shall run."
            ),
            _ => unreachable!(),
        };
        assault(&input);
    }
    // Bounded nesting of the round-9 recursive shapes (the deep form is
    // pinned in `finding_nested_object_gaps_must_stay_polynomial`).
    for depth in 1..=4 {
        let mut np = String::from("the proxy");
        for i in 0..depth {
            np = format!("the node{i} that {np} monitors");
        }
        assault(&format!("Each request that {np} forwards shall be logged."));
        let guard = "the monitor ensures that ".repeat(depth) + "the token is valid";
        assault(&format!("When {guard}, the pump shall run."));
    }
}
