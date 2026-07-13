//! Round 12: force-aware directed refinement, the one-call pairing
//! verdict, ambiguous definite references, number-word extension with
//! fail-closed unknowns, better participle stem candidates, and
//! capability guard objects.

use so_lang::ast::Sentence;
use so_lang::parse::parse;
use so_reason::formula::{
    claim_formula, contract_formula, AssumptionSource, EdgeKind, SourceIssue, SourceIssueReason,
    WellFormedness,
};
use so_reason::relate::{assess, refines, Outcome, Ternary};
use so_reason::semantics::{references, AntecedentCandidate, Resolution};

fn one(input: &str) -> Sentence {
    parse(input).unwrap().sentences.remove(0)
}

// =====================================================================
// Change 1 — force-aware directed refinement in assess()
// =====================================================================

/// The motivating hazard: a RECOMMENDED tightening must not be reported
/// as refining a BINDING promise — advice would be promoted into the
/// discharge of a stronger obligation. The containment proof exists at
/// the force-blind level, but assess() answers Unknown in both argument
/// orders (the reverse direction is a loosening, not a refinement).
#[test]
fn should_never_refines_shall_via_assess() {
    let advice = one("The service should respond within 5 seconds.");
    let promise = one("The service shall respond within 10 seconds.");
    assert_eq!(assess(&advice, &promise), Outcome::Unknown);
    assert_eq!(assess(&promise, &advice), Outcome::Unknown);
}

/// The admissible directions of the force preorder: Binding refines
/// Recommended (a promise strengthens advice) and Binding refines a
/// description; Recommended refines Recommended; descriptions refine
/// descriptions.
#[test]
fn force_preorder_admissible_directions() {
    // Binding (tight) refines Recommended (loose).
    let shall = one("The service shall respond within 5 seconds.");
    let should = one("The service should respond within 10 seconds.");
    assert_eq!(
        assess(&shall, &should),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
    assert_eq!(
        assess(&should, &shall),
        Outcome::Refinement {
            concrete_is_a: false
        }
    );
    // Recommended refines Recommended.
    let should_tight = one("The service should respond within 5 seconds.");
    assert_eq!(
        assess(&should_tight, &should),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
    // Binding refines a description.
    let described = one("The retry count is at most 5.");
    let required = one("The retry count shall be at most 3.");
    assert_eq!(
        assess(&required, &described),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
    // A description does NOT refine a binding obligation.
    let described_tight = one("The retry count is at most 3.");
    let required_loose = one("The retry count shall be at most 5.");
    assert_eq!(assess(&described_tight, &required_loose), Outcome::Unknown);
}

/// Description pairs are unchanged: same-force interval containment is
/// still a directed refinement.
#[test]
fn description_refinement_unchanged() {
    let tight = one("The retry count is at most 3.");
    let loose = one("The retry count is at most 5.");
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

/// PIN: the low-level refines() stays force-blind by design — the
/// should-vs-shall containment pair still proves at Yes there; only the
/// graph-facing assess() verdict gates on force.
#[test]
fn low_level_refines_stays_force_blind() {
    let advice = contract_formula(&one("The service should respond within 5 seconds.")).unwrap();
    let promise = contract_formula(&one("The service shall respond within 10 seconds.")).unwrap();
    assert_eq!(refines(&advice, &promise), Ternary::Yes);
}

// =====================================================================
// Change 2 — the one-call pairing verdict
// =====================================================================

/// The aggregate truth table: `all_sources_contract_forming` gates on
/// all four per-source conditions at once, and `source_issues` itemizes
/// every reason per source index.
#[test]
fn aggregate_verdict_truth_table() {
    let target = one("The daemon shall flush the buffer.");
    let source = one("The scheduler is ready.");
    let bare = contract_formula(&target).unwrap();
    // Row 1: no sources — vacuously forming, no issues.
    let w = bare.well_formed();
    assert!(w.all_sources_contract_forming);
    assert!(w.source_issues.is_empty());
    // Row 2: a default-relied source — NotExplicitRelied.
    let default =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    let w = bare.paired(std::slice::from_ref(&default)).well_formed();
    assert!(!w.all_sources_contract_forming);
    assert_eq!(
        w.source_issues,
        vec![SourceIssue {
            index: 0,
            reasons: vec![SourceIssueReason::NotExplicitRelied]
        }]
    );
    // Row 3: explicit but unproven — NotProven.
    let unproven = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&one("The queue is empty.")).unwrap(),
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&unproven)).well_formed();
    assert!(!w.all_sources_contract_forming);
    assert_eq!(
        w.source_issues[0].reasons,
        vec![SourceIssueReason::NotProven]
    );
    // Row 4 (the round-11 display hazard, now caught): explicit + proven
    // + shared responsible-subject keys — the narrow booleans stay true,
    // the aggregate reports false, the reason is itemized.
    let shared_source = one("The daemon is ready.");
    let shared = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &shared_source,
        &target,
        claim_formula(&shared_source).unwrap(),
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&shared)).well_formed();
    assert!(
        w.all_contract_forming_explicit && w.all_proven,
        "the hazard: booleans look fine"
    );
    assert!(!w.all_sources_contract_forming, "the aggregate catches it");
    assert_eq!(
        w.source_issues[0].reasons,
        vec![SourceIssueReason::SharedSubjectKeys]
    );
    // Row 5: a RECOMMENDED source — RecommendedForce (with the explicit,
    // proven reliance).
    let advice = one("The scheduler should warm the cache.");
    let recommended = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &advice,
        &target,
        claim_formula(&advice).unwrap(),
    )
    .unwrap();
    let w = bare
        .paired(std::slice::from_ref(&recommended))
        .well_formed();
    assert!(!w.all_sources_contract_forming);
    assert_eq!(
        w.source_issues[0].reasons,
        vec![SourceIssueReason::RecommendedForce]
    );
    // Row 6: reasons ACCUMULATE — a default-relied recommendation shows
    // both gates at once.
    let lazy_advice =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &advice, &target).unwrap();
    let w = bare
        .paired(std::slice::from_ref(&lazy_advice))
        .well_formed();
    assert_eq!(
        w.source_issues[0].reasons,
        vec![
            SourceIssueReason::NotExplicitRelied,
            SourceIssueReason::RecommendedForce
        ]
    );
    // Row 7: an envelope source — EnvelopeKind recorded (by design, not
    // a defect), and the aggregate stays vacuously true.
    let envelope = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The client may retry."),
        &target,
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&envelope)).well_formed();
    assert!(
        w.all_sources_contract_forming,
        "envelopes never count against the aggregate"
    );
    assert_eq!(
        w.source_issues[0].reasons,
        vec![SourceIssueReason::EnvelopeKind]
    );
    // A healthy explicit pairing: forming, no issues.
    let healthy = AssumptionSource::for_guarantee_with_relied(
        EdgeKind::OccurrenceReliance,
        &source,
        &target,
        claim_formula(&source).unwrap(),
    )
    .unwrap();
    let w = bare.paired(std::slice::from_ref(&healthy)).well_formed();
    assert!(w.all_sources_contract_forming);
    assert!(w.source_issues.is_empty());
}

// =====================================================================
// Change 3 — definite references can be Ambiguous again
// =====================================================================

/// The motivating trio: two same-head introductions with differing full
/// identities make a bare definite AMBIGUOUS, while a modifier-carrying
/// definite selects its antecedent and resolves Unique.
#[test]
fn differing_fulls_make_a_bare_definite_ambiguous() {
    let spec = parse(
        "A user session shall expire. \
         An admin session shall expire. \
         The session shall expire.",
    )
    .unwrap();
    let refs = references(&spec);
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].head, "session");
    assert_eq!(
        refs[0].resolution,
        Resolution::Ambiguous {
            candidates: vec![
                AntecedentCandidate {
                    sentence: 0,
                    full: "user session".into()
                },
                AntecedentCandidate {
                    sentence: 1,
                    full: "admin session".into()
                },
            ]
        }
    );
}

/// A reference whose modifiers select exactly one candidate full is
/// Unique to that introduction; modifiers matching NO candidate leave
/// the choice open — Ambiguous over all candidates (legislated).
#[test]
fn modifiers_select_or_leave_ambiguous() {
    let spec = parse(
        "A user session shall expire. \
         An admin session shall expire. \
         The admin session shall expire.",
    )
    .unwrap();
    let refs = references(&spec);
    assert_eq!(refs.len(), 1);
    assert_eq!(
        refs[0].resolution,
        Resolution::Unique {
            antecedent_sentence: 1
        }
    );
    let spec = parse(
        "A user session shall expire. \
         An admin session shall expire. \
         The stale session shall expire.",
    )
    .unwrap();
    let refs = references(&spec);
    assert!(matches!(
        &refs[0].resolution,
        Resolution::Ambiguous { candidates } if candidates.len() == 2
    ));
}

/// Single-antecedent resolution is unchanged: one introduction of the
/// head resolves Unique — even under a modifier-carrying reference (all
/// candidates share one full, so the full-identity rule decides before
/// modifier selection is consulted).
#[test]
fn single_antecedent_unique_unchanged() {
    let spec = parse(
        "A session means a sequence of requests. \
         When a session expires, the system shall close the session.",
    )
    .unwrap();
    let refs = references(&spec);
    assert_eq!(refs.len(), 2);
    assert_eq!(
        refs[0].resolution,
        Resolution::Unresolved,
        "the system stays deixis"
    );
    assert_eq!(
        refs[1].resolution,
        Resolution::Unique {
            antecedent_sentence: 1
        }
    );
}

/// Cross-sentence ordering: repeated introductions of ONE full identity
/// are the same term — Unique to the most recent, exactly as before.
#[test]
fn same_full_reintroduction_resolves_to_most_recent() {
    let spec = parse(
        "A session shall begin. \
         A session shall end. \
         The session shall expire.",
    )
    .unwrap();
    let refs = references(&spec);
    assert_eq!(
        refs[0].resolution,
        Resolution::Unique {
            antecedent_sentence: 1
        }
    );
}

/// Coordination: coordinated indefinite items introduce per item, so a
/// bare definite over their shared head is ambiguous between them —
/// and the candidate list keeps reading order.
#[test]
fn coordinated_introductions_make_ambiguity() {
    let spec = parse(
        "The system shall start a primary node and a backup node. \
         The node shall restart.",
    )
    .unwrap();
    let refs = references(&spec);
    let node = refs.iter().find(|r| r.head == "node").unwrap();
    assert_eq!(
        node.resolution,
        Resolution::Ambiguous {
            candidates: vec![
                AntecedentCandidate {
                    sentence: 0,
                    full: "primary node".into()
                },
                AntecedentCandidate {
                    sentence: 0,
                    full: "backup node".into()
                },
            ]
        },
        "coordinated object items introduce per item, reading order kept"
    );
}

/// Serde: the restored Ambiguous variant is internally tagged like every
/// Resolution variant, carrying plain-struct candidates.
#[test]
fn ambiguous_resolution_serde_shape() {
    let resolution = Resolution::Ambiguous {
        candidates: vec![AntecedentCandidate {
            sentence: 0,
            full: "user session".into(),
        }],
    };
    let json = serde_json::to_value(&resolution).unwrap();
    assert_eq!(json["kind"], "ambiguous");
    assert_eq!(json["candidates"][0]["sentence"], 0);
    assert_eq!(json["candidates"][0]["full"], "user session");
    let back: Resolution = serde_json::from_value(json).unwrap();
    assert_eq!(back, resolution);
}

// =====================================================================
// Change 4 — number words: extend and fail closed
// =====================================================================

/// The extended table parses as counts in quantifier positions —
/// `eleven` through `twenty`, the tens, `hundred` — with the stored
/// numeric value (quantifiers render digits, as always).
#[test]
fn extended_number_words_parse_as_counts() {
    use so_reason::semantics::{skeleton, CountOp, Quantifier};
    for (word, n) in [
        ("eleven", 11),
        ("twelve", 12),
        ("thirteen", 13),
        ("fourteen", 14),
        ("fifteen", 15),
        ("sixteen", 16),
        ("seventeen", 17),
        ("eighteen", 18),
        ("nineteen", 19),
        ("twenty", 20),
        ("thirty", 30),
        ("forty", 40),
        ("fifty", 50),
        ("sixty", 60),
        ("seventy", 70),
        ("eighty", 80),
        ("ninety", 90),
        ("hundred", 100),
    ] {
        let s = one(&format!("At least {word} nodes shall run."));
        let k = skeleton(&s).unwrap();
        assert_eq!(
            k.subject.quantifier,
            Quantifier::Count {
                op: CountOp::AtLeast,
                n
            },
            "{word}"
        );
    }
    // Digits are unchanged.
    let k = skeleton(&one("At least 11 nodes shall run.")).unwrap();
    assert_eq!(
        k.subject.quantifier,
        Quantifier::Count {
            op: CountOp::AtLeast,
            n: 11
        }
    );
}

/// An unknown number word after a quantifier opener fails CLOSED —
/// `unknown_number_word`, with the write-digits rewrite — instead of
/// silently degrading the quantifier into open-class modifiers. Compounds
/// are documented out and land in the same error.
#[test]
fn unknown_number_words_reject_in_quantifier_position() {
    use so_lang::parse::ParseError;
    for text in [
        "At least eleventy nodes shall run.",
        "At most eleventy nodes shall run.",
        "Exactly eleventy nodes shall run.",
        "The pool shall keep at least eleventy nodes.",
        "At least twenty-one nodes shall run.",
    ] {
        let err = parse(text).unwrap_err();
        assert!(
            matches!(&err, ParseError::UnknownNumberWord { .. }),
            "{text}: {err:?}"
        );
        assert_eq!(err.kind(), "unknown_number_word");
        assert!(
            err.to_string().contains("digits"),
            "the rewrite hint names digits"
        );
    }
    // A determiner-led phrase after the opener is NOT a number position
    // gone wrong (legislated carve-out): it keeps its existing reading.
    assert!(parse("The daemon shall retain the log for at least the limit.").is_err());
    use so_lang::parse::ParseError as PE;
    assert!(matches!(
        parse("The daemon shall retain the log for at least the limit.").unwrap_err(),
        PE::ForRequiresMeasure
    ));
}

/// Measure positions fail closed the same way: an unknown number word
/// after `within`, or after a bound opener under `for`, is rejected
/// rather than swallowed as a noun-phrase measure that never grounds.
#[test]
fn unknown_number_words_reject_in_measure_positions() {
    use so_lang::parse::ParseError;
    for text in [
        "The daemon shall flush the buffer within eleventy seconds.",
        "The daemon shall retain the log for at least eleventy days.",
        "The daemon shall retain the log for between eleventy and 10 days.",
    ] {
        assert!(
            matches!(
                parse(text).unwrap_err(),
                ParseError::UnknownNumberWord { .. }
            ),
            "{text}"
        );
    }
    // Determiner-led deadline measures keep their noun-phrase reading.
    assert!(parse("The daemon shall flush the buffer within the timeout.").is_ok());
    // Digits and known words are unchanged.
    assert!(parse("The daemon shall flush the buffer within 11 seconds.").is_ok());
    assert!(parse("The daemon shall retain the log for at least thirty days.").is_ok());
}

/// Render round-trips: a measure keeps its number word AS WRITTEN in the
/// canonical render, and the extended words ground intervals — `within
/// eleven seconds` refines `within twelve seconds`.
#[test]
fn extended_measure_words_round_trip_and_ground() {
    let s = one("The daemon shall flush the buffer within eleven seconds.");
    let rendered = s.render();
    assert!(
        rendered.contains("eleven"),
        "canonical keeps the word as written: {rendered}"
    );
    assert_eq!(
        one(&rendered).render(),
        rendered,
        "canonical render is a fixed point"
    );
    let loose = one("The daemon shall flush the buffer within twelve seconds.");
    assert_eq!(
        assess(&s, &loose),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
}

// =====================================================================
// Change 5 — better participle stem candidates (proposal-only)
// =====================================================================

/// The round-12 candidate ordering: irregular-map hit first, then the
/// double-consonant undoubled strip, then the round-11 strips, then the
/// participle itself; duplicates drop.
#[test]
fn participle_stem_ordering_round12() {
    let stems = |text: &str| -> Vec<String> {
        so_reason::semantics::normalization_candidates(&one(text))
            .into_iter()
            .map(|c| c.atom.words[0].clone())
            .collect()
    };
    // Map miss with a doubled consonant: the undoubled strip leads.
    assert_eq!(
        stems("Each request shall be logged by the daemon."),
        vec!["log", "logg", "logge", "logged"]
    );
    assert_eq!(
        stems("The pump is stopped by the daemon."),
        vec!["stop", "stopp", "stoppe", "stopped"]
    );
    // Irregular map hits.
    assert_eq!(
        stems("The report shall be sent by the daemon."),
        vec!["send", "sent"]
    );
    assert_eq!(
        stems("The lock is held by the daemon."),
        vec!["hold", "hel", "held"]
    );
    // A map hit AND a doubled consonant: both candidates ride, map first.
    assert_eq!(
        stems("The report is written by the daemon."),
        vec!["write", "writ", "writt", "writte", "written"]
    );
    // A map hit that equals a strip dedupes (take).
    assert_eq!(
        stems("The record is taken by the daemon."),
        vec!["take", "tak", "taken"]
    );
    // A self-mapping irregular dedupes with the participle; the crude
    // d-strip still rides (all plausible stems are emitted).
    assert_eq!(
        stems("The file is read by the daemon."),
        vec!["read", "rea"]
    );
    // No doubled consonant, no map hit: the round-11 strips then the
    // participle.
    assert_eq!(
        stems("The record is used by the daemon."),
        vec!["us", "use", "used"]
    );
}

// =====================================================================
// Change 6 — capability guard objects
// =====================================================================

/// Capability clause bodies populate the skeleton's objects from the
/// capability verb phrase's object group: the hold-the-lock vs
/// hold-the-token guards differ in the index now.
#[test]
fn capability_guard_objects_digest() {
    use so_reason::semantics::{skeleton, Quantifier};
    let a = one("While the client is able to hold the lock, the gateway shall throttle the queue.");
    let b =
        one("While the client is able to hold the token, the gateway shall throttle the queue.");
    let ga = skeleton(&a).unwrap().guards.states.remove(0);
    let gb = skeleton(&b).unwrap().guards.states.remove(0);
    assert_ne!(ga, gb);
    assert_eq!(ga.objects.len(), 1);
    assert_eq!(ga.objects[0].head, "lock");
    assert_eq!(ga.objects[0].quantifier, Quantifier::Definite);
    assert_eq!(gb.objects[0].head, "token");
    // The rest of the digest is shared — the difference is the object.
    assert_eq!(ga.words, gb.words);
    assert_eq!(ga.subject_head, gb.subject_head);
}

/// A plain copular guard body remains object-free: a predicate has no
/// object.
#[test]
fn copular_guard_objects_stay_empty() {
    use so_reason::semantics::skeleton;
    let s = one("While the pump is active, the gateway shall throttle the queue.");
    let g = skeleton(&s).unwrap().guards.states.remove(0);
    assert!(g.objects.is_empty());
    // An object-free capability body is empty too.
    let s = one("While the client is able to retry, the gateway shall throttle the queue.");
    let g = skeleton(&s).unwrap().guards.states.remove(0);
    assert!(g.objects.is_empty());
}

/// Serde: the new fields ride on the wire (snake_case reasons; empty
/// issues skipped), and a pre-round-12 summary without them loads with
/// the conservative defaults (`false`, empty).
#[test]
fn well_formedness_serde_round_trip_and_legacy() {
    let target = one("The daemon shall flush the buffer.");
    let advice = one("The scheduler should warm the cache.");
    let lazy =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &advice, &target).unwrap();
    let w = contract_formula(&target)
        .unwrap()
        .paired(std::slice::from_ref(&lazy))
        .well_formed();
    let json = serde_json::to_value(&w).unwrap();
    assert_eq!(
        json["all_sources_contract_forming"],
        serde_json::json!(false)
    );
    assert_eq!(json["source_issues"][0]["index"], serde_json::json!(0));
    assert_eq!(
        json["source_issues"][0]["reasons"],
        serde_json::json!(["not_explicit_relied", "recommended_force"])
    );
    let back: WellFormedness = serde_json::from_value(json.clone()).unwrap();
    assert_eq!(back, w);
    // Empty issues are skipped on the wire.
    let clean = contract_formula(&target).unwrap().well_formed();
    let json_clean = serde_json::to_value(&clean).unwrap();
    assert!(json_clean.get("source_issues").is_none());
    // Legacy JSON: the round-12 fields absent load conservatively.
    let mut legacy = json;
    legacy
        .as_object_mut()
        .unwrap()
        .remove("all_sources_contract_forming");
    legacy.as_object_mut().unwrap().remove("source_issues");
    let back: WellFormedness = serde_json::from_value(legacy).unwrap();
    assert!(
        !back.all_sources_contract_forming,
        "absent loads as false — conservative"
    );
    assert!(back.source_issues.is_empty());
}
