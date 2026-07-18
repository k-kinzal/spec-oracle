//! Adversarial conformance attack on the round-2 changes (IMPROVE-SPEC-2).
//!
//! Object under test: the code in `so_lang/src` after round 2 —
//!
//! 1. subject-level `no` enters the denotation; `no` + `may` is rejected
//!    (`ParseError::NoWithMay`, kind `no_with_may`);
//! 2. skeleton enrichment: `Atom::objects`, `Atom::roles` (one digest per
//!    `RolePp` kind), `Skeleton::guards`, `Skeleton::exception`;
//! 3. trigger conjuncts: at most one event (verbal) clause per `and` group
//!    under `When`/`If` (`ParseError::MultipleEventConjuncts`, kind
//!    `multiple_event_conjuncts`); `or` groups exempt; `While`/`Where`
//!    unrestricted;
//! 4. totality over the new constructs.
//!
//! Every test pins behavior the round-2 spec legislates, or probes an edge
//! the spec left to the implementation (those pins say so). Tests that fail
//! are marked `#[ignore]` with the finding title.

use so_lang::ast::*;
use so_lang::parse::{parse, ParseError};
use so_reason::semantics::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

// ---- helpers ----------------------------------------------------------------------

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("expected {input:?} to parse, got {e}"));
    assert_eq!(
        spec.sentences.len(),
        1,
        "expected one sentence in {input:?}"
    );
    spec.sentences.into_iter().next().unwrap()
}

fn sk(input: &str) -> Skeleton {
    skeleton(&one(input)).unwrap_or_else(|| panic!("expected a skeleton for {input:?}"))
}

/// The combined claim polarity of a behavioral sentence's denotation.
fn claim_polarity(sentence: &Sentence) -> Polarity {
    match denote(sentence) {
        Denotation::Behavior(a) | Denotation::Admissibility(a) => match a.claim {
            Claim::State { polarity, .. } | Claim::Action { polarity, .. } => polarity,
            Claim::Admissible { .. } | Claim::Capability { .. } => {
                panic!(
                    "claim carries no claim-level polarity site: {:?}",
                    sentence.source
                )
            }
        },
        Denotation::Vocabulary { .. } => panic!("vocabulary has no claim: {:?}", sentence.source),
    }
}

/// A Heads-value role over definite (`the …`) items — the fixtures' common
/// case. Skeleton v3: each item carries its quantifier. Round 6: the fixture
/// string is the FULL identity (modifiers included); the head is its last
/// word.
fn heads_role(kind: RoleKind, hs: &[&str]) -> RoleSkeleton {
    RoleSkeleton {
        kind,
        value: RoleValue::Heads {
            items: objs(hs),
            // The fixtures coordinate role items with `and` only.
            conj: (hs.len() > 1).then_some(Conj::And),
        },
        marker: None,
    }
}

/// Definite (`the …`) object digests — the fixtures' common case. Round 6:
/// the fixture string is the FULL identity; the head is its last word.
fn objs(hs: &[&str]) -> Vec<ObjectSkeleton> {
    hs.iter()
        .map(|s| ObjectSkeleton {
            quantifier: Quantifier::Definite,
            head: s.split_whitespace().last().unwrap().to_string(),
            full: s.to_string(),
        })
        .collect()
}

/// A Location role digest: like [`heads_role`], plus the preposition
/// marker (round 9 — the preposition entered role identity).
fn loc_role(prep: &str, hs: &[&str]) -> RoleSkeleton {
    RoleSkeleton {
        marker: Some(prep.to_string()),
        ..heads_role(RoleKind::Location, hs)
    }
}

/// The Rate role digests its bare unit word with no quantifier.
fn rate_role(unit: &str) -> RoleSkeleton {
    RoleSkeleton {
        kind: RoleKind::Rate,
        value: RoleValue::Heads {
            items: vec![ObjectSkeleton {
                quantifier: Quantifier::None,
                head: unit.to_string(),
                full: unit.to_string(),
            }],
            conj: None,
        },
        marker: None,
    }
}

fn measure_role(kind: RoleKind, number: &str, unit: Option<&str>) -> RoleSkeleton {
    RoleSkeleton {
        kind,
        value: RoleValue::Measure {
            number: number.to_string(),
            unit: unit.map(str::to_string),
        },
        marker: None,
    }
}

// Round 8, change 1 (fixture updated with the pin): clausal role values
// carry the FULL nested clause skeleton plus the full render — the flat
// {subject_head, words} digest let `after no backup completes` equal
// `after the backup completes`.
fn clause_role(kind: RoleKind, subject_head: &str, words: &[&str], full: &str) -> RoleSkeleton {
    RoleSkeleton {
        kind,
        value: RoleValue::Clause {
            skeleton: cs(subject_head, None, words),
            full: full.to_string(),
        },
        marker: None,
    }
}

fn cs(subject_head: &str, polarity: Option<Polarity>, words: &[&str]) -> ClauseSkeleton {
    ClauseSkeleton {
        subject_head: subject_head.to_string(),
        polarity,
        words: words.iter().map(|s| s.to_string()).collect(),
        // Round 4, change 1: verbal digests carry a manner slot; these
        // fixtures digest manner-free clauses.
        manner: Vec::new(),
        // Round 3, change 1: clause bodies carry thematic roles; these
        // fixtures digest role-free clauses.
        roles: Vec::new(),
        // Round 11, change 2: verbal digests carry object digests; these
        // fixtures digest object-free clauses.
        objects: Vec::new(),
        // Round 6, change 5: comparison predicates digest structurally;
        // these fixtures digest non-comparison clauses.
        comparison: None,
        // Round 9, change 4: verbal bodies may carry a content
        // complement; these fixtures digest content-free clauses.
        content: None,
    }
}

// ====================================================================================
// 1. The no-subject rule
// ====================================================================================

#[test]
fn no_with_may_rejected_in_every_deontic_shape() {
    // The canonical form, and casing variants of both `no` and `may` — the
    // closed-class test is case-insensitive.
    assert_eq!(parse("No client may retry."), Err(ParseError::NoWithMay));
    assert_eq!(parse("no client may retry."), Err(ParseError::NoWithMay));
    assert_eq!(parse("NO client MAY retry."), Err(ParseError::NoWithMay));
    assert_eq!(parse("No client May retry."), Err(ParseError::NoWithMay));
    // Coordinated subjects: ANY item determined by `no` triggers it,
    // whichever position it sits in and under either conjunction.
    assert_eq!(
        parse("The client and no server may retry."),
        Err(ParseError::NoWithMay)
    );
    assert_eq!(
        parse("No client and the server may retry."),
        Err(ParseError::NoWithMay)
    );
    assert_eq!(
        parse("The client or no server may retry."),
        Err(ParseError::NoWithMay)
    );
    assert_eq!(
        parse("Either no client or the proxy may retry."),
        Err(ParseError::NoWithMay)
    );
    assert_eq!(
        parse("Both no client and the proxy may retry."),
        Err(ParseError::NoWithMay)
    );
    // A `no` on the HEAD noun phrase of an of-chain is subject-level.
    assert_eq!(
        parse("No owner of the file may retry."),
        Err(ParseError::NoWithMay)
    );
    // `no` + `may not` stacks two legislated ambiguities; the subject rule
    // fires first (the modal is `may` and the subject carries `no`).
    assert_eq!(
        parse("No client may not retry."),
        Err(ParseError::NoWithMay)
    );
    // With a VP that carries objects and roles.
    assert_eq!(
        parse("No exporter may send the payload to the collector within 5 seconds."),
        Err(ParseError::NoWithMay)
    );
    // Under frames the rule is unchanged.
    assert_eq!(
        parse("When the order ships, no client may retry."),
        Err(ParseError::NoWithMay)
    );
}

#[test]
fn no_with_may_error_kind_and_message() {
    assert_eq!(ParseError::NoWithMay.kind(), "no_with_may");
    let message = ParseError::NoWithMay.to_string();
    assert!(
        message.contains("shall not"),
        "message must direct to `shall not`: {message}"
    );
    assert!(
        message.contains("prohibition"),
        "message names the intended act: {message}"
    );
    assert!(
        message.contains("permission"),
        "message names the denied act: {message}"
    );
}

#[test]
fn no_inside_of_chain_is_not_subject_level() {
    // Only the item's own determiner counts: a `no` inside an `of`-chain
    // does not negate the phrase itself, so `may` stands and the sentence
    // is a permission — with NO polarity flip anywhere.
    let s = one("The owner of no file may retry.");
    assert_eq!(speech_act(&s), SpeechAct::Permission);
    assert!(matches!(denote(&s), Denotation::Admissibility(_)));
    let sk = skeleton(&s).expect("permission skeleton");
    assert_eq!(sk.polarity, Polarity::Affirmative);
    assert_eq!(sk.subject.quantifier, Quantifier::Definite);
    // Likewise under shall: the of-chain `no` never flips the claim.
    let s = one("The owner of no file shall retry.");
    assert_eq!(claim_polarity(&s), Polarity::Affirmative);
    assert_eq!(skeleton(&s).unwrap().polarity, Polarity::Affirmative);
    // A `no` inside a relative clause is likewise not subject-level.
    let s = one("The client that serves no tenant may retry.");
    assert_eq!(speech_act(&s), SpeechAct::Permission);
    assert_eq!(skeleton(&s).unwrap().polarity, Polarity::Affirmative);
}

#[test]
fn object_position_no_does_not_flip_claim_polarity() {
    // `no` in OBJECT position is not part of the rule: the claim polarity
    // reads the subject only, and the skeleton agrees.
    let s = one("The daemon shall log no request.");
    assert_eq!(speech_act(&s), SpeechAct::Obligation);
    assert_eq!(claim_polarity(&s), Polarity::Affirmative);
    let k = skeleton(&s).unwrap();
    assert_eq!(k.polarity, Polarity::Affirmative);
    // Skeleton v3: the object `no` stays out of claim polarity (settled)
    // but is now visible as the object's quantifier.
    assert_eq!(
        k.atoms[0].objects,
        vec![ObjectSkeleton {
            quantifier: Quantifier::Negative,
            head: "request".into(),
            full: "request".into()
        }]
    );
    // Modal `not` still flips exactly once; the object `no` adds nothing.
    let s = one("The daemon shall not log no request.");
    assert_eq!(claim_polarity(&s), Polarity::Negative);
    assert_eq!(skeleton(&s).unwrap().polarity, Polarity::Negative);
    // Object `no` under `may` does NOT trigger NoWithMay: the rule reads
    // the subject group only.
    let s = one("The client may log no request.");
    assert_eq!(speech_act(&s), SpeechAct::Permission);
    assert_eq!(skeleton(&s).unwrap().polarity, Polarity::Affirmative);
}

#[test]
fn no_subject_with_should_and_must() {
    // `should`: recommendation, negative claim, recommended force.
    let s = one("No client should retry.");
    assert_eq!(speech_act(&s), SpeechAct::Recommendation);
    assert_eq!(force(&s), Some(Force::Recommended));
    assert_eq!(claim_polarity(&s), Polarity::Negative);
    let k = skeleton(&s).unwrap();
    assert_eq!(k.polarity, Polarity::Negative);
    assert_eq!(k.subject.quantifier, Quantifier::Negative);
    assert_eq!(k.force, Some(Force::Recommended));
    // `must`: binding, negative claim. NOTE the act stays Obligation — the
    // classification is read off the pivot alone (modal + `not` flag), so a
    // `no`-subject binding sentence classifies as Obligation even though
    // its denotation is a negative binding action (see report: minor).
    let s = one("No pump must run.");
    assert_eq!(speech_act(&s), SpeechAct::Obligation);
    assert_eq!(force(&s), Some(Force::Binding));
    assert_eq!(claim_polarity(&s), Polarity::Negative);
    assert_eq!(skeleton(&s).unwrap().polarity, Polarity::Negative);
    // `shall` from the round spec: Claim::Action, Negative, skeleton agrees.
    let s = one("No request shall be logged.");
    match denote(&s) {
        Denotation::Behavior(a) => match a.claim {
            Claim::Action {
                polarity: Polarity::Negative,
                force: Force::Binding,
                ..
            } => {}
            other => panic!("expected negative binding action, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    }
    let k = skeleton(&s).unwrap();
    assert_eq!(k.polarity, Polarity::Negative);
    assert_eq!(k.atoms[0].words, vec!["logged"]);
    // The negative obligation still ingests as a contract.
    let contract = ingest_contract(&s).expect("binding sentence ingests");
    assert_eq!(contract.assumption.render(), "⊤");
}

#[test]
fn double_negation_composes_in_claim_and_skeleton() {
    // Modal `not` XOR subject `no` — two flips cancel, in the CLAIM and in
    // the skeleton, through every binding modal and `should`.
    for input in [
        "No request shall not be logged.",
        "No request must not be logged.",
        "No client should not retry.",
    ] {
        let s = one(input);
        assert_eq!(
            claim_polarity(&s),
            Polarity::Affirmative,
            "claim polarity of {input:?}"
        );
        let k = skeleton(&s).unwrap();
        assert_eq!(
            k.polarity,
            Polarity::Affirmative,
            "skeleton polarity of {input:?}"
        );
        assert_eq!(
            k.subject.quantifier,
            Quantifier::Negative,
            "quantifier of {input:?}"
        );
    }
    // Description `never` XOR subject `no` cancels the same way.
    let s = one("No request is never logged.");
    assert_eq!(claim_polarity(&s), Polarity::Affirmative);
    assert_eq!(skeleton(&s).unwrap().polarity, Polarity::Affirmative);
}

#[test]
fn descriptions_compose_never_always_and_no() {
    // One flip: subject `no` alone, with either copula.
    let s = one("No request is logged.");
    assert!(matches!(
        denote(&s),
        Denotation::Behavior(Assertion {
            claim: Claim::State {
                polarity: Polarity::Negative,
                ..
            },
            ..
        })
    ));
    assert_eq!(sk("No requests are logged.").polarity, Polarity::Negative);
    // `always` strengthens but never flips: `no` + `always` stays Negative.
    let s = one("No request is always logged.");
    assert_eq!(claim_polarity(&s), Polarity::Negative);
    let k = skeleton(&s).unwrap();
    assert_eq!(k.polarity, Polarity::Negative);
    // The adverb survives in the AST/claim even though the polarity is combined.
    match denote(&s) {
        Denotation::Behavior(a) => match a.claim {
            Claim::State {
                adverb: Some(DescriptionAdverb::Always),
                ..
            } => {}
            other => panic!("expected retained `always`, got {other:?}"),
        },
        other => panic!("expected behavior, got {other:?}"),
    }
}

#[test]
fn coordinated_subject_no_flips_the_claim_even_without_a_skeleton() {
    // A coordinated subject has no skeleton (no single normal form), but the
    // claim polarity still composes: any item with `no` flips once.
    let s = one("No pump and the valve shall run.");
    assert_eq!(claim_polarity(&s), Polarity::Negative);
    assert!(
        skeleton(&s).is_none(),
        "coordinated subjects have no skeleton in v0.2"
    );
    let s = one("The pump and no valve shall not run.");
    assert_eq!(
        claim_polarity(&s),
        Polarity::Affirmative,
        "two flips cancel"
    );
}

// ====================================================================================
// 2. Skeleton enrichment
// ====================================================================================

#[test]
fn role_skeletons_cover_every_role_kind() {
    // One sentence carrying ten of the eleven role kinds, in surface order.
    let k = sk(
        "The daemon shall send the report and the invoice to the operator and \
                the auditor via the queue about the outage within 5 seconds for two \
                minutes per second from the sensor into the archive in the vault \
                before the session expires.",
    );
    assert_eq!(k.atoms[0].words, vec!["send"]);
    assert_eq!(k.atoms[0].objects, objs(&["report", "invoice"]));
    assert_eq!(
        k.atoms[0].roles,
        vec![
            heads_role(RoleKind::Recipient, &["operator", "auditor"]),
            heads_role(RoleKind::Means, &["queue"]),
            heads_role(RoleKind::Topic, &["outage"]),
            measure_role(RoleKind::Deadline, "5", Some("seconds")),
            measure_role(RoleKind::Duration, "two", Some("minutes")),
            rate_role("second"),
            heads_role(RoleKind::Source, &["sensor"]),
            heads_role(RoleKind::Goal, &["archive"]),
            loc_role("in", &["vault"]),
            clause_role(
                RoleKind::Before,
                "session",
                &["expires"],
                "the session expires"
            ),
        ]
    );
    // The eleventh: `after` (a clausal role, like `before`).
    let k = sk("The daemon shall retry after the payment clears.");
    assert_eq!(
        k.atoms[0].roles,
        vec![clause_role(
            RoleKind::After,
            "payment",
            &["clears"],
            "the payment clears"
        )]
    );
    // `using` collapses to the same Means digest as `via` (the marker is
    // surface detail; the skeleton indexes the role).
    let via = sk("The daemon shall sign the report via the key.");
    let using = sk("The daemon shall sign the report using the key.");
    assert_eq!(
        via.atoms[0].roles,
        vec![heads_role(RoleKind::Means, &["key"])]
    );
    assert_eq!(via.atoms[0].roles, using.atoms[0].roles);
}

#[test]
fn deadline_number_and_unit_fidelity() {
    let deadline = |input: &str| sk(input).atoms[0].roles.clone();
    // Integer + unit, kept as written.
    assert_eq!(
        deadline("The daemon shall respond within 5 seconds."),
        vec![measure_role(RoleKind::Deadline, "5", Some("seconds"))]
    );
    // Decimal numbers survive the tokenizer and stay as written.
    assert_eq!(
        deadline("The daemon shall respond within 5.5 seconds."),
        vec![measure_role(RoleKind::Deadline, "5.5", Some("seconds"))]
    );
    // Number words are NOT normalized to digits.
    assert_eq!(
        deadline("The daemon shall respond within five seconds."),
        vec![measure_role(RoleKind::Deadline, "five", Some("seconds"))]
    );
    // A missing unit is None, not an empty string.
    assert_eq!(
        deadline("The daemon shall respond within 5."),
        vec![measure_role(RoleKind::Deadline, "5", None)]
    );
    assert_eq!(
        deadline("The daemon shall respond within ten."),
        vec![measure_role(RoleKind::Deadline, "ten", None)]
    );
    // A noun-phrase deadline digests as heads under the Deadline kind.
    assert_eq!(
        deadline("The daemon shall respond within the timeout."),
        vec![heads_role(RoleKind::Deadline, &["timeout"])]
    );
    // Unit casing is kept as written (only Heads lowercase).
    assert_eq!(
        deadline("The daemon shall respond within 5 Seconds."),
        vec![measure_role(RoleKind::Deadline, "5", Some("Seconds"))]
    );
    // Duplicate roles keep surface order.
    assert_eq!(
        deadline("The daemon shall respond within 5 seconds within the timeout."),
        vec![
            measure_role(RoleKind::Deadline, "5", Some("seconds")),
            heads_role(RoleKind::Deadline, &["timeout"]),
        ]
    );
}

#[test]
fn deadline_pair_differs_only_in_the_deadline_role() {
    let five = sk("The daemon shall respond within 5 seconds.");
    let ten = sk("The daemon shall respond within 10 seconds.");
    assert_eq!(five.subject, ten.subject);
    assert_eq!(five.polarity, ten.polarity);
    assert_eq!(five.atoms[0].words, ten.atoms[0].words);
    assert_eq!(five.atoms[0].objects, ten.atoms[0].objects);
    assert_eq!(five.force, ten.force);
    assert_eq!(five.act, ten.act);
    assert_eq!(five.guards, ten.guards);
    assert_eq!(five.exception, ten.exception);
    assert_ne!(
        five.atoms[0].roles, ten.atoms[0].roles,
        "the deadline must be visible"
    );
    assert_eq!(
        five.atoms[0].roles,
        vec![measure_role(RoleKind::Deadline, "5", Some("seconds"))]
    );
    assert_eq!(
        ten.atoms[0].roles,
        vec![measure_role(RoleKind::Deadline, "10", Some("seconds"))]
    );
}

#[test]
fn archive_and_public_bucket_no_longer_collide() {
    // The round-2 motivating pair: same verb, same object, different place.
    let archive = sk("The daemon shall store the report in the archive.");
    let bucket = sk("The daemon shall not store the report on the public bucket.");
    assert_eq!(archive.atoms[0].words, vec!["store"]);
    assert_eq!(archive.atoms[0].words, bucket.atoms[0].words);
    assert_eq!(archive.atoms[0].objects, bucket.atoms[0].objects);
    assert_ne!(
        archive.atoms[0].roles, bucket.atoms[0].roles,
        "Location heads must differ"
    );
    assert_eq!(archive.atoms[0].roles, vec![loc_role("in", &["archive"])]);
    assert_eq!(
        bucket.atoms[0].roles,
        vec![loc_role("on", &["public bucket"])]
    );
    assert_eq!(archive.polarity, Polarity::Affirmative);
    assert_eq!(bucket.polarity, Polarity::Negative);
    // SUPERSEDED PIN (round 9, recorded): the round-2 "known residual
    // collision" — the heads-only Location digest that made `in the
    // archive` and `on the archive` share one proposition — is retired:
    // the Location digest now carries its preposition marker, so the two
    // digests differ exactly there.
    let on = sk("The daemon shall store the report on the archive.");
    assert_ne!(
        archive.atoms[0], on.atoms[0],
        "the preposition is role identity now"
    );
    assert_eq!(on.atoms[0].roles, vec![loc_role("on", &["archive"])]);
}

#[test]
fn multi_object_coordination_heads() {
    let k = sk("The daemon shall store the report and the invoice in the archive.");
    assert_eq!(k.atoms[0].objects, objs(&["report", "invoice"]));
    let k = sk("The daemon shall store the report or the invoice in the archive.");
    assert_eq!(k.atoms[0].objects, objs(&["report", "invoice"]));
    // Marked coordination works in ROLE position (and its heads digest).
    let k = sk("The daemon shall send the report to both the operator and the auditor.");
    assert_eq!(k.atoms[0].objects, objs(&["report"]));
    assert_eq!(
        k.atoms[0].roles,
        vec![heads_role(RoleKind::Recipient, &["operator", "auditor"])]
    );
    // Three-way coordination, lowercasing, and modifiers dropped from heads.
    let k = sk("The daemon shall store the Report and the final Invoice and the audit Log.");
    assert_eq!(
        k.atoms[0].objects,
        objs(&["report", "final invoice", "audit log"])
    );
    // State claims have no objects and no roles.
    let k = sk("The report is in the archive.");
    assert_eq!(k.atoms[0].words, vec!["in", "the", "archive"]);
    assert_eq!(k.atoms[0].objects, Vec::<ObjectSkeleton>::new());
    assert_eq!(k.atoms[0].roles, Vec::<RoleSkeleton>::new());
}

/// FIXED (was a major finding): `both …and…` / `either …or…` marked
/// coordination used to be accepted in subject, thematic-role, predicate-PP,
/// and definiens positions but rejected in VP direct-object and clause-object
/// position, because the object gates treated the reserved marker words as
/// ending the phrase. `parse_vp` and the clause determiner scan now admit a
/// group marker as an object opener, so `Atom::objects` sees marked
/// coordinations like unmarked ones.
#[test]
fn marked_object_coordination_should_parse_like_role_position() {
    let k = sk("The daemon shall store both the report and the invoice in the archive.");
    assert_eq!(k.atoms[0].objects, objs(&["report", "invoice"]));
    let k = sk("The daemon shall store either the report or the invoice in the archive.");
    assert_eq!(k.atoms[0].objects, objs(&["report", "invoice"]));
    // Clause-object position has the same hole.
    assert!(
        parse("When the order ships both the report and the invoice, the system shall pack.")
            .is_ok()
    );
}

#[test]
fn object_no_is_visible_as_the_object_quantifier() {
    // SUPERSEDED PIN (round 3, change 3, skeleton v3): object determiners
    // now reach the skeleton as per-object quantifiers, so `log no request`
    // and `log the request` no longer share a skeleton — they differ
    // exactly in the object's quantifier. Object `no` STILL stays out of
    // claim polarity (round 2's subject-only rule is settled).
    let no = sk("The daemon shall log no request.");
    let the = sk("The daemon shall log the request.");
    assert_ne!(no, the);
    assert_eq!(no.polarity, the.polarity);
    assert_eq!(no.atoms[0].words, the.atoms[0].words);
    assert_eq!(
        no.atoms[0].objects,
        vec![ObjectSkeleton {
            quantifier: Quantifier::Negative,
            head: "request".into(),
            full: "request".into()
        }]
    );
    assert_eq!(
        the.atoms[0].objects,
        vec![ObjectSkeleton {
            quantifier: Quantifier::Definite,
            head: "request".into(),
            full: "request".into()
        }]
    );
}

#[test]
fn guards_digest_all_frame_families() {
    let k = sk(
        "Where the Flag is Enabled, Where the mode is strict, While the engine \
                is running, While the queue is empty, When the order ships and the \
                payment is cleared, the system shall pack the crate, unless no \
                operator is present.",
    );
    assert_eq!(
        k.guards.scopes,
        vec![
            cs("flag", None, &["enabled"]),
            cs("mode", None, &["strict"])
        ],
        "scope digests are flattened across Where frames and lowercased"
    );
    assert_eq!(
        k.guards.states,
        vec![
            cs("engine", None, &["running"]),
            cs("queue", None, &["empty"])
        ]
    );
    assert_eq!(
        k.guards.trigger,
        Some(TriggerSkeleton {
            kind: TriggerKind::Event,
            conj: Some(Conj::And),
            clauses: vec![
                cs("order", None, &["ships"]),
                cs("payment", None, &["cleared"])
            ],
        })
    );
    assert_eq!(
        k.exception,
        Some(cs("operator", Some(Polarity::Negative), &["present"])),
        "a `no` subject is the exception clause's negation site"
    );
    // A bare sentence has empty guards and no exception.
    let bare = sk("The pump shall stop.");
    assert_eq!(bare.guards, Guards::default());
    assert_eq!(bare.exception, None);
}

#[test]
fn guard_digests_carry_no_subject_polarity_and_or_groups() {
    // `no` in a Where guard.
    let k = sk("Where no endpoint is configured, the exporter shall stay disabled.");
    assert_eq!(
        k.guards.scopes,
        vec![cs("endpoint", Some(Polarity::Negative), &["configured"])]
    );
    // An `or` trigger group of three verbal clauses digests with its conj.
    let k = sk(
        "When the pump stops or the valve closes or the sensor fails, the \
                system shall alert.",
    );
    assert_eq!(
        k.guards.trigger,
        Some(TriggerSkeleton {
            kind: TriggerKind::Event,
            conj: Some(Conj::Or),
            clauses: vec![
                cs("pump", None, &["stops"]),
                cs("valve", None, &["closes"]),
                cs("sensor", None, &["fails"]),
            ],
        })
    );
    // A single-clause trigger digests with conj None; `If` keeps its kind.
    let k = sk("If the pump stops, then the system shall alert.");
    assert_eq!(
        k.guards.trigger,
        Some(TriggerSkeleton {
            kind: TriggerKind::Contingency,
            conj: None,
            clauses: vec![cs("pump", None, &["stops"])],
        })
    );
    // A coordinated guard SUBJECT stays one clause: heads joined by a space.
    let k = sk("When the pump and the valve are open, the system shall start.");
    assert_eq!(
        k.guards.trigger,
        Some(TriggerSkeleton {
            kind: TriggerKind::Event,
            conj: None,
            clauses: vec![cs("pump valve", None, &["open"])],
        })
    );
    // A verbal guard digest keeps the VERB only — the guard's object is not
    // part of the digest (per spec: words = verb or predicate words).
    let k = sk("When the temperature exceeds the limit, the controller shall open the valve.");
    // Round 11, change 2 (pin updated): the verbal guard digest carries
    // the object digests now — the drop-the-object blind spot is retired.
    assert_eq!(
        k.guards.trigger.unwrap().clauses,
        vec![ClauseSkeleton {
            objects: vec![ObjectSkeleton {
                quantifier: Quantifier::Definite,
                head: "limit".into(),
                full: "limit".into(),
            }],
            ..cs("temperature", None, &["exceeds"])
        }]
    );
}

#[test]
fn exception_digest_verbal_and_copular() {
    let k = sk("The pump shall stop, unless the override is active.");
    assert_eq!(k.exception, Some(cs("override", None, &["active"])));
    // Round 11, change 2 (pin updated): the verbal exception digest
    // carries its object digests.
    let k = sk("The pump shall stop, unless the operator presses the button.");
    assert_eq!(
        k.exception,
        Some(ClauseSkeleton {
            objects: vec![ObjectSkeleton {
                quantifier: Quantifier::Definite,
                head: "button".into(),
                full: "button".into(),
            }],
            ..cs("operator", None, &["presses"])
        })
    );
}

#[test]
fn skeleton_and_claim_polarity_agree_on_a_generated_matrix() {
    // 36 generated sentences: every subject determiner crossed with every
    // claim shape and negation site. The skeleton polarity and the claim's
    // combined polarity must never drift apart.
    let dets: [(&str, bool); 4] = [
        ("The ", false),
        ("No ", true),
        ("Each ", false),
        ("A ", false),
    ];
    let forms: [(&str, bool); 9] = [
        ("request shall be logged.", false),
        ("request shall not be logged.", true),
        ("request must be logged.", false),
        ("request must not be logged.", true),
        ("request should be logged.", false),
        ("request should not be logged.", true),
        ("request is logged.", false),
        ("request is never logged.", true),
        ("request is always logged.", false),
    ];
    let mut checked = 0;
    for (det, subject_flips) in dets {
        for (form, site_flips) in forms {
            let input = format!("{det}{form}");
            let expected = if subject_flips != site_flips {
                Polarity::Negative
            } else {
                Polarity::Affirmative
            };
            let s = one(&input);
            assert_eq!(claim_polarity(&s), expected, "claim polarity of {input:?}");
            let k = skeleton(&s).unwrap_or_else(|| panic!("skeleton for {input:?}"));
            assert_eq!(k.polarity, expected, "skeleton polarity of {input:?}");
            checked += 1;
        }
    }
    assert!(
        checked >= 20,
        "the matrix must cover at least 20 sentences, got {checked}"
    );
}

// ====================================================================================
// 3. Trigger conjunct rule
// ====================================================================================

#[test]
fn and_group_with_two_or_three_verbal_conjuncts_is_rejected() {
    // Two events under `and` — the round-2 headline case.
    assert_eq!(
        parse("When the order ships and the payment clears, the system shall pack."),
        Err(ParseError::MultipleEventConjuncts)
    );
    // Three events.
    assert_eq!(
        parse(
            "When the order ships and the payment clears and the stock arrives, \
               the system shall pack."
        ),
        Err(ParseError::MultipleEventConjuncts)
    );
    // Two events with a state between them: still two events.
    assert_eq!(
        parse(
            "When the order ships and the payment is cleared and the invoice posts, \
               the system shall pack."
        ),
        Err(ParseError::MultipleEventConjuncts)
    );
    // `If` groups obey the same rule as `When`.
    assert_eq!(
        parse("If the order ships and the payment clears, then the system shall halt."),
        Err(ParseError::MultipleEventConjuncts)
    );
    assert_eq!(
        parse("If the order ships and the payment clears, the system shall halt."),
        Err(ParseError::MultipleEventConjuncts)
    );
    // Keyword casing does not matter.
    assert_eq!(
        parse("WHEN the order ships and the payment clears, the system shall pack."),
        Err(ParseError::MultipleEventConjuncts)
    );
    // A verbal conjunct with a numeric object is still an event.
    assert_eq!(
        parse("When the counter reaches zero and the timer expires, the system shall reset."),
        Err(ParseError::MultipleEventConjuncts)
    );
}

#[test]
fn and_group_with_one_verbal_conjunct_is_accepted_in_any_order() {
    // Verbal first.
    let s = one(
        "When the order ships and the payment is cleared, the system shall \
                 issue the receipt.",
    );
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert!(matches!(&group.items[0].body, ClauseBody::Verbal { verb, .. } if verb == "ships"));
    assert!(matches!(&group.items[1].body, ClauseBody::Copular { .. }));
    // Copular first, verbal second: the rule counts, it does not order.
    let s = one(
        "When the payment is cleared and the order ships, the system shall \
                 issue the receipt.",
    );
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert!(matches!(&group.items[0].body, ClauseBody::Copular { .. }));
    assert!(matches!(&group.items[1].body, ClauseBody::Verbal { verb, .. } if verb == "ships"));
    // Verbal in the middle of three.
    let s = one(
        "When the stock is available and the order ships and the payment is \
                 cleared, the system shall pack.",
    );
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.items.len(), 3);
    assert!(matches!(&group.items[1].body, ClauseBody::Verbal { verb, .. } if verb == "ships"));
    // All-copular `and` groups are fine; `remains` is a copula.
    let s = one("When the order is shipped and the payment is cleared, the system shall pack.");
    assert_eq!(s.frames.trigger.as_ref().unwrap().clause.items.len(), 2);
    let s = one("When the order ships and the pump remains active, the system shall pack.");
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert!(matches!(
        &group.items[1].body,
        ClauseBody::Copular {
            copula: ClauseCopula::Remains,
            ..
        }
    ));
}

#[test]
fn or_groups_admit_any_number_of_verbal_conjuncts() {
    // Disjunction of events is alternation — well-defined, exempt.
    let s = one("When the pump stops or the valve closes, the system shall alert.");
    let group = &s.frames.trigger.as_ref().unwrap().clause;
    assert_eq!(group.conj, Some(Conj::Or));
    assert_eq!(group.items.len(), 2);
    let s = one(
        "When the pump stops or the valve closes or the sensor fails or the \
                 breaker trips, the system shall alert.",
    );
    assert_eq!(s.frames.trigger.as_ref().unwrap().clause.items.len(), 4);
    // Same exemption under `If`.
    let s = one("If the pump stops or the valve closes, then the system shall alert.");
    assert_eq!(s.frames.trigger.as_ref().unwrap().clause.items.len(), 2);
}

#[test]
fn while_and_where_groups_are_unrestricted() {
    let s = one("While the pump runs and the fan spins, the daemon shall wait.");
    let group = &s.frames.states[0].clause;
    assert_eq!(group.conj, Some(Conj::And));
    assert_eq!(group.items.len(), 2);
    assert!(group
        .items
        .iter()
        .all(|c| matches!(c.body, ClauseBody::Verbal { .. })));
    let s = one("Where the pump runs and the fan spins, the daemon shall wait.");
    let group = &s.frames.scopes[0].clause;
    assert_eq!(group.items.len(), 2);
    assert!(group
        .items
        .iter()
        .all(|c| matches!(c.body, ClauseBody::Verbal { .. })));
    // Three verbal conjuncts under While.
    let s = one(
        "While the pump runs and the fan spins and the belt turns, the daemon \
                 shall wait.",
    );
    assert_eq!(s.frames.states[0].clause.items.len(), 3);
}

#[test]
fn mixed_coordination_still_wins_over_the_event_count() {
    // A mixed group is diagnosed as MixedCoordination during group parsing,
    // before the event count is ever taken.
    assert_eq!(
        parse(
            "When the order ships and the payment clears or the stock exists, the \
               system shall pack."
        ),
        Err(ParseError::MixedCoordination)
    );
    assert_eq!(
        parse(
            "If the order ships or the payment clears and the stock exists, then \
               the system shall halt."
        ),
        Err(ParseError::MixedCoordination)
    );
}

#[test]
fn multiple_event_conjuncts_error_kind_and_message() {
    assert_eq!(
        ParseError::MultipleEventConjuncts.kind(),
        "multiple_event_conjuncts"
    );
    let message = ParseError::MultipleEventConjuncts.to_string();
    assert!(
        message.contains("one event"),
        "message states the rule: {message}"
    );
    assert!(
        message.contains("While"),
        "message offers the While rewrite: {message}"
    );
    assert!(
        message.contains("is/are/remains"),
        "message offers the copular rewrite: {message}"
    );
}

// ====================================================================================
// 4. Totality over the new constructs
// ====================================================================================

/// Assert that `parse` — and the semantic derivations over any accepted
/// tree — return without panicking.
fn total(input: &str) {
    let result = catch_unwind(AssertUnwindSafe(|| {
        if let Ok(spec) = parse(input) {
            for sentence in &spec.sentences {
                let _ = speech_act(sentence);
                let _ = force(sentence);
                let _ = denote(sentence);
                let _ = ingest_contract(sentence);
                let _ = skeleton(sentence);
            }
            let _ = references(&spec);
        }
    }));
    assert!(result.is_ok(), "panic on input: {input:?}");
}

#[test]
fn directed_hostile_inputs_around_round2_constructs() {
    for input in [
        // `no`/`may` shrapnel.
        "No no no may may.",
        "no may.",
        "No may may.",
        "no.",
        "No client may retry",
        "No 中文 may 中文.",
        "No owner of no file of no folder may retry.",
        "Either no or no may retry.",
        "Both no and no may no.",
        "No client may not not retry.",
        // Trigger-conjunct shrapnel.
        "When and, the pump shall stop.",
        "When the order ships and, the pump shall stop.",
        "When the order ships and the payment clears,",
        "When or or or, no may no.",
        "If and then then, then the pump shall stop.",
        "While and while and while, the pump shall stop.",
        // Role/measure shrapnel.
        "The pump shall within.",
        "The daemon shall respond within 5.5.5 seconds.",
        "The daemon shall send to to to.",
        "The daemon shall respond within within within.",
        "The daemon shall respond within 5 seconds within 10 seconds within the timeout.",
        "The daemon shall store the report in .",
        "Within 5 seconds, the pump shall stop.",
        "The daemon shall retry before before before.",
        "The daemon shall retry after no.",
        "The daemon shall retry per .",
        // Combined stacks.
        "No request shall not never be logged, unless no operator is present, so that \
         no audit fails.",
        "Where no, While no, When no and no, no may no.",
        "When no order ships or no payment clears, no client should not retry within \
         zero, unless no override is active.",
    ] {
        total(input);
    }
    // A wide `or` trigger group of verbal clauses must stay total (and legal).
    let wide = format!(
        "When {}, the system shall alert.",
        (0..40)
            .map(|i| format!("the sensor{i} fails"))
            .collect::<Vec<_>>()
            .join(" or ")
    );
    total(&wide);
    assert!(
        parse(&wide).is_ok(),
        "a wide or-group of events is alternation and legal"
    );
}

/// Invariants every ACCEPTED parse must satisfy after round 2. The parser
/// legislates these; if any composition path lets a violating tree through,
/// the fuzzer finds it.
fn check_round2_invariants(input: &str, spec: &Specification) {
    for sentence in &spec.sentences {
        // Invariant 1: a When/If `and` group carries at most one verbal
        // (event) conjunct.
        if let Some(trigger) = &sentence.frames.trigger {
            if trigger.clause.conj == Some(Conj::And) {
                let verbal = trigger
                    .clause
                    .items
                    .iter()
                    .filter(|c| matches!(c.body, ClauseBody::Verbal { .. }))
                    .count();
                assert!(
                    verbal <= 1,
                    "accepted trigger `and` group with {verbal} events: {input:?}"
                );
            }
        }
        // Invariant 2: no accepted `may` core has a `no`-determined subject
        // item.
        if let Core::Deontic {
            subject,
            modal: Modal::May,
            ..
        } = &sentence.core
        {
            assert!(!subject.has_no_item(), "accepted `no` + may: {input:?}");
        }
        // Invariant 3: the skeleton polarity always equals the claim's
        // combined polarity (the shared-helper guarantee).
        if let Some(k) = skeleton(sentence) {
            match denote(sentence) {
                Denotation::Behavior(a) | Denotation::Admissibility(a) => match a.claim {
                    Claim::State { polarity, .. } | Claim::Action { polarity, .. } => {
                        assert_eq!(
                            k.polarity, polarity,
                            "skeleton/claim polarity drift on {input:?}"
                        );
                    }
                    Claim::Admissible { .. } | Claim::Capability { .. } => {}
                },
                Denotation::Vocabulary { .. } => {}
            }
        }
    }
}

#[test]
fn seeded_fuzz_over_round2_constructs() {
    // splitmix64: deterministic, seed pinned.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
            z ^ (z >> 31)
        }
        fn pick<'a>(&mut self, pool: &[&'a str]) -> &'a str {
            pool[(self.next() % pool.len() as u64) as usize]
        }
    }
    let frames = [
        "",
        "When the order ships, ",
        "When the order ships and the payment clears, ",
        "When the order ships and the payment is cleared, ",
        "When no order ships or the payment clears, ",
        "When the pump stops or the valve closes or the sensor fails, ",
        "If the pump stops or the valve closes, then ",
        "If the order ships and the payment clears, then ",
        "While the pump runs and the fan spins, ",
        "Where no endpoint is configured, ",
        "Where the flag is enabled, While the engine is running, When the order ships, ",
        "When the pump and the valve are open, ",
        "When no and no, ",
    ];
    let subjects = [
        "The daemon",
        "No client",
        "no client",
        "Each request",
        "A request",
        "Requests",
        "The client and no server",
        "Either no client or the proxy",
        "Both no client and the proxy",
        "The owner of no file",
        "No owner of the file",
        "At least 3 replicas",
        "no",
        "The pump and the valve",
    ];
    let pivots = [
        "shall",
        "shall not",
        "must",
        "must not",
        "should",
        "should not",
        "may",
        "may not",
        "MAY",
        "is",
        "is never",
        "is always",
        "are",
        "are never",
        "means",
    ];
    let tails = [
        " retry",
        " log no request",
        " be logged",
        " respond within 5 seconds",
        " respond within 5.5",
        " respond within five seconds",
        " respond within the timeout",
        " store the report and the invoice in the archive",
        " send the report to the operator via the queue about the outage",
        " retry before the session expires",
        " retry after the payment clears",
        " retry per second",
        " logged",
        " above the limit",
        " a sequence of requests",
        " within within",
        " no",
        "",
    ];
    let adjuncts = [
        "",
        ", unless no operator is present",
        ", unless the override is active",
        ", so that the operator retains control",
        ", in order to preserve the audit trail",
        ", unless no",
    ];
    let terminators = [".", "", " .", ".."];
    let mut rng = Rng(0x5eed_2026_0707);
    for _ in 0..4000 {
        let input = format!(
            "{}{} {}{}{}{}",
            rng.pick(&frames),
            rng.pick(&subjects),
            rng.pick(&pivots),
            rng.pick(&tails),
            rng.pick(&adjuncts),
            rng.pick(&terminators),
        );
        let result = catch_unwind(AssertUnwindSafe(|| {
            if let Ok(spec) = parse(&input) {
                check_round2_invariants(&input, &spec);
                for sentence in &spec.sentences {
                    let _ = ingest_contract(sentence);
                }
            }
        }));
        assert!(
            result.is_ok(),
            "panic or invariant violation on fuzz input: {input:?}"
        );
    }
}
