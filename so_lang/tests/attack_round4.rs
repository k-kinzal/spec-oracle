//! Adversarial conformance attack on the round-4 changes.
//!
//! Targets, per IMPROVE-SPEC-4: the manner slot (`ly` words in every
//! position), formula-bearing coordinated subjects, formula-layer quantifier
//! normalization (index vs logic split), lossless atom anchors and the
//! Admissibility atom kind, the typed pairing machinery (`paired`,
//! `EdgeKind`, supersession), capability (`is able to`) and `until`, and
//! seeded totality fuzzing over the new vocabulary.
//!
//! Passing tests pin behavior permanently. The three findings this attack
//! originally encoded as `#[ignore]`d expectations (mixed-`no` coordination
//! negating the plain item; the copular split swallowing a clause nested
//! under `until`/`before`/`after` inside a guard; clause-final `ly` verbs
//! rejected as EmptySubject) were FIXED by the round-4 fixer, so those
//! tests now run un-ignored and the pins of the old wrong behavior were
//! updated to pin the fix.

use so_lang::ast::*;
use so_lang::formula::{
    applicability, claim_formula, contract_formula, AssumptionSource, AtomRef, BehaviorAtom,
    ContractFormula, EdgeKind, Formula,
};
use so_lang::parse::{parse, ParseError};
use so_lang::semantics::{
    denote, force, ingest_contract, skeleton, speech_act, Claim, ClauseSkeleton, Denotation,
    Polarity, Quantifier, RoleKind, RoleValue, SpeechAct,
};
use std::panic::{catch_unwind, AssertUnwindSafe};

// ---- helpers ---------------------------------------------------------------------

/// Parse an input expected to hold exactly one sentence.
fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

/// The claim formula of an input, which must exist.
fn claim(input: &str) -> Formula {
    claim_formula(&one(input)).unwrap_or_else(|| panic!("{input:?} must have a claim formula"))
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
    assert_eq!(r.render(), rendered, "render must be a fixpoint for {rendered:?}");
}

/// Every behavior/admissibility atom in a formula, with its negation flag and
/// whether it sits in the Admissibility arm.
fn behavior_atoms(f: &Formula) -> Vec<(bool, bool, &BehaviorAtom)> {
    fn walk<'a>(f: &'a Formula, neg: bool, out: &mut Vec<(bool, bool, &'a BehaviorAtom)>) {
        match f {
            Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
                out.push((neg, false, behavior))
            }
            Formula::Atom { atom: AtomRef::Admissibility { behavior } } => {
                out.push((neg, true, behavior))
            }
            Formula::Atom { atom: AtomRef::Guard { .. } } => {}
            Formula::And { items } | Formula::Or { items } => {
                for item in items {
                    walk(item, neg, out);
                }
            }
            Formula::Not { inner } => walk(inner, !neg, out),
            Formula::Top | Formula::Bottom => {}
        }
    }
    let mut out = Vec::new();
    walk(f, false, &mut out);
    out
}

/// Every guard atom in a formula, with its negation flag.
fn guard_atoms(f: &Formula) -> Vec<(bool, &ClauseSkeleton, &str)> {
    fn walk<'a>(f: &'a Formula, neg: bool, out: &mut Vec<(bool, &'a ClauseSkeleton, &'a str)>) {
        match f {
            Formula::Atom { atom: AtomRef::Guard { clause, source, .. } } => {
                out.push((neg, clause, source))
            }
            Formula::Atom { .. } => {}
            Formula::And { items } | Formula::Or { items } => {
                for item in items {
                    walk(item, neg, out);
                }
            }
            Formula::Not { inner } => walk(inner, !neg, out),
            Formula::Top | Formula::Bottom => {}
        }
    }
    let mut out = Vec::new();
    walk(f, false, &mut out);
    out
}

fn not(inner: Formula) -> Formula {
    Formula::Not { inner: Box::new(inner) }
}

// ====================================================================================
// 1. The manner slot: `ly` words in every position
// ====================================================================================

#[test]
fn bare_ly_object_without_determiner_is_swept_into_manner_and_backticks_restore_it() {
    // The DOCUMENTED misclassification: a bare `ly` noun in object position
    // reads as manner; the backtick escape hatch is the legislated rewrite.
    let s = one("The depot shall record supply.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "record");
    assert_eq!(vp.manner, vec!["supply"]);
    assert!(vp.object.is_none(), "bare `supply` is (documented) manner, not the object");
    render_round_trips(&s);

    let s = one("The depot shall record `supply`.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["`supply`"]);
    render_round_trips(&s);

    // A backticked `ly` word never matches the manner rule anywhere.
    let s = one("The pump shall stop `immediately`.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["`immediately`"]);
    render_round_trips(&s);
}

#[test]
fn determiner_led_ly_words_stay_nouns() {
    // Determiner-led position is never manner.
    let s = one("The team shall review the supply.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["supply"]);

    // Even a word that is ONLY plausible as an adverb: inside an NP it is a
    // head like any other (legislated).
    let s = one("The pump shall stop the immediately.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["immediately"]);
    render_round_trips(&s);
}

#[test]
fn ly_words_as_np_modifiers_and_heads_are_untouched() {
    // Modifier before a head.
    let s = one("The system shall run the nightly build.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    match vp.object.as_ref().unwrap() {
        NpGroup::Single(np) => {
            assert_eq!(np.modifiers, vec!["nightly"]);
            assert_eq!(np.head, "build");
        }
        other => panic!("expected single object, got {other:?}"),
    }
    // `ly` head as a subject.
    let s = one("The assembly is running.");
    match &s.core {
        Core::Description { subject, .. } => assert_eq!(subject.heads(), vec!["assembly"]),
        other => panic!("expected description, got {other:?}"),
    }
}

#[test]
fn clause_final_verb_guard_takes_trailing_ly_words_as_manner() {
    // The motivating clause: the final-word-verb rule must not pick the `ly`
    // word as the verb.
    let s = one("When the export completes successfully, the system shall log the event.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, manner, object, roles, .. } => {
            assert_eq!(verb, "completes");
            assert_eq!(manner, &vec!["successfully".to_string()]);
            assert!(object.is_none());
            assert!(roles.is_empty());
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn manner_between_clause_verb_and_role_opener() {
    let s = one("When the pump stops immediately at the depot, the alarm shall sound.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, manner, roles, .. } => {
            assert_eq!(verb, "stops");
            assert_eq!(manner, &vec!["immediately".to_string()]);
            assert!(matches!(roles[0], RolePp::Location { .. }));
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    render_round_trips(&s);
}

/// SUPERSEDED PIN, updated with the fix: the old behavior rejected a bare
/// `ly`-final clause VERB (`reply`, `apply`, `fly` under a plural subject)
/// with the misleading diagnosis `EmptySubject`. The fixer added a back-off
/// to the final-word-verb rule: when the fully stripped reading leaves no
/// parseable subject+verb, trailing `ly` words are re-admitted innermost
/// first, so the `ly` word itself can be the verb. The backtick escape
/// still works and still forces the verb reading directly.
#[test]
fn clause_final_ly_verb_is_rejected_and_backticks_rescue_it() {
    // Fixed: the ly-final verb clause now parses (see
    // clause_final_ly_verb_should_parse_as_the_verb). The backtick spelling
    // keeps parsing too, with the backticks preserved.
    let s = one("When the peers `reply`, the server shall log the message.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, manner, .. } => {
            assert_eq!(verb, "`reply`");
            assert!(manner.is_empty());
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    // The back-off keeps the non-`ly` verb preference where one parses: a
    // trailing manner word after the verb stays manner.
    let s = one("When the peers reply quickly, the server shall log the message.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, manner, .. } => {
            assert_eq!(verb, "reply");
            assert_eq!(manner, &vec!["quickly".to_string()]);
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
    // And the round-4 motivating shape is untouched.
    let s = one("When the export completes successfully, the system shall log the event.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, manner, .. } => {
            assert_eq!(verb, "completes");
            assert_eq!(manner, &vec!["successfully".to_string()]);
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
}

#[test]
fn clause_final_ly_verb_should_parse_as_the_verb() {
    let s = one("When the peers reply, the server shall log the message.");
    let trigger = s.frames.trigger.as_ref().unwrap();
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, manner, .. } => {
            assert_eq!(verb, "reply");
            assert!(manner.is_empty());
        }
        other => panic!("expected verbal clause, got {other:?}"),
    }
}

#[test]
fn ly_verbs_after_a_modal_are_ordinary_verbs() {
    // Post-modal position is the verb slot; the manner rule is post-VERBAL.
    for (input, verb) in [
        ("The bird shall fly.", "fly"),
        ("The team shall apply the patch.", "apply"),
        ("The server shall reply to the client.", "reply"),
    ] {
        let s = one(input);
        assert_eq!(deontic_vp(&s).verb, verb, "in {input:?}");
        assert!(deontic_vp(&s).manner.is_empty(), "in {input:?}");
        render_round_trips(&s);
    }
}

#[test]
fn short_word_length_rule() {
    // len > 2: `fly` (3 chars) qualifies as manner in post-verbal position…
    let s = one("The drone shall monitor fly.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.manner, vec!["fly"]);
    assert!(vp.object.is_none());
    // …but the bare two-char word `ly` itself never does.
    let s = one("The parser shall emit ly.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["ly"]);
}

#[test]
fn multiple_juxtaposed_manner_words_and_conjunction_ends_the_run() {
    let s = one("The daemon shall stop quickly gracefully.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.manner, vec!["quickly", "gracefully"]);
    assert!(vp.object.is_none());
    render_round_trips(&s);
    // Legislated: `quickly and safely` is NOT supported — the conjunction
    // ends the manner run and the leftover is diagnosed.
    assert_eq!(
        parse("The daemon shall stop quickly and safely."),
        Err(ParseError::UnexpectedTokens { token: "and".into() })
    );
}

#[test]
fn manner_particle_and_roles_ordering() {
    let s = one("The session shall time out immediately within 30 seconds.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.verb, "time");
    assert_eq!(vp.particle.as_deref(), Some("out"));
    assert_eq!(vp.manner, vec!["immediately"]);
    assert!(matches!(vp.roles[0], RolePp::Deadline(_)));
    render_round_trips(&s);

    let s = one("The daemon shall shut down gracefully within 5 seconds.");
    let vp = deontic_vp(&s);
    assert_eq!((vp.verb.as_str(), vp.particle.as_deref()), ("shut", Some("down")));
    assert_eq!(vp.manner, vec!["gracefully"]);
    render_round_trips(&s);

    // Skeleton: manner is its own field, lowercased; words do not absorb it.
    let k = skeleton(&s).unwrap();
    assert_eq!(k.atoms[0].words, vec!["shut", "down"]);
    assert_eq!(k.atoms[0].manner, vec!["gracefully"]);

    // Manner may precede an object and renders back in that order.
    let s = one("The daemon shall log quickly the request.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.manner, vec!["quickly"]);
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["request"]);
    render_round_trips(&s);
}

/// SUPERSEDED PIN, updated with the fix: a manner word between the verb and
/// a particle no longer blocks the particle join — `shut gracefully down`
/// is the particle verb `shut down` with manner `gracefully`, sharing its
/// kernel with `shut down gracefully` (canonical render). The old behavior
/// left `down` as a bare OBJECT head, splitting the two spellings' atoms.
#[test]
fn manner_before_trailing_particle_leaves_the_particle_as_object() {
    let s = one("The daemon shall shut gracefully down.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.particle.as_deref(), Some("down"));
    assert_eq!(vp.manner, vec!["gracefully"]);
    assert_eq!(vp.object, None);
    // Canonical render reorders to `shut down gracefully`, and both
    // spellings share one tree and one kernel.
    assert_eq!(s.render(), "the daemon shall shut down gracefully.");
    render_round_trips(&s);
    let canonical = one("The daemon shall shut down gracefully.");
    assert_eq!(deontic_vp(&canonical), vp);
    assert_eq!(skeleton(&s).unwrap().atoms[0], skeleton(&canonical).unwrap().atoms[0]);
}

#[test]
fn manner_casing_is_preserved_in_the_tree_and_lowercased_in_digests() {
    let s = one("The pump shall stop IMMEDIATELY.");
    assert_eq!(deontic_vp(&s).manner, vec!["IMMEDIATELY"]);
    render_round_trips(&s);
    let k = skeleton(&s).unwrap();
    assert_eq!(k.atoms[0].manner, vec!["immediately"]);
    // Mixed case suffix match is ASCII-case-insensitive.
    let s = one("The pump shall stop QuickLY.");
    assert_eq!(deontic_vp(&s).manner, vec!["QuickLY"]);
    // Guard digests lowercase manner too.
    let s = one("When the export completes SUCCESSFULLY, the system shall log the event.");
    let k = skeleton(&s).unwrap();
    assert_eq!(k.guards.trigger.as_ref().unwrap().clauses[0].manner, vec!["successfully"]);
}

#[test]
fn multibyte_words_ending_in_ly_are_never_manner_and_never_panic() {
    // The ASCII guard protects the byte-slice suffix test: a non-ASCII word
    // ending in `ly` stays an object (and must not split a UTF-8 char).
    for (input, head) in [
        ("The pump shall stop cafély.", "cafély"),
        ("The pump shall stop 日本語ly.", "日本語ly"),
        ("The pump shall stop e\u{0301}ly.", "e\u{0301}ly"),
    ] {
        let s = one(input);
        let vp = deontic_vp(&s);
        assert!(vp.manner.is_empty(), "in {input:?}");
        assert_eq!(vp.object.as_ref().unwrap().heads(), vec![head], "in {input:?}");
        render_round_trips(&s);
    }
}

#[test]
fn quantifier_openers_ending_in_ly_are_not_manner() {
    // `exactly` ends in `ly` but a quantifier opener keeps its meaning…
    let s = one("The system shall create exactly 7 copies.");
    let vp = deontic_vp(&s);
    assert!(vp.manner.is_empty());
    match vp.object.as_ref().unwrap() {
        NpGroup::Single(np) => assert_eq!(np.det, Some(Det::Exactly { n: 7 })),
        other => panic!("expected single object, got {other:?}"),
    }
    // …and a broken quantifier keeps its precise diagnosis instead of
    // degrading into a manner word plus stray material.
    assert_eq!(
        parse("The system shall create exactly 5.5 copies."),
        Err(ParseError::QuantifierNotWhole { word: "5.5".into() })
    );
}

/// PIN: the positional rule is purely morphological, so `only` — a focus
/// adverb, not a manner adverb — is swept into the manner slot too.
#[test]
fn focus_adverb_only_is_swept_into_manner() {
    let s = one("The system shall log only the errors.");
    let vp = deontic_vp(&s);
    assert_eq!(vp.manner, vec!["only"]);
    assert_eq!(vp.object.as_ref().unwrap().heads(), vec!["errors"]);
    render_round_trips(&s);
}

// ====================================================================================
// 2. Coordinated subjects are formula-bearing
// ====================================================================================

#[test]
fn and_coordination_builds_a_conjunction_of_per_item_atoms() {
    let f = claim("The pump and the valve shall stop.");
    let atoms = behavior_atoms(&f);
    assert!(matches!(f, Formula::And { .. }));
    assert_eq!(atoms.len(), 2);
    let (neg0, adm0, pump) = &atoms[0];
    let (neg1, adm1, valve) = &atoms[1];
    assert!(!neg0 && !neg1 && !adm0 && !adm1);
    assert_eq!(pump.subject.head, "pump");
    assert_eq!(valve.subject.head, "valve");
    assert_eq!(pump.atom, valve.atom, "same kernel per item");
    assert_eq!(pump.source, "the pump shall stop");
    assert_eq!(valve.source, "the valve shall stop");
    // Round-4 pin: coordinated subjects are contract-bearing…
    assert!(contract_formula(&one("The pump and the valve shall stop.")).is_some());
    // …while the skeleton (the index) stays single-subject.
    assert!(skeleton(&one("The pump and the valve shall stop.")).is_none());
}

#[test]
fn or_and_marker_shapes() {
    assert!(matches!(claim("The pump or the valve shall stop."), Formula::Or { .. }));
    // Markers do not change the logic: `both … and` conjoins exactly as the
    // unmarked group, `either … or` disjoins.
    let marked = claim("Both the pump and the valve shall stop.");
    let unmarked = claim("The pump and the valve shall stop.");
    assert_eq!(marked, unmarked, "`both` must not change the formula");
    let marked = claim("Either the pump or the valve shall stop.");
    let unmarked = claim("The pump or the valve shall stop.");
    assert_eq!(marked, unmarked, "`either` must not change the formula");
}

#[test]
fn negative_polarity_distributes_not_per_atom() {
    // `shall not run` over and-subjects = ∧ᵢ ¬run(subjectᵢ).
    let f = claim("The pump and the valve shall not run.");
    match &f {
        Formula::And { items } => {
            assert_eq!(items.len(), 2);
            for item in items {
                assert!(matches!(item, Formula::Not { .. }), "Not applies PER ATOM");
            }
        }
        other => panic!("expected And, got {other:?}"),
    }
    let atoms = behavior_atoms(&f);
    assert!(atoms.iter().all(|(neg, _, _)| *neg));
    assert_eq!(atoms[0].2.source, "the pump shall not run");
    assert_eq!(atoms[1].2.source, "the valve shall not run");
}

#[test]
fn three_item_coordination() {
    let f = claim("The pump and the valve and the fan shall stop.");
    match &f {
        Formula::And { items } => assert_eq!(items.len(), 3),
        other => panic!("expected And over three items, got {other:?}"),
    }
    let heads: Vec<&str> = behavior_atoms(&f)
        .iter()
        .map(|(_, _, b)| b.subject.head.as_str())
        .collect();
    assert_eq!(heads, vec!["pump", "valve", "fan"]);
}

#[test]
fn coordinated_items_share_the_kernel_including_roles() {
    let f = claim("The pump and the valve shall stop within 5 seconds.");
    let atoms = behavior_atoms(&f);
    assert_eq!(atoms.len(), 2);
    for (_, _, b) in &atoms {
        assert_eq!(b.atom.words, vec!["stop"]);
        assert_eq!(b.atom.roles.len(), 1);
        assert_eq!(b.atom.roles[0].kind, RoleKind::Deadline);
        assert!(
            b.source.ends_with("shall stop within 5 seconds"),
            "anchor must carry the roles: {:?}",
            b.source
        );
    }
}

#[test]
fn all_no_coordination_is_one_flip_applied_per_universal_atom() {
    // `No pump and no valve shall run.` — has_no_item is one flip; each atom
    // is normalized Universal and negated once: ∀p ¬run ∧ ∀v ¬run. Sound.
    let f = claim("No pump and no valve shall run.");
    let atoms = behavior_atoms(&f);
    assert_eq!(atoms.len(), 2);
    for (neg, _, b) in &atoms {
        assert!(*neg);
        assert_eq!(b.subject.quantifier, Quantifier::Universal);
    }
    // And the flips CANCEL against a modal `not`: `No pump and no valve
    // shall not run.` is affirmative per atom (∀ run).
    let f = claim("No pump and no valve shall not run.");
    for (neg, _, b) in behavior_atoms(&f) {
        assert!(!neg, "no XOR not must cancel");
        assert_eq!(b.subject.quantifier, Quantifier::Universal);
    }
}

#[test]
fn mixed_no_coordination_must_not_negate_the_plain_item() {
    // First-order reading: (∀p ¬run(p)) ∧ run(valve). Fixed in round 4:
    // negation is composed PER ITEM (claim-level site XOR the item's own
    // `no`), so a sibling's `no` never leaks onto a plain item.
    let f = claim("No pump and the valve shall run.");
    let atoms = behavior_atoms(&f);
    let pump = atoms.iter().find(|(_, _, b)| b.subject.head == "pump").unwrap();
    let valve = atoms.iter().find(|(_, _, b)| b.subject.head == "valve").unwrap();
    assert!(pump.0, "the `no pump` atom is negated");
    assert!(!valve.0, "the `the valve` atom must NOT be negated");
    assert_eq!(pump.2.subject.quantifier, Quantifier::Universal);
    assert_eq!(valve.2.subject.quantifier, Quantifier::Definite);
    // Each anchor re-parses to exactly its item's sub-formula.
    assert_eq!(pump.2.source, "no pump shall run");
    assert_eq!(valve.2.source, "the valve shall run");
}

#[test]
fn mixed_no_coordination_with_a_claim_site_not_composes_per_item() {
    // `No pump and the valve shall not run.`: the deontic `not` XORs with
    // each item's own `no` — pump: not XOR no = affirmative over the
    // universal restrictor (∀p run(p)); valve: negated (¬run(valve)).
    let f = claim("No pump and the valve shall not run.");
    let atoms = behavior_atoms(&f);
    let pump = atoms.iter().find(|(_, _, b)| b.subject.head == "pump").unwrap();
    let valve = atoms.iter().find(|(_, _, b)| b.subject.head == "valve").unwrap();
    assert!(!pump.0, "`no pump shall not run` composes to an un-negated universal atom");
    assert!(valve.0, "`the valve shall not run` stays negated");
    // The anchors carry each item's surface sites, so re-deriving a claim
    // formula from an anchor reproduces exactly that item's sub-formula.
    assert_eq!(pump.2.source, "no pump shall not run");
    assert_eq!(valve.2.source, "the valve shall not run");
}

#[test]
fn coordination_formula_serde_shape() {
    let f = claim("The pump and the valve shall not run.");
    let v = serde_json::to_value(&f).unwrap();
    assert_eq!(v["kind"], "and");
    assert_eq!(v["items"][0]["kind"], "not");
    let atom = &v["items"][0]["inner"]["atom"];
    assert_eq!(atom["kind"], "behavior");
    assert_eq!(atom["behavior"]["subject"]["head"], "pump");
    assert_eq!(atom["behavior"]["subject"]["quantifier"]["kind"], "definite");
    assert_eq!(atom["behavior"]["source"], "the pump shall not run");
    // Round trip.
    let back: Formula = serde_json::from_value(v).unwrap();
    assert_eq!(back, f);
}

// ====================================================================================
// 3. Quantifier normalization: index vs logic
// ====================================================================================

#[test]
fn no_subject_normalizes_to_universal_under_exactly_one_negation() {
    let f = claim("No daemon shall sleep.");
    match &f {
        Formula::Not { inner } => match inner.as_ref() {
            Formula::Atom { atom: AtomRef::Behavior { behavior } } => {
                assert_eq!(behavior.subject.quantifier, Quantifier::Universal);
                assert_eq!(behavior.subject.head, "daemon");
                assert_eq!(behavior.atom.words, vec!["sleep"]);
                assert_eq!(behavior.source, "no daemon shall sleep");
            }
            other => panic!("expected a behavior atom under Not, got {other:?}"),
        },
        other => panic!("expected exactly one Not, got {other:?}"),
    }
    // A `no` subject in a DESCRIPTION goes through the same normalization.
    let f = claim("No daemon is asleep.");
    let atoms = behavior_atoms(&f);
    assert_eq!(atoms.len(), 1);
    assert!(atoms[0].0, "negated once");
    assert_eq!(atoms[0].2.subject.quantifier, Quantifier::Universal);
}

#[test]
fn double_negation_is_unnegated_and_equals_the_each_form() {
    // `No request shall not be logged.` → combined Affirmative → the atom is
    // NOT wrapped (no X: ¬P ≡ ∀X P).
    let f = claim("No request shall not be logged.");
    let no_atoms = behavior_atoms(&f);
    assert_eq!(no_atoms.len(), 1);
    let (neg, _, no_atom) = &no_atoms[0];
    assert!(!neg, "double negation composes to an un-negated atom");
    assert_eq!(no_atom.subject.quantifier, Quantifier::Universal);

    // First-order equality with `Each request shall be logged.`: the
    // normalized subject digest and behavior kernel coincide exactly.
    let g = claim("Each request shall be logged.");
    let each_atoms = behavior_atoms(&g);
    let (each_neg, _, each_atom) = &each_atoms[0];
    assert!(!each_neg);
    assert_eq!(no_atom.subject, each_atom.subject);
    assert_eq!(no_atom.atom, each_atom.atom);
    assert_eq!(no_atom.force, each_atom.force);
    // The surface residue that intentionally still differs: the speech act
    // (read off the pivot) and the lossless anchor.
    assert_eq!(no_atom.act, SpeechAct::Prohibition);
    assert_eq!(each_atom.act, SpeechAct::Obligation);
    assert_ne!(no_atom.source, each_atom.source);
}

#[test]
fn skeleton_keeps_the_surface_negative_quantifier_the_formula_does_not() {
    // The pinned index/logic split.
    let s = one("No daemon shall sleep.");
    let k = skeleton(&s).unwrap();
    assert_eq!(k.subject.quantifier, Quantifier::Negative, "skeleton = surface index");
    assert_eq!(k.polarity, Polarity::Negative);
    let f = claim_formula(&s).unwrap();
    let (_, _, b) = behavior_atoms(&f)[0];
    assert_eq!(b.subject.quantifier, Quantifier::Universal, "formula = normalized logic");

    let s = one("No request shall not be logged.");
    let k = skeleton(&s).unwrap();
    assert_eq!(k.subject.quantifier, Quantifier::Negative);
    assert_eq!(k.polarity, Polarity::Affirmative, "combined polarity XORs the two sites");
}

// ====================================================================================
// 4. Lossless atom anchors + the Admissibility arm
// ====================================================================================

/// Behavior/admissibility anchors must re-parse, and the re-parse must
/// reproduce the SAME atom — digest fields, negation flag, arm, and the
/// anchor itself (the canonical render is a fixpoint).
#[test]
fn every_behavior_anchor_reparses_to_the_same_atom() {
    let corpus = [
        "When the order ships, the pump shall stop within 5 seconds, unless the override is active, so that the line drains.",
        "No daemon shall sleep.",
        "No request shall not be logged.",
        "The pump and the valve shall not run within 5 seconds.",
        "Both the pump and the valve shall stop.",
        "Either the pump or the valve shall stop.",
        "The client may retry.",
        "The temperature is never above the limit.",
        "The daemon is able to shut down gracefully within 5 seconds.",
        "The pump shall run until the tank is full.",
        "The depot shall record supply.",
        "No pump and no valve shall run.",
        "THE CLIENT IS ABLE TO RETRY.",
        "Where the mode is strict, the retry count is at most 3.",
    ];
    for input in corpus {
        let original = claim_formula(&one(input)).unwrap();
        let atoms = behavior_atoms(&original);
        assert!(!atoms.is_empty(), "{input:?} must yield atoms");
        for (neg, adm, behavior) in atoms {
            let reparsed = claim_formula(&one(&behavior.source)).unwrap_or_else(|| {
                panic!("anchor {:?} of {input:?} must have a claim formula", behavior.source)
            });
            let ratoms = behavior_atoms(&reparsed);
            assert_eq!(ratoms.len(), 1, "anchor {:?} is one atom's material", behavior.source);
            let (rneg, radm, rbehavior) = ratoms[0];
            assert_eq!(rneg, neg, "negation must survive the anchor of {input:?}");
            assert_eq!(radm, adm, "the arm must survive the anchor of {input:?}");
            assert_eq!(
                rbehavior, behavior,
                "anchor {:?} must re-parse to an identical atom",
                behavior.source
            );
        }
    }
}

#[test]
fn behavior_anchor_excludes_frames_exception_and_purpose() {
    let s = one(
        "When the order ships, the pump shall stop within 5 seconds, \
         unless the override is active, so that the line drains.",
    );
    let f = claim_formula(&s).unwrap();
    let (_, _, b) = behavior_atoms(&f)[0];
    assert_eq!(b.source, "the pump shall stop within 5 seconds");
}

#[test]
fn guard_anchors_reparse_and_match_their_digests() {
    let s = one(
        "Where the mode is strict, While the engine remains hot, \
         When the order ships, the pump shall stop, unless the override is active.",
    );
    let app = applicability(&s);
    let guards = guard_atoms(&app);
    assert_eq!(guards.len(), 4);
    let expected_sources = [
        "the mode is strict",
        "the engine remains hot",
        "the order ships",
        "the override is active",
    ];
    for ((neg, clause, source), expected) in guards.iter().zip(expected_sources) {
        assert_eq!(*source, expected);
        assert_eq!(*neg, expected == "the override is active", "only the exception negates");
        // The anchor is a clause: re-parse it as a trigger guard and the
        // digest and anchor must reproduce exactly.
        let wrapped = one(&format!("When {source}, the pump shall stop."));
        let wrapped_app = applicability(&wrapped);
        let rguards = guard_atoms(&wrapped_app);
        assert_eq!(rguards.len(), 1);
        assert_eq!(rguards[0].1, *clause, "guard digest must survive its anchor {source:?}");
        assert_eq!(rguards[0].2, *source, "guard anchor must be a fixpoint");
    }
}

#[test]
fn coordinated_clause_group_guards_carry_per_item_anchors() {
    let s = one("When the order ships or the payment clears, the system shall log the event.");
    let f = applicability(&s);
    match &f {
        Formula::Or { items } => assert_eq!(items.len(), 2),
        other => panic!("expected Or over the guard atoms, got {other:?}"),
    }
    let guards = guard_atoms(&f);
    assert_eq!(guards[0].2, "the order ships");
    assert_eq!(guards[1].2, "the payment clears");
    for (_, clause, source) in guards {
        let wrapped = one(&format!("When {source}, the system shall log the event."));
        let wrapped_app = applicability(&wrapped);
        let rguards = guard_atoms(&wrapped_app);
        assert_eq!(rguards[0].1, clause);
    }
    // An `and` group over one event plus a state keeps per-item anchors too.
    let s = one("When the order ships and the engine remains hot, the pump shall stop.");
    let app = applicability(&s);
    let guards = guard_atoms(&app);
    assert_eq!(guards.len(), 2);
    assert_eq!(guards[0].2, "the order ships");
    assert_eq!(guards[1].2, "the engine remains hot");
}

#[test]
fn permissions_produce_the_admissibility_arm() {
    let s = one("The client may retry.");
    let f = claim_formula(&s).unwrap();
    match &f {
        Formula::Atom { atom: AtomRef::Admissibility { behavior } } => {
            assert_eq!(behavior.act, SpeechAct::Permission);
            assert_eq!(behavior.force, None);
            assert_eq!(behavior.source, "the client may retry");
            assert_eq!(behavior.atom.words, vec!["retry"]);
        }
        other => panic!("expected the Admissibility arm, got {other:?}"),
    }
    // An admissibility never yields a lone contract (nothing to discharge).
    assert!(contract_formula(&s).is_none());
    assert!(ingest_contract(&s).is_none());
    // A binding sentence must NOT use the Admissibility arm.
    match claim("The client shall retry.") {
        Formula::Atom { atom: AtomRef::Behavior { .. } } => {}
        other => panic!("expected the Behavior arm, got {other:?}"),
    }
}

#[test]
fn atomref_serde_shapes() {
    // Admissibility arm.
    let f = claim("The client may retry.");
    let v = serde_json::to_value(&f).unwrap();
    assert_eq!(v["kind"], "atom");
    assert_eq!(v["atom"]["kind"], "admissibility");
    assert_eq!(v["atom"]["behavior"]["source"], "the client may retry");
    assert_eq!(serde_json::from_value::<Formula>(v).unwrap(), f);
    // Guard arm.
    let a = applicability(&one("When the order ships, the pump shall stop."));
    let v = serde_json::to_value(&a).unwrap();
    assert_eq!(v["atom"]["kind"], "guard");
    assert_eq!(v["atom"]["source"], "the order ships");
    assert_eq!(v["atom"]["clause"]["subject_head"], "order");
    assert_eq!(serde_json::from_value::<Formula>(v).unwrap(), a);
    // Top.
    assert_eq!(serde_json::to_value(Formula::Top).unwrap()["kind"], "top");
}

// ====================================================================================
// 5. Typed pairing machinery
// ====================================================================================

// Round 5: `AssumptionSource` carries validated provenance (act + force).
// Round 11 (change 3): the pairing-algebra pins build their sources with
// an EXPLICIT reliance — the whole source conditional, explicitly selected
// through the graph-edge entry point — because a default reliance is a
// permanent candidate now and never forms A. The fixed target mirrors the
// contracts these pins pair onto (every source subject is disjoint from
// the pump).
fn source_of(kind: EdgeKind, input: &str) -> AssumptionSource {
    let sentence = one(input);
    let target = one("The pump shall stop.");
    let relied = AssumptionSource::from_sentence(kind, &sentence).unwrap().formula;
    AssumptionSource::for_guarantee_with_relied(kind, &sentence, &target, relied).unwrap()
}

#[test]
fn paired_with_empty_sources_is_the_identity() {
    let c = contract_formula(&one("When the order ships, the pump shall stop.")).unwrap();
    assert_eq!(c.assumption, Formula::Top);
    let paired = c.paired(&[]);
    assert_eq!(paired, c, "empty sources leave the contract unchanged (still ⊤)");
    // With assumption Top, saturation is the guarantee itself.
    assert_eq!(c.saturated(), c.guarantee);
}

#[test]
fn paired_single_source_replaces_top_without_a_wrapper() {
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    let a1 = source_of(EdgeKind::GuaranteeDischarge, "The sensor shall send the signal.");
    let paired = c.paired(std::slice::from_ref(&a1));
    // Supersession: the assumption IS the source formula — not And([Top, A]),
    // not And([A]).
    assert_eq!(paired.assumption, a1.formula);
    assert_eq!(paired.guarantee, c.guarantee, "the guarantee is untouched");
    fn contains_top(f: &Formula) -> bool {
        match f {
            Formula::Top => true,
            Formula::And { items } | Formula::Or { items } => items.iter().any(contains_top),
            Formula::Not { inner } => contains_top(inner),
            _ => false,
        }
    }
    assert!(!contains_top(&paired.assumption), "⊤ is superseded, never conjoined");
}

#[test]
fn paired_multiple_sources_conjoin_in_order() {
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    let a1 = source_of(EdgeKind::GuaranteeDischarge, "The sensor shall send the signal.");
    // Round 5: a permission validates only as an envelope, so the reliance
    // source is a binding sentence (occurrence reliance on an obligation).
    let a2 = source_of(EdgeKind::OccurrenceReliance, "The operator shall press the button.");
    let a3 = source_of(EdgeKind::AdmissibilityEnvelope, "The network may drop each packet.");
    let (a1_kept, a2_kept) = (a1.clone(), a2.clone());
    let paired = c.paired(&[a1.clone(), a2.clone(), a3.clone()]);
    // Round 6 (supersedes the round-4/5 shape that conjoined the envelope):
    // an envelope is compatibility data — it widens tolerated environment
    // behavior — so it never enters the assumption conjunction (negating it
    // under saturation would misread the permission as a behavior-set
    // complement). It stays in `sources`, in order.
    assert_eq!(
        paired.assumption,
        Formula::And { items: vec![a1.formula, a2.formula] }
    );
    assert_eq!(paired.sources, vec![a1_kept, a2_kept, a3]);
    assert_eq!(paired.guarantee, c.guarantee);
}

#[test]
fn repairing_supersedes_the_previous_pairing() {
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    let a1 = source_of(EdgeKind::GuaranteeDischarge, "The sensor shall send the signal.");
    let a2 = source_of(EdgeKind::GuaranteeDischarge, "The relay shall close.");
    let repaired = c
        .paired(std::slice::from_ref(&a1))
        .paired(std::slice::from_ref(&a2));
    // REPLACING, not accumulating: the second pairing's assumption stands
    // alone.
    assert_eq!(repaired.assumption, a2.formula);
    assert_ne!(repaired.assumption, Formula::And { items: vec![a1.formula, a2.formula] });
}

#[test]
fn saturation_over_a_paired_contract() {
    let c = contract_formula(&one("When the order ships, the pump shall stop.")).unwrap();
    let a1 = source_of(EdgeKind::GuaranteeDischarge, "The sensor shall send the signal.");
    let a2 = source_of(EdgeKind::OccurrenceReliance, "The clock shall tick.");
    let paired = c.paired(&[a1.clone(), a2.clone()]);
    // G ∨ ¬(∧ᵢAᵢ).
    assert_eq!(
        paired.saturated(),
        Formula::Or {
            items: vec![
                paired.guarantee.clone(),
                not(Formula::And { items: vec![a1.formula, a2.formula] }),
            ],
        }
    );
}

#[test]
fn edge_kind_and_assumption_source_serde() {
    assert_eq!(
        serde_json::to_value(EdgeKind::OccurrenceReliance).unwrap(),
        serde_json::json!("occurrence_reliance")
    );
    assert_eq!(
        serde_json::to_value(EdgeKind::GuaranteeDischarge).unwrap(),
        serde_json::json!("guarantee_discharge")
    );
    assert_eq!(
        serde_json::to_value(EdgeKind::AdmissibilityEnvelope).unwrap(),
        serde_json::json!("admissibility_envelope")
    );
    // Round 5: sources carry act + force provenance.
    let source =
        source_of(EdgeKind::GuaranteeDischarge, "The sensor shall send the signal.");
    let v = serde_json::to_value(&source).unwrap();
    assert_eq!(v["kind"], "guarantee_discharge");
    assert_eq!(v["act"], "obligation");
    assert_eq!(v["force"], "binding");
    assert_eq!(serde_json::from_value::<AssumptionSource>(v).unwrap(), source);
    // ContractFormula serde round trip.
    let c = contract_formula(&one("The pump shall stop.")).unwrap();
    let v = serde_json::to_value(&c).unwrap();
    assert_eq!(serde_json::from_value::<ContractFormula>(v).unwrap(), c);
}

// ====================================================================================
// 6. Capability (`is able to`) and `until`
// ====================================================================================

#[test]
fn is_able_to_parses_as_capability() {
    let s = one("The client is able to retry.");
    match &s.core {
        Core::Description { adverb: None, predicate: Predicate::AbleTo { vp }, .. } => {
            assert_eq!(vp.verb, "retry");
        }
        other => panic!("expected AbleTo description, got {other:?}"),
    }
    assert_eq!(speech_act(&s), SpeechAct::Description);
    assert_eq!(force(&s), None);
    match denote(&s) {
        Denotation::Behavior(assertion) => match assertion.claim {
            Claim::Capability { vp, .. } => assert_eq!(vp.verb, "retry"),
            other => panic!("expected capability claim, got {other:?}"),
        },
        other => panic!("expected behavior denotation, got {other:?}"),
    }
    // Ingests like other descriptions: (⊤, G).
    let contract = ingest_contract(&s).unwrap();
    assert_eq!(contract.assumption.render(), "⊤");
    assert!(contract_formula(&s).is_some());
    // Skeleton digests the vp.
    let k = skeleton(&s).unwrap();
    assert_eq!(k.atoms[0].words, vec!["retry"]);
    assert_eq!(k.polarity, Polarity::Affirmative);
    render_round_trips(&s);
}

#[test]
fn subject_no_denies_the_capability() {
    let s = one("No client is able to retry.");
    let k = skeleton(&s).unwrap();
    assert_eq!(k.polarity, Polarity::Negative);
    assert_eq!(k.subject.quantifier, Quantifier::Negative);
    // Formula: one Not over a Universal-normalized behavior atom.
    let f = claim_formula(&s).unwrap();
    let atoms = behavior_atoms(&f);
    assert_eq!(atoms.len(), 1);
    let (neg, adm, b) = atoms[0];
    assert!(neg, "capability denied");
    assert!(!adm, "a capability is a behavior atom, not admissibility");
    assert_eq!(b.subject.quantifier, Quantifier::Universal);
    render_round_trips(&s);
}

#[test]
fn capability_vp_carries_particle_manner_and_roles() {
    let s = one("The daemon is able to shut down gracefully within 5 seconds.");
    match &s.core {
        Core::Description { predicate: Predicate::AbleTo { vp }, .. } => {
            assert_eq!(vp.verb, "shut");
            assert_eq!(vp.particle.as_deref(), Some("down"));
            assert_eq!(vp.manner, vec!["gracefully"]);
            assert!(matches!(vp.roles[0], RolePp::Deadline(_)));
        }
        other => panic!("expected AbleTo, got {other:?}"),
    }
    let k = skeleton(&s).unwrap();
    assert_eq!(k.atoms[0].words, vec!["shut", "down"]);
    assert_eq!(k.atoms[0].manner, vec!["gracefully"]);
    assert_eq!(k.atoms[0].roles[0].kind, RoleKind::Deadline);
    render_round_trips(&s);
}

#[test]
fn able_to_is_case_insensitive_and_copula_agnostic() {
    let s = one("THE CLIENT IS ABLE TO RETRY.");
    match &s.core {
        Core::Description { predicate: Predicate::AbleTo { vp }, .. } => {
            assert_eq!(vp.verb, "RETRY", "open-class casing preserved");
        }
        other => panic!("expected AbleTo, got {other:?}"),
    }
    render_round_trips(&s);
    let s = one("The clients are able to retry.");
    assert!(matches!(
        &s.core,
        Core::Description { copula: Copula::Are, predicate: Predicate::AbleTo { .. }, .. }
    ));
}

#[test]
fn able_to_triggers_only_immediately_after_the_copula() {
    // SUPERSEDED PIN (round 5, change 7): the description adverb is now
    // admitted between copula and `able to` — `is always able to <vp>` is
    // capability with the adverb kept (round 4 had pinned the open-words
    // fallback).
    let s = one("The client is always able to retry.");
    match &s.core {
        Core::Description {
            adverb: Some(DescriptionAdverb::Always),
            predicate: Predicate::AbleTo { vp },
            ..
        } => assert_eq!(vp.verb, "retry"),
        other => panic!("expected always + AbleTo, got {other:?}"),
    }
    // SUPERSEDED PIN (round 8, change 5): capability is now
    // POSITIONAL-CONSISTENT — `able to` exactly after the copula parses as
    // `Predicate::AbleTo` in copular RELATIVES and copular CLAUSE bodies
    // too, not only in description cores. The round-4 pin froze the flat
    // Words fallback in those positions, which made the same words mean
    // capability in one position and an opaque word run in another.
    let s = one("The client that is able to retry is active.");
    match &s.core {
        Core::Description { subject: NpGroup::Single(np), predicate, .. } => {
            match &np.relative.as_ref().unwrap().body {
                RelativeBody::Copular { predicate: Predicate::AbleTo { vp }, .. } => {
                    assert_eq!(vp.verb, "retry");
                }
                other => panic!("expected AbleTo in the relative, got {other:?}"),
            }
            assert_eq!(predicate, &Predicate::Words { words: vec!["active".into()] });
        }
        other => panic!("expected description, got {other:?}"),
    }
    // Inside a frame clause: the guard digest is structural since round 8
    // (`able to` + verb kernel; the vp's roles digest structurally).
    let s = one("While the client is able to retry, the pump shall run.");
    let app = applicability(&s);
    let guards = guard_atoms(&app);
    assert_eq!(guards.len(), 1);
    assert_eq!(guards[0].1.words, vec!["able", "to", "retry"]);
    assert_eq!(guards[0].2, "the client is able to retry");
    // As NP material before a head: ordinary modifiers.
    let s = one("The able to retry flag is set.");
    match &s.core {
        Core::Description { subject: NpGroup::Single(np), .. } => {
            assert_eq!(np.modifiers, vec!["able", "to", "retry"]);
            assert_eq!(np.head, "flag");
        }
        other => panic!("expected description, got {other:?}"),
    }
    // An empty capability vp is diagnosed.
    assert_eq!(parse("The client is able to."), Err(ParseError::EmptyVp));
}

#[test]
fn can_is_rejected_with_the_is_able_to_hint() {
    let err = parse("The client can retry.").unwrap_err();
    assert_eq!(err, ParseError::UnsupportedModal { word: "can".into() });
    let message = err.to_string();
    assert!(
        message.contains("is able to"),
        "the UnsupportedModal hint must mention `is able to`, got: {message}"
    );
}

#[test]
fn until_is_a_clausal_role() {
    let s = one("The pump shall run until the tank is full.");
    let vp = deontic_vp(&s);
    match &vp.roles[0] {
        RolePp::Until(clause) => {
            assert_eq!(clause.subject.heads(), vec!["tank"]);
            assert!(matches!(clause.body, ClauseBody::Copular { .. }));
        }
        other => panic!("expected Until role, got {other:?}"),
    }
    let k = skeleton(&s).unwrap();
    assert_eq!(k.atoms[0].roles[0].kind, RoleKind::Until);
    // Round 8, change 1 (pin updated): the clause value carries the full
    // nested skeleton + full render.
    match &k.atoms[0].roles[0].value {
        RoleValue::Clause { skeleton, full } => {
            assert_eq!(skeleton.subject_head, "tank");
            assert_eq!(skeleton.words, vec!["full"]);
            assert_eq!(full, "the tank is full");
        }
        other => panic!("expected clause digest, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn until_nests_clauses_like_before_and_after() {
    let s = one("The pump shall run until the valve opens after the tank drains.");
    let vp = deontic_vp(&s);
    match &vp.roles[0] {
        RolePp::Until(clause) => match &clause.body {
            ClauseBody::Verbal { verb, roles, .. } => {
                assert_eq!(verb, "opens");
                assert!(matches!(&roles[0], RolePp::After(inner) if inner.subject.heads() == vec!["tank"]));
            }
            other => panic!("expected verbal until-clause, got {other:?}"),
        },
        other => panic!("expected Until role, got {other:?}"),
    }
    render_round_trips(&s);
}

#[test]
fn until_shares_the_depth_bound() {
    let mut deep = String::from("The pump shall run");
    for _ in 0..70 {
        deep.push_str(" until the pump runs");
    }
    deep.push('.');
    assert_eq!(parse(&deep), Err(ParseError::PhraseTooDeep { limit: 64 }));
    // Below the bound the tower parses and round-trips.
    let mut ok = String::from("The pump shall run");
    for _ in 0..10 {
        ok.push_str(" until the pump runs");
    }
    ok.push('.');
    render_round_trips(&one(&ok));
}

#[test]
fn until_inside_guard_clauses_and_capability() {
    // A guard clause's verbal body carries `until` like any role — when the
    // nested clause is itself verbal.
    let s = one("While the pump runs until the tank drains, the alarm shall stay silent.");
    let app = applicability(&s);
    let guards = guard_atoms(&app);
    assert_eq!(guards.len(), 1);
    assert_eq!(guards[0].1.subject_head, "pump");
    assert_eq!(guards[0].1.words, vec!["runs"]);
    assert_eq!(guards[0].1.roles[0].kind, RoleKind::Until);
    assert_eq!(guards[0].2, "the pump runs until the tank drains");
    render_round_trips(&s);
    // Capability + until compose.
    let s = one("The client is able to retry until the limit is reached.");
    match &s.core {
        Core::Description { predicate: Predicate::AbleTo { vp }, .. } => {
            assert!(matches!(vp.roles[0], RolePp::Until(_)));
        }
        other => panic!("expected AbleTo, got {other:?}"),
    }
    render_round_trips(&s);
}

/// SUPERSEDED PIN, updated with the fix: inside a GUARD clause, a COPULAR
/// clause nested under `until` (or `before`/`after` — same machinery) used
/// to be swallowed by the copular-first split into one flat subject NP.
/// Fixed: when the would-be copular subject slice contains a bare clausal
/// role preposition, the verbal reading is preferred wherever it parses, so
/// the guard keeps its nested-clause role. A subject that merely CONTAINS
/// such a word with no verbal reading stays copular.
#[test]
fn until_copular_clause_inside_a_guard_is_swallowed_by_the_copular_split() {
    // `before`/`after` go through the same machinery as `until`.
    for prep in ["until", "before", "after"] {
        let input = format!(
            "While the pump runs {prep} the tank is full, the alarm shall stay silent."
        );
        let s = one(&input);
        let clause = &s.frames.states[0].clause.items[0];
        assert_eq!(clause.subject.heads(), vec!["pump"], "in {input:?}");
        match &clause.body {
            ClauseBody::Verbal { verb, roles, .. } => {
                assert_eq!(verb, "runs", "in {input:?}");
                let inner = match &roles[0] {
                    RolePp::Until(c) | RolePp::Before(c) | RolePp::After(c) => c,
                    other => panic!("expected a clausal role, got {other:?}"),
                };
                assert_eq!(inner.subject.heads(), vec!["tank"], "in {input:?}");
            }
            other => panic!("expected verbal clause, got {other:?}"),
        }
        render_round_trips(&s);
    }
    // A copular guard whose subject merely contains a clausal-prep word (no
    // verbal reading exists) keeps the copular split.
    let s = one("While the after image is ready, the alarm shall stay silent.");
    let clause = &s.frames.states[0].clause.items[0];
    match (&clause.subject, &clause.body) {
        (NpGroup::Single(np), ClauseBody::Copular { .. }) => {
            assert_eq!(np.head, "image");
            assert_eq!(np.modifiers, vec!["after"]);
        }
        other => panic!("expected the copular reading to survive, got {other:?}"),
    }
    // The same sentence shape in a DEONTIC core keeps parsing correctly
    // (role prepositions are closed inside a verb phrase).
    let s = one("The pump shall run until the tank is full.");
    assert!(matches!(deontic_vp(&s).roles[0], RolePp::Until(_)));
}

#[test]
fn until_copular_clause_inside_a_guard_should_stay_an_until_role() {
    let s = one("While the pump runs until the tank is full, the alarm shall stay silent.");
    let clause = &s.frames.states[0].clause.items[0];
    assert_eq!(clause.subject.heads(), vec!["pump"]);
    match &clause.body {
        ClauseBody::Verbal { verb, roles, .. } => {
            assert_eq!(verb, "runs");
            assert!(matches!(&roles[0], RolePp::Until(inner) if inner.subject.heads() == vec!["tank"]));
        }
        other => panic!("expected verbal guard with an Until role, got {other:?}"),
    }
}

// ====================================================================================
// 7. Totality: seeded fuzz over the round-4 vocabulary
// ====================================================================================

/// Words biased toward the round-4 machinery: `ly` forms in every flavor,
/// `able`/`to`, `until`, coordination, `no`, particles, measures, backticks,
/// multibyte.
const FUZZ_WORDS: &[&str] = &[
    "the", "a", "an", "no", "each", "every", "all", "any", "both", "either", "and", "or", "not",
    "is", "are", "shall", "must", "should", "may", "remains", "means", "that", "unless", "so",
    "in", "order", "to", "able", "until", "before", "after", "within", "for", "per", "at",
    "least", "most", "exactly", "pump", "valve", "supply", "reply", "apply", "fly", "ly",
    "quickly", "immediately", "successfully", "gracefully", "only", "nightly", "assembly",
    "stop", "run", "time", "shut", "log", "out", "down", "up", "off", "5", "5.5", "seconds",
    "`supply`", "`immediately`", "café", "日本語ly", "e\u{0301}ly", "QuickLY", "When", "While,",
    "then", ",", ".",
];

/// A tiny deterministic xorshift so the suite never depends on external
/// randomness.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn pick<'a>(&mut self, words: &[&'a str]) -> &'a str {
        words[(self.next() % words.len() as u64) as usize]
    }
}

#[test]
fn seeded_fuzz_never_panics_and_accepted_sentences_render_stably() {
    let mut rng = Rng(0x5eed_2026_0707);
    let mut accepted = 0usize;
    for case in 0..800 {
        let len = 1 + (rng.next() % 14) as usize;
        let mut input = String::new();
        for i in 0..len {
            if i > 0 {
                input.push(' ');
            }
            input.push_str(rng.pick(FUZZ_WORDS));
        }
        if rng.next().is_multiple_of(2) {
            input.push('.');
        }
        let outcome = catch_unwind(AssertUnwindSafe(|| parse(&input)));
        let result = match outcome {
            Ok(result) => result,
            Err(_) => panic!("parse panicked on fuzz case {case}: {input:?}"),
        };
        if let Ok(spec) = result {
            accepted += 1;
            // Anything accepted must render to a stable canonical form…
            let rendered = spec.render();
            let respec = parse(&rendered).unwrap_or_else(|e| {
                panic!("render {rendered:?} of accepted fuzz input {input:?} must re-parse: {e}")
            });
            assert_eq!(
                respec.render(),
                rendered,
                "render must be a fixpoint for fuzz input {input:?}"
            );
            // …and every derived view must be total over it.
            for sentence in &spec.sentences {
                let _ = speech_act(sentence);
                let _ = denote(sentence);
                let _ = skeleton(sentence);
                let _ = claim_formula(sentence);
                let _ = applicability(sentence);
                if let Some(contract) = contract_formula(sentence) {
                    let _ = contract.saturated();
                    let _ = contract.paired(&[]);
                }
            }
        }
    }
    // The generator must actually exercise the accept path, not only rejects.
    assert!(accepted > 0, "the fuzz vocabulary should accept at least one sentence");
}
