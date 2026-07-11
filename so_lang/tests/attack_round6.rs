//! Adversarial conformance attack on the ROUND-6 changes (IMPROVE-SPEC-6):
//! lossiness-aware propositions, target-aware pairing, envelope semantics,
//! force-aware `assess`, interval reasoning, VP alternatives, plain-NP
//! `with` rejection, bounded durations, and totality under mixed input.
//!
//! Passing tests pin behavior permanently. Tests marked `#[ignore]` assert
//! the behavior the round-6 doctrine PROMISES but the code does not deliver;
//! each carries its finding title.

use so_lang::ast::*;
use so_lang::formula::{
    claim_formula, contract_formula, AssumptionSource, AtomRef, ContractFormula, EdgeKind, Formula,
    PairingError, SubjectRelation,
};
use so_lang::parse::{parse, ParseError};
use so_lang::relate::{assess, contradicts, implies, refines, Outcome, Ternary};
use so_lang::semantics::{skeleton, RoleValue, Skeleton};

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

/// Round 11 (change 3): pairing pins build their sources with an EXPLICIT
/// reliance (the whole source conditional, explicitly selected through the
/// graph-edge entry point) — a default reliance is a permanent candidate
/// now and never forms A.
fn explicit_source(
    kind: EdgeKind,
    source: &so_lang::ast::Sentence,
    target: &so_lang::ast::Sentence,
) -> AssumptionSource {
    let default = AssumptionSource::for_guarantee(kind, source, target).unwrap();
    AssumptionSource::for_guarantee_with_relied(kind, source, target, default.formula.clone())
        .unwrap()
}

// =====================================================================================
// Change 1 — lossiness awareness: no false Yes
// =====================================================================================

/// Relatives differing DEEP in an of-chain: the chain link's relative is part
/// of the subject's full identity, so a coarse (quantifier+head) match with a
/// full mismatch is Unknown — never Yes, never No.
#[test]
fn deep_of_chain_relative_difference_is_unknown() {
    let locked = claim("The owner of the file that is locked shall sign.");
    let open = claim("The owner of the file that is open shall not sign.");
    assert_eq!(contradicts(&locked, &open), Ternary::Unknown);
    assert_eq!(implies(&locked, &open), Ternary::Unknown);
    assert_eq!(implies(&open, &locked), Ternary::Unknown);
    // Identical deep chains still meet — the sharpening removes only false
    // positives.
    let denial = claim("The owner of the file that is locked shall not sign.");
    assert_eq!(contradicts(&locked, &denial), Ternary::Yes);
}

/// Nested determiners are part of what the phrase names (legislated):
/// `the owner of a file` and `the owner of the file` differ in full identity.
#[test]
fn nested_determiners_distinguish_full_identity() {
    let definite = claim("The owner of the file shall sign.");
    let indefinite = claim("The owner of a file shall not sign.");
    assert_eq!(contradicts(&definite, &indefinite), Ternary::Unknown);
    assert_eq!(implies(&definite, &indefinite), Ternary::Unknown);
}

/// Role noun phrases carry full identity too: a Recipient differing only in
/// its relative clause must not collide.
#[test]
fn role_np_relative_difference_is_unknown() {
    let active = claim("The daemon shall send the report to the user who is active.");
    let idle = claim("The daemon shall not send the report to the user who is idle.");
    assert_eq!(contradicts(&active, &idle), Ternary::Unknown);
    let denial = claim("The daemon shall not send the report to the user who is active.");
    assert_eq!(contradicts(&active, &denial), Ternary::Yes);
}

/// Coordinated object items with different relatives: one item's relative
/// difference is enough to block the match.
#[test]
fn coordinated_object_relative_difference_is_unknown() {
    let a = claim("The daemon shall notify the admin and the user that is active.");
    let b = claim("The daemon shall not notify the admin and the user that is idle.");
    assert_eq!(contradicts(&a, &b), Ternary::Unknown);
    let denial = claim("The daemon shall not notify the admin and the user that is active.");
    assert_eq!(contradicts(&a, &denial), Ternary::Yes);
}

/// Passive-agent noun phrases digest as Agent roles and carry full identity:
/// `by the daemon that is primary` vs `by the daemon that is secondary`.
#[test]
fn agent_np_relative_difference_is_unknown() {
    let primary = claim("The request is logged by the daemon that is primary.");
    let secondary = claim("The request is never logged by the daemon that is secondary.");
    assert_eq!(contradicts(&primary, &secondary), Ternary::Unknown);
    let denial = claim("The request is never logged by the daemon that is primary.");
    assert_eq!(contradicts(&primary, &denial), Ternary::Yes);
    // The deontic passive still meets the described passive at one atom.
    let deontic = claim("The request shall not be logged by the daemon that is primary.");
    assert_eq!(contradicts(&primary, &deontic), Ternary::Yes);
}

/// Manner-only differences never produce a Yes: `stop immediately` and
/// `stop` are different atoms, and their disjointness is not provable.
#[test]
fn manner_only_difference_is_unknown() {
    let manner = claim("The pump shall stop immediately.");
    let bare = claim("The pump shall not stop.");
    assert_eq!(contradicts(&manner, &bare), Ternary::Unknown);
    assert_eq!(
        implies(&manner, &claim("The pump shall stop.")),
        Ternary::Unknown
    );
}

/// Subject identity stays case-sensitive (restrictor and head are kept as
/// written): `The Pump` and `the pump` do not meet. Conservative — never a
/// false Yes from case folding half the digest.
#[test]
fn subject_case_difference_stays_unknown() {
    let upper = claim("The Pump shall stop.");
    let lower = claim("The pump shall not stop.");
    assert_eq!(contradicts(&upper, &lower), Ternary::Unknown);
}

/// FINDING (critical, FIXED in the round-6 follow-up): np-group CONJUNCTION
/// used to be dropped from object and role digests, so `notify the admin or
/// the owner` and `notify the admin and the owner` carried EQUAL
/// propositions — `implies` answered Yes in BOTH directions (and `assess`
/// called them Equivalent), but an or-object does not entail an and-object.
/// Fixed by digesting the group's `and`/`or` alongside the item skeletons
/// (`Atom::objects_conj`, `RoleValue::Heads::conj`); the pairs are now
/// Unknown — conservative, never a false Yes (the true `and → or` direction
/// stays future work).
#[test]
fn object_group_conjunction_must_block_the_false_yes() {
    let or_obj = claim("The daemon shall notify the admin or the owner.");
    let and_obj = claim("The daemon shall notify the admin and the owner.");
    // `or` must not entail `and`. (Yes today — a false Yes.)
    assert_ne!(implies(&or_obj, &and_obj), Ternary::Yes);
    assert_ne!(
        assess(
            &one("The daemon shall notify the admin or the owner."),
            &one("The daemon shall notify the admin and the owner."),
        ),
        Outcome::Equivalent
    );
    // Same defect through a role NP group.
    let or_role = claim("The daemon shall send the report to the admin or the owner.");
    let and_role = claim("The daemon shall send the report to the admin and the owner.");
    assert_ne!(implies(&or_role, &and_role), Ternary::Yes);
}

// =====================================================================================
// Change 2 — target-aware pairing
// =====================================================================================

/// Of-chain subjects: the whole modifier-carrying chain key decides.
/// SUPERSEDED (round 10, change 6): a shared key no longer REJECTS — the
/// keys are tentative textual identity, so the collision is RECORDED as
/// `SubjectRelation::SharedKeys` (candidate only, never contract-forming)
/// instead of hard-failing construction.
#[test]
fn of_chain_subject_keys_gate_pairing() {
    let target = one("The owner of the file shall sign.");
    let same = one("The owner of the file is ready.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &same, &target).unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    assert!(
        !shared.contract_forming(),
        "shared keys ride as candidates, never in A"
    );
    // A different chain link is a different key.
    let bucket = one("The owner of the bucket is ready.");
    AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &bucket, &target)
        .expect("different of-chain pairs");
    // Chain links keep their modifiers: owner.backup.file != owner.file.
    let backup = one("The owner of the backup file is ready.");
    AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &backup, &target)
        .expect("modifier-bearing chain is a different key");
    // The key is one path string, not a containment relation: `the file` is
    // textually disjoint from `the owner of the file`.
    let file = one("The file is ready.");
    AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &file, &target)
        .expect("whole-key comparison, not component containment");
}

/// A coordinated TARGET sharing any key with the source is OBSERVED as
/// SharedKeys, in both coordination directions (round 10 — recorded, not
/// rejected; the shared-key source rides as a candidate).
#[test]
fn coordinated_target_overlap_is_recorded_as_shared() {
    let target = one("The daemon and the pump shall run.");
    let source = one("The pump is primed.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &source, &target).unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    assert!(!shared.contract_forming());
    // Coordinated on both sides, one shared key.
    let both = one("The valve and the pump are primed.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &both, &target).unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    // Fully disjoint coordinations pair and — with an explicit reliance
    // (round 11, change 3) — form A.
    let disjoint = one("The valve and the sensor are primed.");
    let ok = AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &disjoint, &target)
        .expect("disjoint coordinated subjects pair");
    assert_eq!(ok.subject_relation, SubjectRelation::DisjointKeys);
    assert!(
        !ok.contract_forming(),
        "default reliance: candidate only (round 11)"
    );
    assert!(explicit_source(EdgeKind::OccurrenceReliance, &disjoint, &target).contract_forming());
}

/// Subject keys deliberately DROP relatives (documented tentative identity):
/// a source restricted by a relative clause still collides with the bare
/// target subject. Pinned so the caveat stays true rather than silently
/// narrowing — round 10: the collision is recorded as SharedKeys.
#[test]
fn relative_only_difference_is_still_same_subject() {
    let target = one("The daemon shall flush the buffer.");
    let restricted = one("The daemon that is idle is ready.");
    let shared =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &restricted, &target)
            .unwrap();
    assert_eq!(shared.subject_relation, SubjectRelation::SharedKeys);
    assert!(!shared.contract_forming());
}

/// The rest of the act × kind matrix under `for_guarantee`: a description
/// cannot discharge or bound, a binding sentence is no envelope.
#[test]
fn remaining_act_kind_cells_hold_under_for_guarantee() {
    let target = one("The daemon shall flush the buffer.");
    let description = one("The scheduler is ready.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &description, &target)
            .unwrap_err(),
        PairingError::DescriptionOnlyReliance
    );
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::AdmissibilityEnvelope, &description, &target)
            .unwrap_err(),
        PairingError::DescriptionOnlyReliance
    );
    let binding = one("The scheduler shall rotate the logs.");
    assert_eq!(
        AssumptionSource::for_guarantee(EdgeKind::AdmissibilityEnvelope, &binding, &target)
            .unwrap_err(),
        PairingError::BindingNoEnvelope
    );
    AssumptionSource::for_guarantee(EdgeKind::GuaranteeDischarge, &binding, &target)
        .expect("a binding guarantee discharges");
}

/// `from_sentence` (kept, doc-hidden) applies the matrix ONLY: with no
/// target in hand it cannot observe the subject relation and sets the
/// LEGISLATED `DisjointKeys` default (round 10 — the pre-round-10 reading,
/// matching the serde default for stored edges), while `for_guarantee`
/// observes the same source honestly as SharedKeys — pinned so the two
/// entry points stay honestly different rather than drifting together.
#[test]
#[allow(deprecated)]
fn from_sentence_omits_the_subject_check() {
    let target = one("The daemon shall flush the buffer.");
    let same = one("The daemon is available.");
    let blind = AssumptionSource::from_sentence(EdgeKind::OccurrenceReliance, &same)
        .expect("matrix-only entry point accepts");
    assert_eq!(blind.subject_relation, SubjectRelation::DisjointKeys);
    let observed =
        AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &same, &target).unwrap();
    assert_eq!(observed.subject_relation, SubjectRelation::SharedKeys);
}

/// `advisory_reliance_check` is conservative implication: a refined source
/// formula proves the looser reliance, an admissibility source can never
/// witness a behavior reliance (species mismatch → Unknown, not No).
#[test]
fn advisory_reliance_check_is_conservative() {
    let target = one("The daemon shall flush the buffer.");
    // Structural interval rule flows through: within 5 proves within 10.
    let tight = one("The scheduler shall rotate the logs within 5 seconds.");
    let a = AssumptionSource::for_guarantee(EdgeKind::OccurrenceReliance, &tight, &target).unwrap();
    let loose = claim("The scheduler shall rotate the logs within 10 seconds.");
    assert_eq!(a.advisory_reliance_check(&loose), Ternary::Yes);
    // The other direction is Unknown, never No.
    let tighter = claim("The scheduler shall rotate the logs within 2 seconds.");
    assert_eq!(a.advisory_reliance_check(&tighter), Ternary::Unknown);
    // An envelope's admissibility atom never meets a behavior atom — even
    // with an identical kernel (`drop packets`), the species differ.
    let permission = one("The network may drop packets.");
    let envelope =
        AssumptionSource::for_guarantee(EdgeKind::AdmissibilityEnvelope, &permission, &target)
            .unwrap();
    let obliged = claim("The network shall drop packets.");
    assert_eq!(envelope.advisory_reliance_check(&obliged), Ternary::Unknown);
    // Everything proves Top.
    assert_eq!(
        envelope.advisory_reliance_check(&Formula::Top),
        Ternary::Yes
    );
}

/// Serde of the pairing artifacts: snake_case edge kinds, the round-6 error
/// name, and a full source round-trip for every kind.
#[test]
fn pairing_serde_and_error_names() {
    assert_eq!(
        serde_json::to_value(EdgeKind::AdmissibilityEnvelope).unwrap(),
        serde_json::json!("admissibility_envelope")
    );
    assert_eq!(
        serde_json::to_value(EdgeKind::OccurrenceReliance).unwrap(),
        serde_json::json!("occurrence_reliance")
    );
    assert_eq!(
        serde_json::to_value(EdgeKind::GuaranteeDischarge).unwrap(),
        serde_json::json!("guarantee_discharge")
    );
    // Round 10: `PairingError::SameSubject` is removed (shared keys are
    // `SubjectRelation::SharedKeys` data now); its `same_subject` telemetry
    // name is retired with it. SubjectRelation serializes snake_case.
    assert_eq!(
        serde_json::to_value(SubjectRelation::SharedKeys).unwrap(),
        serde_json::json!("shared_keys")
    );
    assert_eq!(
        serde_json::to_value(SubjectRelation::DisjointKeys).unwrap(),
        serde_json::json!("disjoint_keys")
    );
    let target = one("The daemon shall flush the buffer.");
    let permission = one("The network may drop packets.");
    let envelope =
        AssumptionSource::for_guarantee(EdgeKind::AdmissibilityEnvelope, &permission, &target)
            .unwrap();
    let json = serde_json::to_value(&envelope).unwrap();
    assert_eq!(json["kind"], "admissibility_envelope");
    assert_eq!(json["act"], "permission");
    assert_eq!(json["force"], serde_json::Value::Null);
    let back: AssumptionSource = serde_json::from_value(json).unwrap();
    assert_eq!(back, envelope);
}

// =====================================================================================
// Change 3 — envelope semantics
// =====================================================================================

/// Two reliances plus an envelope: the assumption is the And of the two
/// reliance formulas only; saturation negates that And and nothing else; all
/// three sources are retained in order.
#[test]
fn mixed_sources_saturate_without_the_envelope() {
    let target = one("The daemon shall respond.");
    let c = contract_formula(&target).unwrap();
    // Round 11 (change 3): the reliances are selected explicitly.
    let r1 = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The clock is monotonic."),
        &target,
    );
    let r2 = explicit_source(
        EdgeKind::GuaranteeDischarge,
        &one("The scheduler shall tick."),
        &target,
    );
    let env = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
        &target,
    )
    .unwrap();
    let paired = c.paired(&[r1.clone(), env.clone(), r2.clone()]);
    assert_eq!(
        paired.assumption,
        Formula::And {
            items: vec![r1.formula.clone(), r2.formula.clone()]
        }
    );
    assert_eq!(paired.sources, vec![r1.clone(), env.clone(), r2.clone()]);
    assert_eq!(
        paired.saturated(),
        Formula::Or {
            items: vec![
                paired.guarantee.clone(),
                Formula::Not {
                    inner: Box::new(Formula::And {
                        items: vec![r1.formula.clone(), r2.formula.clone()],
                    })
                },
            ],
        }
    );
}

/// Pairing again SUPERSEDES: the new source set replaces assumption and
/// sources wholesale — nothing is conjoined across pairings — and the empty
/// set is the identity.
#[test]
fn repairing_supersedes_and_empty_is_identity() {
    let target = one("The daemon shall respond.");
    let c = contract_formula(&target).unwrap();
    // Round 11 (change 3): the reliances are selected explicitly.
    let r1 = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The clock is monotonic."),
        &target,
    );
    let r2 = explicit_source(
        EdgeKind::OccurrenceReliance,
        &one("The link is up."),
        &target,
    );
    let first = c.paired(std::slice::from_ref(&r1));
    let second = first.paired(std::slice::from_ref(&r2));
    assert_eq!(second.assumption, r2.formula);
    assert_eq!(second.sources, vec![r2.clone()]);
    // Empty pairing returns the contract unchanged (sources included).
    assert_eq!(first.paired(&[]), first);
}

/// Pre-round-5 serialized contracts (no `sources` field) still deserialize;
/// a paired contract round-trips with its envelope retained.
#[test]
fn contract_formula_serde_compat() {
    let target = one("The daemon shall respond.");
    let c = contract_formula(&target).unwrap();
    let mut json = serde_json::to_value(&c).unwrap();
    json.as_object_mut().unwrap().remove("sources");
    let back: ContractFormula = serde_json::from_value(json).unwrap();
    assert_eq!(back.sources, Vec::new());
    assert_eq!(back.guarantee, c.guarantee);
    // Round-trip with an envelope in the sources.
    let env = AssumptionSource::for_guarantee(
        EdgeKind::AdmissibilityEnvelope,
        &one("The network may drop packets."),
        &target,
    )
    .unwrap();
    let paired = c.paired(std::slice::from_ref(&env));
    let json = serde_json::to_value(&paired).unwrap();
    assert_eq!(json["assumption"]["kind"], "top");
    assert_eq!(json["sources"][0]["kind"], "admissibility_envelope");
    let back: ContractFormula = serde_json::from_value(json).unwrap();
    assert_eq!(back, paired);
}

// =====================================================================================
// Change 4 — force-aware assess()
// =====================================================================================

/// A recommendation crossing a DESCRIPTION is advisory tension (the
/// Recommended arm wins over the description arm in the classification).
#[test]
fn recommendation_vs_description_conflict_is_advisory_tension() {
    let rec = one("The request should be logged.");
    let desc = one("The request is never logged.");
    assert_eq!(assess(&rec, &desc), Outcome::AdvisoryTension);
    assert_eq!(assess(&desc, &rec), Outcome::AdvisoryTension);
}

/// Description × description conflict is descriptive.
#[test]
fn description_vs_description_conflict_is_descriptive() {
    let a = one("The door is open.");
    let b = one("The door is never open.");
    assert_eq!(assess(&a, &b), Outcome::DescriptiveConflict);
}

/// Interval-driven conflict between a description and an obligation is
/// descriptive (one side carries no force), in both argument orders.
#[test]
fn interval_conflict_with_a_description_side_is_descriptive() {
    let described = one("The depth is between 1 and 2.");
    let required = one("The depth shall be at least 4.");
    assert_eq!(assess(&described, &required), Outcome::DescriptiveConflict);
    assert_eq!(assess(&required, &described), Outcome::DescriptiveConflict);
}

/// An unconditional obligation refines its conditional counterpart (the
/// assumption may weaken, the saturated guarantee strengthens); the
/// direction flag names which argument is concrete.
#[test]
fn unconditional_refines_conditional_with_direction() {
    let conditional = one("When the door opens, the pump shall stop.");
    let unconditional = one("The pump shall stop.");
    assert_eq!(
        assess(&conditional, &unconditional),
        Outcome::Refinement {
            concrete_is_a: false
        }
    );
    assert_eq!(
        assess(&unconditional, &conditional),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
}

/// Comparison containment surfaces as refinement through assess.
#[test]
fn comparison_containment_is_refinement() {
    let strict = one("The depth shall be greater than 3.");
    let loose = one("The depth shall be at least 3.");
    assert_eq!(
        assess(&strict, &loose),
        Outcome::Refinement {
            concrete_is_a: true
        }
    );
}

/// An unrelated pair is Unknown — Independent requires PROVEN non-
/// entailment both ways, which the structural rules almost never have.
#[test]
fn unrelated_pair_is_unknown_not_independent() {
    let a = one("The pump shall stop.");
    let b = one("The valve shall open.");
    assert_eq!(assess(&a, &b), Outcome::Unknown);
}

/// The force-blind core stays force-blind BY DESIGN: `should` and `shall`
/// claims still imply each other at the formula layer even though assess
/// legislates the pair Unknown.
#[test]
fn force_blind_implies_is_unchanged() {
    let should = claim("The pump should stop.");
    let shall = claim("The pump shall stop.");
    assert_eq!(implies(&should, &shall), Ternary::Yes);
    assert_eq!(implies(&shall, &should), Ternary::Yes);
    assert_eq!(
        assess(&one("The pump should stop."), &one("The pump shall stop.")),
        Outcome::Unknown
    );
}

/// Permissions and definitions stay out of the contract-vs-contract
/// judgments — even against themselves. SUPERSEDED IN PART (round 7,
/// change 6): a permission crossing the PROHIBITION of the same behavior
/// is no longer Unknown — the prohibition forbids exactly what the
/// permission admits, and round 7 names that envelope conflict. The
/// round-6 pin predates the envelope check; the permission-never-relates
/// doctrine survives for every other pair.
#[test]
fn permissions_and_definitions_always_assess_unknown() {
    let permission = one("The client may retry.");
    assert_eq!(assess(&permission, &permission), Outcome::Unknown);
    let definition = one("A session means a sequence of requests.");
    assert_eq!(assess(&definition, &definition), Outcome::Unknown);
    let prohibition = one("The client shall not retry.");
    // Round 7: the envelope conflict is now visible (change 6).
    assert_eq!(assess(&permission, &prohibition), Outcome::EnvelopeConflict);
}

/// Alternative order does not matter: `either A or B` ≡ `either B or A`
/// (same force, mutual implication through the Or).
#[test]
fn alternative_order_is_equivalent() {
    let ab = one("The server shall either accept the request or reject the request.");
    let ba = one("The server shall either reject the request or accept the request.");
    assert_eq!(assess(&ab, &ba), Outcome::Equivalent);
}

/// Every Outcome variant keeps its snake_case wire name.
#[test]
fn outcome_wire_names() {
    let tags = [
        (Outcome::HardContradiction, "hard_contradiction"),
        (Outcome::AdvisoryTension, "advisory_tension"),
        (Outcome::DescriptiveConflict, "descriptive_conflict"),
        (Outcome::Equivalent, "equivalent"),
        (Outcome::Independent, "independent"),
        (Outcome::Unknown, "unknown"),
    ];
    for (outcome, tag) in tags {
        let json = serde_json::to_value(outcome).unwrap();
        assert_eq!(json["kind"], tag);
        let back: Outcome = serde_json::from_value(json).unwrap();
        assert_eq!(back, outcome);
    }
}

// =====================================================================================
// Change 5 — intervals over the six operators
// =====================================================================================

/// Containment across all six operators, including the open/closed pins:
/// `greater than` / `less than` open, `at least` / `at most` closed,
/// `equal to` a point, `between` closed both ends.
#[test]
fn containment_matrix_over_the_six_ops() {
    let c = claim;
    // Open ⊆ closed at the same bound.
    assert_eq!(
        implies(
            &c("The depth is greater than 3."),
            &c("The depth is at least 3.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The depth is less than 3."),
            &c("The depth is at most 3.")
        ),
        Ternary::Yes
    );
    // Closed ⊄ open at the same bound: the endpoint escapes.
    assert_eq!(
        implies(
            &c("The depth is at least 3."),
            &c("The depth is greater than 3.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        implies(
            &c("The depth is at most 3."),
            &c("The depth is less than 3.")
        ),
        Ternary::Unknown
    );
    // Point ⊆ everything containing it; between ⊆ open bound strictly
    // outside it.
    assert_eq!(
        implies(
            &c("The depth is equal to 3."),
            &c("The depth is greater than 2.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The depth is between 1 and 2."),
            &c("The depth is less than 3.")
        ),
        Ternary::Yes
    );
    // between at the exact closed edge of an open bound does NOT fit.
    assert_eq!(
        implies(
            &c("The depth is between 1 and 3."),
            &c("The depth is less than 3.")
        ),
        Ternary::Unknown
    );
    // Same-op equivalences across lexeme spellings: word/number/decimal.
    assert_eq!(
        implies(
            &c("The depth is at most three."),
            &c("The depth is at most 3.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The depth is at most 3.0."),
            &c("The depth is at most 3.")
        ),
        Ternary::Yes
    );
}

/// Empty-intersection contradiction with boundary pins: touching CLOSED
/// endpoints are compatible (at most 3 / at least 3), a single open side
/// breaks the touch, point intervals collide only when equal.
#[test]
fn disjointness_boundary_pins() {
    let c = claim;
    assert_eq!(
        contradicts(
            &c("The depth is at most 3."),
            &c("The depth is at least 3.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &c("The depth is greater than 3."),
            &c("The depth is at most 3.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &c("The depth is less than 3."),
            &c("The depth is at least 3.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &c("The depth is equal to 3."),
            &c("The depth is greater than 3.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &c("The depth is equal to 3."),
            &c("The depth is equal to 5.")
        ),
        Ternary::Yes
    );
    // Same point: the same claim, provably NOT a contradiction.
    assert_eq!(
        contradicts(
            &c("The depth is equal to 3."),
            &c("The depth is equal to 3.")
        ),
        Ternary::No
    );
    // Overlap without containment stays Unknown.
    assert_eq!(
        contradicts(
            &c("The depth is less than 4."),
            &c("The depth is greater than 3.")
        ),
        Ternary::Unknown
    );
    // between/between: touching closed ends intersect.
    assert_eq!(
        contradicts(
            &c("The depth is between 1 and 3."),
            &c("The depth is between 3 and 5.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &c("The depth is between 1 and 2."),
            &c("The depth is between 3 and 5.")
        ),
        Ternary::Yes
    );
}

/// SUPERSEDED PIN (round 9, recorded): a written descending `between` is
/// now a PARSE ERROR (`descending_between`) — the round-6 doctrine let the
/// grammar freeze a silently-empty interval, and nobody writes one on
/// purpose, so the typo-shield moved to parse time. A HAND-BUILT empty
/// interval still behaves as this test always pinned: disjoint from
/// everything, itself included — the exclusion rule fires before the
/// syntactic-equality No — and vacuously implies every same-subject
/// comparison. The satisfiability machinery keeps covering hand-built
/// trees.
#[test]
fn descending_between_is_empty_and_self_contradicts() {
    assert!(matches!(
        parse("The latency is between 6 and 4."),
        Err(ParseError::DescendingBetween { .. })
    ));
    // Hand-built: swap the bounds of an accepted ascending `between`.
    let mut s = one("The latency is between 4 and 6.");
    let Core::Description {
        predicate: Predicate::Comparison(comparison),
        ..
    } = &mut s.core
    else {
        panic!("expected comparison description");
    };
    let upper = comparison.upper.take().unwrap();
    comparison.upper = Some(std::mem::replace(&mut comparison.value, upper));
    let empty = claim_formula(&s).unwrap();
    assert_eq!(contradicts(&empty, &empty), Ternary::Yes);
    assert_eq!(
        contradicts(&empty, &claim("The latency is equal to 5.")),
        Ternary::Yes
    );
    // The empty interval is contained everywhere — vacuous implication.
    assert_eq!(
        implies(&empty, &claim("The latency is at most 100.")),
        Ternary::Yes
    );
}

/// Unit gating: mismatched units, present-vs-missing units, and
/// case-insensitive unit equality.
#[test]
fn unit_gating_pins() {
    let c = claim;
    assert_eq!(
        contradicts(
            &c("The lag is at most 3 seconds."),
            &c("The lag is at least 5.")
        ),
        Ternary::Unknown
    );
    assert_eq!(
        contradicts(
            &c("The lag is at most 3 Seconds."),
            &c("The lag is at least 5 seconds.")
        ),
        Ternary::Yes
    );
    // Decimals ground exactly.
    assert_eq!(
        contradicts(
            &c("The lag is at most 2.5 seconds."),
            &c("The lag is at least 2.6 seconds.")
        ),
        Ternary::Yes
    );
    assert_eq!(
        contradicts(
            &c("The lag is at most 2.5 seconds."),
            &c("The lag is at least 2.5 seconds.")
        ),
        Ternary::Unknown
    );
}

/// Numbers are UNSIGNED lexemes: `-5` is no numeral, so it parses as a
/// noun-phrase measure (head `-5`) and never grounds an interval — every
/// relation over it is honestly Unknown, never a sign-blind Yes.
#[test]
fn negative_numbers_are_np_measures_and_never_ground() {
    let s = one("The temperature is at most -5.");
    let Core::Description {
        predicate: Predicate::Comparison(comparison),
        ..
    } = &s.core
    else {
        panic!("expected comparison description, got {:?}", s.core);
    };
    assert!(
        matches!(&comparison.value, Measure::Np { np } if np.heads() == vec!["-5"]),
        "`-5` must be an opaque noun-phrase measure, got {:?}",
        comparison.value
    );
    let a = claim("The temperature is at most -5.");
    let b = claim("The temperature is at least -3.");
    assert_eq!(contradicts(&a, &b), Ternary::Unknown);
    assert_eq!(implies(&a, &b), Ternary::Unknown);
}

// =====================================================================================
// Change 6 — VP alternatives
// =====================================================================================

/// Alternatives carrying particles, manner, roles, and objects round-trip
/// through render, reshape into per-alternative skeleton atoms, and build an
/// Or formula of matching width.
#[test]
fn rich_alternatives_round_trip_and_reshape() {
    let s = one(
        "The daemon shall either shut down gracefully or flush the buffer within 5 seconds or halt.",
    );
    let Core::Deontic {
        vp: VpGroup::Alternatives { items },
        ..
    } = &s.core
    else {
        panic!("expected alternatives, got {:?}", s.core);
    };
    assert_eq!(items.len(), 3);
    assert_eq!(items[0].verb, "shut");
    assert_eq!(items[0].particle.as_deref(), Some("down"));
    assert_eq!(items[0].manner, vec!["gracefully".to_string()]);
    assert_eq!(items[1].verb, "flush");
    assert_eq!(items[1].roles.len(), 1);
    assert_eq!(items[2].verb, "halt");
    // Canonical render re-parses to the same core.
    let rendered = s.render();
    assert_eq!(
        one(&rendered).core,
        s.core,
        "render round-trip for {rendered:?}"
    );
    // Skeleton: one atom per alternative, in surface order.
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.atoms.len(), 3);
    assert_eq!(sk.atoms[0].words, vec!["shut", "down"]);
    assert_eq!(sk.atoms[0].manner, vec!["gracefully"]);
    assert_eq!(sk.atoms[2].words, vec!["halt"]);
    // Formula: Or of three behavior atoms; skeleton atoms and formula atoms
    // agree.
    let Formula::Or { items: disjuncts } = claim_formula(&s).unwrap() else {
        panic!("expected Or over alternatives");
    };
    assert_eq!(disjuncts.len(), 3);
    for (disjunct, atom) in disjuncts.iter().zip(&sk.atoms) {
        let Formula::Atom {
            atom: AtomRef::Behavior { behavior },
        } = disjunct
        else {
            panic!("expected behavior atom, got {disjunct:?}");
        };
        assert_eq!(
            &behavior.atom, atom,
            "formula and skeleton must digest alike"
        );
    }
    // Serde round-trips the whole sentence.
    let json = serde_json::to_value(&s).unwrap();
    let back: Sentence = serde_json::from_value(json).unwrap();
    assert_eq!(back, s);
}

/// A subject `no` over alternatives composes as ¬(A ∨ B) — the negation the
/// grammar refuses at the `not` site is coherent from the subject site, and
/// each anchor re-parses with its own alternative as sole verb phrase.
#[test]
fn no_subject_alternatives_negate_the_disjunction() {
    let f = claim("No daemon shall either sleep or halt.");
    let Formula::Not { inner } = &f else {
        panic!("expected Not, got {f:?}")
    };
    let Formula::Or { items } = &**inner else {
        panic!("expected Or, got {inner:?}")
    };
    assert_eq!(items.len(), 2);
    let anchor = |f: &Formula| match f {
        Formula::Atom {
            atom: AtomRef::Behavior { behavior },
        } => behavior.source.clone(),
        other => panic!("expected behavior atom, got {other:?}"),
    };
    assert_eq!(anchor(&items[0]), "no daemon shall sleep");
    assert_eq!(anchor(&items[1]), "no daemon shall halt");
    // The anchors re-parse (the § Anchors consumption rule).
    for f in items {
        let source = anchor(f);
        parse(&format!("{source}.")).expect("anchor re-parses as a sentence core");
    }
}

/// A coordinated subject over alternatives distributes: And over per-item
/// Or groups, four atoms in all.
#[test]
fn coordinated_subject_distributes_over_alternatives() {
    let f = claim("The pump and the valve shall either stop or drain.");
    let Formula::And { items } = &f else {
        panic!("expected And, got {f:?}")
    };
    assert_eq!(items.len(), 2);
    for item in items {
        let Formula::Or { items: alts } = item else {
            panic!("expected Or, got {item:?}")
        };
        assert_eq!(alts.len(), 2);
    }
    // Doing one alternative discharges the disjunction for that subject.
    assert_eq!(
        implies(&claim("The pump shall stop."), items.first().unwrap()),
        Ternary::Yes
    );
}

/// Negation rejection across modals: `shall not either` and `should not
/// either` are NegatedAlternatives; `may not either` stays the earlier
/// AmbiguousModal (pinned precedence).
#[test]
fn negated_alternatives_rejection_precedence() {
    assert_eq!(
        parse("The server shall not either accept the request or reject the request."),
        Err(ParseError::NegatedAlternatives)
    );
    assert_eq!(
        parse("The client should not either retry or abort."),
        Err(ParseError::NegatedAlternatives)
    );
    assert_eq!(
        parse("The client may not either retry or abort."),
        Err(ParseError::AmbiguousModal)
    );
}

/// Disambiguation in the remaining positions: subject `either` stays the NP
/// group marker; `must` opens alternatives like `shall`; a bare trailing
/// `either` is stray material.
#[test]
fn either_disambiguation_in_other_positions() {
    // Subject position: NP coordination marker, untouched by round 6.
    let s = one("Either the pump or the valve shall stop.");
    let Core::Deontic {
        subject,
        vp: VpGroup::Single(_),
        ..
    } = &s.core
    else {
        panic!("expected single-vp deontic, got {:?}", s.core);
    };
    assert!(matches!(
        subject,
        NpGroup::Coordinated { conj: Conj::Or, marker: Some(GroupMarker::Either), items } if items.len() == 2
    ));
    // `must` and `should` take alternatives through the same slot.
    let s = one("The daemon must either fsync the journal or halt.");
    assert!(matches!(
        &s.core,
        Core::Deontic {
            vp: VpGroup::Alternatives { .. },
            modal: Modal::Must,
            ..
        }
    ));
    let s = one("The daemon should either fsync the journal or halt.");
    assert!(matches!(
        &s.core,
        Core::Deontic {
            vp: VpGroup::Alternatives { .. },
            modal: Modal::Should,
            ..
        }
    ));
    // A modal-final `either` is diagnosed, not guessed.
    assert_eq!(
        parse("The pump shall either."),
        Err(ParseError::UnexpectedTokens {
            token: "either".into()
        })
    );
    // `be`-complement items are legal alternatives on both sides.
    let s = one("The daemon shall either be idle or be busy.");
    let sk = skeleton(&s).unwrap();
    assert_eq!(sk.atoms.len(), 2);
    assert_eq!(sk.atoms[0].words, vec!["idle"]);
    assert_eq!(sk.atoms[1].words, vec!["busy"]);
}

/// One concrete act discharges a three-way alternative.
#[test]
fn single_act_discharges_three_way_alternative() {
    let alternative = claim(
        "The server shall either accept the request or reject the request or queue the request.",
    );
    assert_eq!(
        implies(&claim("The server shall queue the request."), &alternative),
        Ternary::Yes
    );
}

/// FINDING (critical, FIXED in the round-6 follow-up): a determiner-led
/// TAIL alternative used to slip through `parse_vp`, which accepted `the`
/// as an open-class VERB: `The server shall either notify the admin or the
/// owner.` parsed as alternatives [notify(the admin), the(owner)] — an
/// accepted-but-wrong tree whose second "behavior" is the word `the`. (Root
/// cause was older — `The pump shall the valve.` also parsed with verb
/// `the`.) Fixed: a determiner at verb position is now
/// `ParseError::DeterminerAsVerb` wherever a verb phrase starts.
#[test]
fn determiner_led_alternative_tail_must_not_become_a_verb() {
    let no_det_verb = |input: &str| match parse(input) {
        Err(_) => {}
        Ok(spec) => {
            for sentence in &spec.sentences {
                if let Core::Deontic { vp, .. } = &sentence.core {
                    for item in vp.items() {
                        assert!(
                            !matches!(
                                item.verb.to_ascii_lowercase().as_str(),
                                "the" | "a" | "an" | "each" | "every" | "all" | "any" | "no"
                            ),
                            "{input:?} accepted a determiner as a verb: {item:?}"
                        );
                    }
                }
            }
        }
    };
    no_det_verb("The server shall either notify the admin or the owner.");
    no_det_verb("The pump shall the valve.");
}

// =====================================================================================
// Change 7 — plain-NP `with` rejected everywhere
// =====================================================================================

/// `with` is closed in every NP-collection context the round-6 doc names —
/// beyond the positions round6.rs already pins: object NPs, role NPs,
/// relative bodies, exceptions, purposes, and definiens.
#[test]
fn with_is_rejected_in_every_remaining_position() {
    for input in [
        // Object position (role-preposition path, kept from round 5).
        "The daemon shall pack the box with the label.",
        // Role NP.
        "The daemon shall send the report to the user with the token.",
        // Relative body object.
        "The file that ships with the manual shall be listed.",
        // Exception clause.
        "The pump shall stop, unless the operator with the badge is present.",
        // Purpose clause (`so that`).
        "The pump shall stop, so that the tank with the valve drains.",
        // Purpose verb phrase (`in order to`).
        "The daemon shall log the request, in order to comply with the policy.",
        // Definiens.
        "A bundle means a folder with the flag.",
        // Description subject and coordinated subject item.
        "The node with the lease is primary.",
        "The pump and the tank with the valve shall drain.",
    ] {
        assert_eq!(
            parse(input),
            Err(ParseError::WithIsAmbiguous),
            "{input:?} must be the round-6 WithIsAmbiguous rejection"
        );
    }
}

/// The backtick escape admits noun uses of `with` in object position, and
/// the canonical render preserves the backticks losslessly.
#[test]
fn backticked_with_stays_an_ordinary_word() {
    let s = one("The daemon shall document the `with` clause.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("expected deontic")
    };
    let object = vp.single().unwrap().object.as_ref().unwrap();
    match object {
        NpGroup::Single(np) => {
            assert_eq!(np.modifiers, vec!["`with`".to_string()]);
            assert_eq!(np.head, "clause");
        }
        other => panic!("expected single NP, got {other:?}"),
    }
    let rendered = s.render();
    assert!(
        rendered.contains("`with`"),
        "render keeps the backticks: {rendered:?}"
    );
    assert_eq!(one(&rendered).core, s.core);
}

// =====================================================================================
// Change 8 — bounded durations
// =====================================================================================

/// SUPERSEDED PIN (round 6 follow-up): this test used to pin that a bound
/// opener after `within` silently parses as a counted noun-phrase measure
/// (`at least 5` as determiner of `seconds`) that never grounds an
/// interval — an accepted-but-misleading tree, and an asymmetry with the
/// `for` position which errors loudly. That shape is now LEGISLATED AWAY:
/// `within` + bound opener is rejected (`WithinTakesPlainMeasure` — a
/// deadline is already an upper bound; bounded measures belong to `for`
/// durations). The plain quantity stays the only `within` measure form
/// with interval grounding.
#[test]
fn within_bound_openers_become_np_measures() {
    // The legislated plain form.
    let s = one("The daemon shall reply within 5 seconds.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("expected deontic")
    };
    assert_eq!(
        vp.single().unwrap().roles[0],
        RolePp::Deadline(Measure::Quantity {
            number: "5".into(),
            unit: Some("seconds".into())
        })
    );
    // Every bound opener after `within` is rejected — with a number, with a
    // noun phrase, and as `between`.
    for input in [
        "The daemon shall reply within at least 5 seconds.",
        "The daemon shall reply within at most 5 seconds.",
        "The daemon shall reply within greater than 5 seconds.",
        "The daemon shall reply within less than 5 seconds.",
        "The daemon shall reply within between 5 and 10 seconds.",
        "The daemon shall reply within at least the limit.",
    ] {
        assert_eq!(
            parse(input).unwrap_err(),
            ParseError::WithinTakesPlainMeasure,
            "{input:?}"
        );
    }
    // A plain NP measure survives: `within the timeout` is still a value
    // name.
    let s = one("The batch shall complete within the timeout.");
    let Core::Deontic { vp, .. } = &s.core else {
        panic!("expected deontic")
    };
    assert!(matches!(
        &vp.single().unwrap().roles[0],
        RolePp::Deadline(Measure::Np { .. })
    ));
}

/// Directionality of every bounded form under `for`, composed with the
/// round-5 legislated plain directions.
#[test]
fn bounded_duration_directionality() {
    let c = claim;
    // at most: tighter cap implies looser cap.
    assert_eq!(
        implies(
            &c("The pump shall run for at most 5 seconds."),
            &c("The pump shall run for at most 10 seconds."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The pump shall run for at most 10 seconds."),
            &c("The pump shall run for at most 5 seconds."),
        ),
        Ternary::Unknown
    );
    // greater than (open) implies at least (closed) at the same bound.
    assert_eq!(
        implies(
            &c("The daemon shall keep the lease for greater than 3 days."),
            &c("The daemon shall keep the lease for at least 3 days."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The daemon shall keep the lease for at least 3 days."),
            &c("The daemon shall keep the lease for greater than 3 days."),
        ),
        Ternary::Unknown
    );
    // between containment, decimals included.
    assert_eq!(
        implies(
            &c("The pump shall run for between 2.5 and 3.5 seconds."),
            &c("The pump shall run for between 2 and 4 seconds."),
        ),
        Ternary::Yes
    );
    // Plain `for n` is [n, ∞) (round 5): it meets at-least but NOT at-most.
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for 30 days."),
            &c("The daemon shall retain the log for at least 10 days."),
        ),
        Ternary::Yes
    );
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for 3 days."),
            &c("The daemon shall retain the log for at most 10 days."),
        ),
        Ternary::Unknown
    );
    // Unit vs no unit never grounds.
    assert_eq!(
        implies(
            &c("The daemon shall retain the log for at least 30."),
            &c("The daemon shall retain the log for at least 10 days."),
        ),
        Ternary::Unknown
    );
}

/// SUPERSEDED PIN (round 7, change 7): role-measure DISJOINTNESS is now a
/// contradiction rule. The round-6 pin held this pair Unknown because the
/// exclusion rule covered comparison predicates only — a documented
/// asymmetry, not a doctrine about role measures themselves. Round 7
/// retires it with justification: role intervals already ground
/// IMPLICATION (containment), so the same interval reading proving an
/// empty intersection over one unit is a proof by the same trusted rule.
/// `for at least 30 days` vs `for less than 10 days` now contradicts at
/// Yes, and the binding pair assesses as a hard contradiction.
#[test]
fn disjoint_duration_bounds_now_contradict() {
    let a = claim("The daemon shall retain the log for at least 30 days.");
    let b = claim("The daemon shall retain the log for less than 10 days.");
    assert_eq!(contradicts(&a, &b), Ternary::Yes);
    assert_eq!(
        assess(
            &one("The daemon shall retain the log for at least 30 days."),
            &one("The daemon shall retain the log for less than 10 days."),
        ),
        Outcome::HardContradiction
    );
}

/// BoundedMeasure serializes with its snake_case tag and round-trips; the
/// deprecated-field compatibility of round 6's widened digests holds (old
/// JSON without `full` still deserializes).
#[test]
fn bounded_measure_and_digest_serde() {
    let s = one("The daemon shall retain the log for between 5 and 10 days.");
    let sk = skeleton(&s).unwrap();
    let value = &sk.atoms[0].roles[0].value;
    assert!(matches!(
        value,
        RoleValue::BoundedMeasure { op: ComparisonOp::Between, upper: Some(u), .. } if u == "10"
    ));
    let json = serde_json::to_value(value).unwrap();
    assert_eq!(json["kind"], "bounded_measure");
    assert_eq!(json["op"], "between");
    assert_eq!(json["number"], "5");
    assert_eq!(json["upper"], "10");
    let back: RoleValue = serde_json::from_value(json).unwrap();
    assert_eq!(&back, value);
    // Old skeleton JSON without the round-6 `full` fields still loads.
    let sk = skeleton(&one("The daemon shall persist the node.")).unwrap();
    let mut json = serde_json::to_value(&sk).unwrap();
    json["subject"].as_object_mut().unwrap().remove("full");
    json["atoms"][0]["objects"][0]
        .as_object_mut()
        .unwrap()
        .remove("full");
    let back: Skeleton = serde_json::from_value(json).unwrap();
    assert_eq!(back.subject.full, "");
    assert_eq!(back.atoms[0].objects[0].full, "");
    // An atom without a comparison omits the key entirely.
    let json = serde_json::to_value(&sk.atoms[0]).unwrap();
    assert!(
        json.get("comparison").is_none(),
        "None comparison must not serialize"
    );
}

// =====================================================================================
// Totality — seeded fuzz over the round-6 surface
// =====================================================================================

/// Deterministic token soup mixing `either`/`or`, `with`, bounded measures,
/// backticks, and the round-6 keywords: parse must never panic; every
/// accepted sentence must render canonically, re-parse, re-render to a fixed
/// point, and survive every derivation (skeleton, formulas, keys, assess).
#[test]
fn seeded_fuzz_over_round6_vocabulary_is_total() {
    const VOCAB: &[&str] = &[
        "the", "a", "no", "each", "either", "or", "and", "both", "with", "for", "within", "at",
        "least", "most", "between", "greater", "less", "than", "equal", "to", "5", "10", "2.5",
        "zero", "ten", "-5", "seconds", "days", "pump", "valve", "daemon", "request", "owner",
        "file", "shall", "must", "may", "should", "not", "be", "is", "are", "never", "stop",
        "notify", "of", "that", "who", "logged", "out", "down", "quickly", "`with`", "unless",
        "when", "while", "so", "means", "able", "per", "by", "using", ",", ".",
    ];
    let mut state: u64 = 0x5eed_c0de_2026_0707;
    let mut next = move || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 33) as usize
    };
    let mut accepted: Vec<Sentence> = Vec::new();
    for _ in 0..600 {
        let len = 1 + next() % 14;
        let mut input = String::new();
        for i in 0..len {
            let word = VOCAB[next() % VOCAB.len()];
            if i > 0 && word != "," && word != "." {
                input.push(' ');
            }
            input.push_str(word);
        }
        input.push('.');
        // Totality: one parse or one error, never a panic.
        let Ok(spec) = parse(&input) else { continue };
        for sentence in spec.sentences {
            // Canonical render is stable: it re-parses, and re-rendering is
            // a fixed point.
            let rendered = sentence.render();
            let again = parse(&rendered)
                .unwrap_or_else(|e| panic!("canonical render must re-parse: {rendered:?} → {e}"));
            let re_rendered = again.sentences[0].render();
            assert_eq!(
                re_rendered, rendered,
                "canonical render must be a fixed point for {:?}",
                sentence.source
            );
            // Every derivation is total on accepted sentences.
            let _ = so_lang::semantics::speech_act(&sentence);
            let _ = so_lang::semantics::denote(&sentence);
            let _ = skeleton(&sentence);
            let _ = so_lang::semantics::subject_keys(&sentence);
            let _ = claim_formula(&sentence);
            if let Some(c) = contract_formula(&sentence) {
                let _ = c.saturated();
            }
            accepted.push(sentence);
        }
    }
    assert!(
        accepted.len() > 10,
        "the fuzz vocabulary should accept a meaningful sample, got {}",
        accepted.len()
    );
    // Relation engine totality over accepted pairs (windowed).
    for pair in accepted.windows(2) {
        let _ = assess(&pair[0], &pair[1]);
        if let (Some(a), Some(b)) = (contract_formula(&pair[0]), contract_formula(&pair[1])) {
            let _ = implies(&a.guarantee, &b.guarantee);
            let _ = contradicts(&a.guarantee, &b.guarantee);
            let _ = refines(&a, &b);
        }
    }
}
