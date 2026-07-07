//! Serialization conformance — the documented serde claims hold at runtime.
//!
//! `docs/grammar/semantics.md` §Serialization states that the syntax tree and
//! every derived view serialize with serde. Internally tagged enums reject
//! newtype variants holding sequences or primitives at *runtime*, so the two
//! shapes that used to hit that wall — open-word predicates
//! (`Predicate::Words`) and count determiners (`Det::AtLeast`/`AtMost`/
//! `Exactly`) — are pinned here as JSON round trips.

use so_lang::ast::{Det, Sentence};
use so_lang::formula::{applicability, claim_formula, contract_formula, Formula};
use so_lang::parse::parse;
use so_lang::semantics::{denote, ingest_contract, skeleton, Denotation, IngestContract, Skeleton};

fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
    assert_eq!(spec.sentences.len(), 1);
    spec.sentences.into_iter().next().unwrap()
}

/// A JSON round trip: serialize, deserialize, compare.
fn json_roundtrip<T>(value: &T) -> serde_json::Value
where
    T: serde::Serialize + serde::de::DeserializeOwned + PartialEq + std::fmt::Debug,
{
    let json = serde_json::to_value(value)
        .unwrap_or_else(|e| panic!("must serialize, got: {e} for {value:?}"));
    let back: T = serde_json::from_value(json.clone())
        .unwrap_or_else(|e| panic!("must deserialize, got: {e} from {json}"));
    assert_eq!(&back, value, "JSON round trip must be lossless");
    json
}

#[test]
fn open_word_predicates_serialize() {
    // A description whose predicate is open words — the common case.
    let sentence = one("Requests are logged.");
    let json = json_roundtrip(&sentence);
    let predicate = &json["core"]["predicate"];
    assert_eq!(predicate["kind"], "words");
    assert_eq!(predicate["words"], serde_json::json!(["logged"]));
}

#[test]
fn count_determiners_serialize() {
    let sentence = one("The daemon shall retain at least 3 copies.");
    let (det, expected) = match &sentence.core {
        so_lang::ast::Core::Deontic { vp, .. } => match vp.single().unwrap().object.as_ref().unwrap() {
            so_lang::ast::NpGroup::Single(np) => {
                (np.det.clone().unwrap(), Det::AtLeast { n: 3 })
            }
            other => panic!("expected single object, got {other:?}"),
        },
        other => panic!("expected deontic core, got {other:?}"),
    };
    assert_eq!(det, expected);
    let json = json_roundtrip(&sentence);
    let det = &json["core"]["vp"]["object"]["det"];
    assert_eq!(det["kind"], "at_least");
    assert_eq!(det["n"], 3);
}

#[test]
fn derived_views_with_open_word_predicates_serialize() {
    for input in [
        "Requests are logged.",
        "The daemon shall not store derived views.",
        // Round 2, change 3: one event per `and` trigger group.
        "When the order ships and the payment is cleared, the system shall issue the receipt.",
        "At least 3 nodes shall sync.",
    ] {
        let sentence = one(input);
        let denotation: Denotation = denote(&sentence);
        json_roundtrip(&denotation);
        if let Some(contract) = ingest_contract(&sentence) {
            let _: &IngestContract = &contract;
            json_roundtrip(&contract);
        }
        if let Some(sk) = skeleton(&sentence) {
            let _: &Skeleton = &sk;
            json_roundtrip(&sk);
        }
    }
}

#[test]
fn skeleton_v3_object_and_role_quantifiers_serialize() {
    // Round 3, change 3: objects and Heads role values carry quantifiers.
    let sentence = one("The daemon shall log no request to each subscriber.");
    let sk = skeleton(&sentence).expect("skeleton");
    let json = json_roundtrip(&sk);
    let object = &json["atoms"][0]["objects"][0];
    assert_eq!(object["quantifier"]["kind"], "negative");
    assert_eq!(object["head"], "request");
    let role = &json["atoms"][0]["roles"][0];
    assert_eq!(role["kind"], "recipient");
    assert_eq!(role["value"]["kind"], "heads");
    assert_eq!(role["value"]["items"][0]["quantifier"]["kind"], "universal");
    assert_eq!(role["value"]["items"][0]["head"], "subscriber");
}

#[test]
fn clause_particles_and_roles_serialize() {
    // Round 3, changes 1–2: the verbal clause body's particle and roles.
    let sentence = one("When the user logs out after the timer expires, the session shall end.");
    let json = json_roundtrip(&sentence);
    let clause = &json["frames"]["trigger"]["clause"]["items"][0];
    assert_eq!(clause["body"]["kind"], "verbal");
    assert_eq!(clause["body"]["particle"], "out");
    assert_eq!(clause["body"]["roles"][0]["role"], "after");
    json_roundtrip(&skeleton(&sentence).expect("skeleton"));
}

#[test]
fn formulas_serialize() {
    // Round 3, change 4: the formula layer follows the same serde
    // discipline (struct variants, internal tags).
    let sentence = one(
        "If the disk fails or the link drops, then the daemon shall alert, \
         unless the override is active.",
    );
    let app: Formula = applicability(&sentence);
    let json = json_roundtrip(&app);
    assert_eq!(json["kind"], "and");
    assert_eq!(json["items"][0]["kind"], "or");
    assert_eq!(json["items"][0]["items"][0]["kind"], "atom");
    assert_eq!(json["items"][0]["items"][0]["atom"]["kind"], "guard");
    assert_eq!(json["items"][1]["kind"], "not");
    json_roundtrip(&claim_formula(&sentence).expect("claim"));
    let contract = contract_formula(&sentence).expect("contract");
    let json = json_roundtrip(&contract);
    assert_eq!(json["assumption"]["kind"], "top");
    assert_eq!(json["guarantee"]["kind"], "or");
    json_roundtrip(&contract.saturated());
    // The behavior atom's tag, on the guarantee's claim disjunct.
    assert_eq!(json["guarantee"]["items"][1]["atom"]["kind"], "behavior");
}
