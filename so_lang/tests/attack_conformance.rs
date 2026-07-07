//! Adversarial conformance audit against LANGUAGE-SPEC.md (v0.2.0).
//!
//! Every expectation here was re-derived from the spec text independently of
//! the implementer's own tests. Tests that failed against the audited
//! implementation were kept `#[ignore]`d until their findings were resolved;
//! all are now active, either asserting the fixed behavior or pinning the
//! deliberate resolution of a spec self-inconsistency (see the `x*` tests).

use so_lang::ast::*;
use so_lang::parse::{parse, ParseError};
use so_lang::semantics::{self, Claim, Denotation, Force, Polarity, Resolution, SpeechAct};

// ---- helpers ------------------------------------------------------------------

/// Parse an input expected to hold exactly one sentence.
fn one(input: &str) -> Sentence {
    let spec = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
    assert_eq!(spec.sentences.len(), 1, "expected one sentence in {input:?}");
    spec.sentences.into_iter().next().unwrap()
}

fn deontic(s: &Sentence) -> (&NpGroup, Modal, bool, &Vp) {
    match &s.core {
        Core::Deontic { subject, modal, negated, vp } => {
            (subject, *modal, *negated, vp.single().expect("single vp fixture"))
        }
        other => panic!("expected deontic core, got {other:?}"),
    }
}

fn description(s: &Sentence) -> (&NpGroup, Copula, Option<DescriptionAdverb>, &Predicate) {
    match &s.core {
        Core::Description { subject, copula, adverb, predicate, .. } => {
            (subject, *copula, *adverb, predicate)
        }
        other => panic!("expected description core, got {other:?}"),
    }
}

fn definition(s: &Sentence) -> (&Np, &Definiens) {
    match &s.core {
        Core::Definition { term, definiens } => (term, definiens),
        other => panic!("expected definition core, got {other:?}"),
    }
}

fn single(group: &NpGroup) -> &Np {
    match group {
        NpGroup::Single(np) => np,
        other => panic!("expected single np, got {other:?}"),
    }
}

// ---- acceptance corpus, re-derived ---------------------------------------------

#[test]
fn a01_simple_obligation() {
    let s = one("The pump shall stop.");
    assert_eq!(s.source, "The pump shall stop.");
    assert!(s.frames.is_empty());
    assert!(s.exception.is_none() && s.purpose.is_none());
    let (subject, modal, negated, vp) = deontic(&s);
    assert_eq!(single(subject).det, Some(Det::The));
    assert_eq!(single(subject).head, "pump");
    assert_eq!(modal, Modal::Shall);
    assert!(!negated);
    assert_eq!(vp.verb, "stop");
    assert!(vp.object.is_none() && vp.roles.is_empty() && vp.complement.is_none());
}

#[test]
fn a02_terminator_optional_and_source_exact() {
    let s = one("The pump shall stop");
    assert_eq!(s.source, "The pump shall stop");
    assert_eq!(deontic(&s).3.verb, "stop");
    // Surrounding whitespace is trimmed from the source slice.
    let s = one("   The pump shall stop.   ");
    assert_eq!(s.source, "The pump shall stop.");
}

#[test]
fn a03_number_word_stored_as_written() {
    let s = one("The sales amount is always greater than zero.");
    let (subject, copula, adverb, predicate) = description(&s);
    assert_eq!(single(subject).modifiers, vec!["sales".to_string()]);
    assert_eq!(single(subject).head, "amount");
    assert_eq!(copula, Copula::Is);
    assert_eq!(adverb, Some(DescriptionAdverb::Always));
    assert_eq!(
        *predicate,
        Predicate::Comparison(Comparison {
            op: ComparisonOp::GreaterThan,
            value: Measure::Quantity { number: "zero".into(), unit: None },
            upper: None,
        })
    );
}

#[test]
fn a04_event_trigger_copular_clause() {
    let s = one("When the order is submitted, the system shall record the total.");
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    assert_eq!(trigger.kind, TriggerKind::Event);
    assert_eq!(trigger.keyword, "When");
    assert_eq!(single(&trigger.clause.items[0].subject).head, "order");
    match &trigger.clause.items[0].body {
        ClauseBody::Copular { copula: ClauseCopula::Is, predicate, ..  } => {
            assert_eq!(*predicate, Predicate::Words { words: vec!["submitted".into()] });
        }
        other => panic!("expected copular body, got {other:?}"),
    }
    assert!(matches!(s.core, Core::Deontic { .. }));
}

#[test]
fn a05_contingency_with_then_and_be_complement() {
    let s = one("If the balance is negative, then the account shall be frozen.");
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    assert_eq!(trigger.kind, TriggerKind::Contingency);
    assert_eq!(trigger.keyword, "If");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.verb, "be");
    assert_eq!(vp.complement, Some(Predicate::Words { words: vec!["frozen".into()] }));
    assert!(vp.object.is_none());
}

#[test]
fn a06_then_is_optional_and_trees_agree() {
    let with = one("If the balance is negative, then the account shall be frozen.");
    let without = one("If the balance is negative, the account shall be frozen.");
    assert_eq!(with.frames, without.frames, "`then` is recorded implicitly");
    assert_eq!(with.core, without.core);
}

#[test]
fn a07_state_frame_plus_trigger_surface_casing() {
    let s = one(
        "While the engine is running, when the temperature exceeds the limit, \
         the controller shall open the valve.",
    );
    assert_eq!(s.frames.states.len(), 1);
    assert_eq!(s.frames.states[0].keyword, "While");
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    assert_eq!(trigger.kind, TriggerKind::Event);
    assert_eq!(trigger.keyword, "when", "surface casing must be preserved");
    match &trigger.clause.items[0].body {
        ClauseBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "exceeds");
            assert_eq!(single(object.as_ref().expect("object")).head, "limit");
        }
        other => panic!("expected verbal body, got {other:?}"),
    }
}

#[test]
fn a08_scoped_definition_keeps_where_casing() {
    let s = one("where the premium plan is enabled, a workspace means a shared folder.");
    assert_eq!(s.frames.scopes.len(), 1);
    assert_eq!(s.frames.scopes[0].keyword, "where");
    let (term, definiens) = definition(&s);
    assert_eq!(term.det, Some(Det::A));
    assert_eq!(term.head, "workspace");
    match definiens {
        Definiens::Np { np, roles } => {
            let np = single(np);
            assert_eq!(np.det, Some(Det::A));
            assert_eq!(np.modifiers, vec!["shared".to_string()]);
            assert_eq!(np.head, "folder");
            assert!(roles.is_empty());
        }
        other => panic!("expected np definiens, got {other:?}"),
    }
}

#[test]
fn a09_definiens_of_chain_and_source_role() {
    let s = one("A session means a sequence of requests from one client.");
    let (term, definiens) = definition(&s);
    assert_eq!(term.head, "session");
    match definiens {
        Definiens::Np { np, roles } => {
            let np = single(np);
            assert_eq!(np.det, Some(Det::A));
            assert_eq!(np.head, "sequence");
            assert_eq!(np.of.as_ref().expect("of-chain").head, "requests");
            match roles.as_slice() {
                [RolePp::Source(source)] => {
                    let source = single(source);
                    assert_eq!(source.det, None, "`one` is a modifier, not a determiner");
                    assert_eq!(source.modifiers, vec!["one".to_string()]);
                    assert_eq!(source.head, "client");
                }
                other => panic!("expected exactly one Source role, got {other:?}"),
            }
        }
        other => panic!("expected np definiens, got {other:?}"),
    }
}

#[test]
fn a10_permission() {
    let s = one("The client may retry.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Permission);
    let (_, modal, negated, vp) = deontic(&s);
    assert_eq!(modal, Modal::May);
    assert!(!negated);
    assert_eq!(vp.verb, "retry");
}

#[test]
fn a11_prohibition() {
    let s = one("The daemon shall not store derived views.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Prohibition);
    let (_, modal, negated, vp) = deontic(&s);
    assert_eq!(modal, Modal::Shall);
    assert!(negated);
    assert_eq!(vp.verb, "store");
    assert_eq!(single(vp.object.as_ref().expect("object")).head, "views");
}

#[test]
fn a12_recommendation_with_coordinated_object() {
    let s = one("The tracing library should install TraceContext and Baggage propagators.");
    assert_eq!(semantics::speech_act(&s), SpeechAct::Recommendation);
    let (_, modal, _, vp) = deontic(&s);
    assert_eq!(modal, Modal::Should);
    match vp.object.as_ref().expect("object") {
        NpGroup::Coordinated { conj: Conj::And, marker: None, items } => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0].head, "TraceContext");
            assert_eq!(items[1].modifiers, vec!["Baggage".to_string()]);
            assert_eq!(items[1].head, "propagators");
        }
        other => panic!("expected and-coordination, got {other:?}"),
    }
}

#[test]
fn a13_deadline_measure_with_unit() {
    let s = one("When an order is submitted, the system shall record the order within 5 seconds.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(
        vp.roles,
        vec![RolePp::Deadline(Measure::Quantity {
            number: "5".into(),
            unit: Some("seconds".into()),
        })]
    );
}

#[test]
fn a14_recipient_then_means_in_surface_order() {
    let s = one("The gateway shall send the receipt to the customer via TLS.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().expect("object")).head, "receipt");
    match vp.roles.as_slice() {
        [RolePp::Recipient(recipient), RolePp::Means { marker: MeansMarker::Via, np }] => {
            assert_eq!(single(recipient).head, "customer");
            assert_eq!(single(np).head, "TLS");
        }
        other => panic!("expected [Recipient, Means(Via)], got {other:?}"),
    }
}

#[test]
fn a15_topic_role() {
    let s = one("The system shall notify the operator about the failure.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(single(vp.object.as_ref().expect("object")).head, "operator");
    match vp.roles.as_slice() {
        [RolePp::Topic(topic)] => assert_eq!(single(topic).head, "failure"),
        other => panic!("expected [Topic], got {other:?}"),
    }
}

#[test]
fn a16_each_with_passive_be() {
    let s = one("Each request shall be logged.");
    let (subject, _, _, vp) = deontic(&s);
    assert_eq!(single(subject).det, Some(Det::Each));
    assert_eq!(single(subject).head, "request");
    assert_eq!(vp.verb, "be");
    assert_eq!(vp.complement, Some(Predicate::Words { words: vec!["logged".into()] }));
}

#[test]
fn a17_framed_description_with_pp_predicate() {
    let s = one("While the engine is running, the temperature is always below the limit.");
    assert_eq!(s.frames.states.len(), 1);
    let (subject, _, adverb, predicate) = description(&s);
    assert_eq!(single(subject).head, "temperature");
    assert_eq!(adverb, Some(DescriptionAdverb::Always));
    match predicate {
        Predicate::Pp { preposition, np } => {
            assert_eq!(preposition, "below");
            assert_eq!(single(np).head, "limit");
        }
        other => panic!("expected pp predicate, got {other:?}"),
    }
}

#[test]
fn a18_exception_clause() {
    let s = one("The pump shall stop, unless the override is active.");
    let exception = s.exception.as_ref().expect("exception clause");
    assert_eq!(single(&exception.subject).head, "override");
    assert!(matches!(
        &exception.body,
        ClauseBody::Copular { copula: ClauseCopula::Is, predicate, ..  }
            if *predicate == Predicate::Words { words: vec!["active".into()] }
    ));
}

#[test]
fn a19_purpose_so_that() {
    let s = one("The daemon shall persist the node, so that the auditor traces the decision.");
    match &s.purpose {
        Some(Purpose::SoThat(clause)) => {
            assert_eq!(single(&clause.subject).head, "auditor");
            match &clause.body {
                ClauseBody::Verbal { verb, object, .. } => {
                    assert_eq!(verb, "traces");
                    assert_eq!(single(object.as_ref().expect("object")).head, "decision");
                }
                other => panic!("expected verbal body, got {other:?}"),
            }
        }
        other => panic!("expected SoThat purpose, got {other:?}"),
    }
}

#[test]
fn a20_purpose_in_order_to() {
    let s = one("The system shall log each request, in order to preserve the audit trail.");
    match &s.purpose {
        Some(Purpose::InOrderTo(vp)) => {
            assert_eq!(vp.verb, "preserve");
            assert_eq!(single(vp.object.as_ref().expect("object")).head, "trail");
        }
        other => panic!("expected InOrderTo purpose, got {other:?}"),
    }
}

#[test]
fn a21_no_determiner_and_url_recipient() {
    let s = one(
        "When no OTLP endpoint is configured, the tracing library should default \
         OTLP HTTP export to http://192.168.10.4:4318.",
    );
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    let frame_subject = single(&trigger.clause.items[0].subject);
    assert_eq!(frame_subject.det, Some(Det::No));
    assert_eq!(frame_subject.modifiers, vec!["OTLP".to_string()]);
    assert_eq!(frame_subject.head, "endpoint");
    let (_, _, _, vp) = deontic(&s);
    match vp.roles.as_slice() {
        [RolePp::Recipient(recipient)] => {
            assert_eq!(single(recipient).head, "http://192.168.10.4:4318");
        }
        other => panic!("expected [Recipient(url)], got {other:?}"),
    }
}

#[test]
fn a22_relative_clause_in_subject() {
    let s = one("The user who is authenticated may open the session.");
    let (subject, modal, _, vp) = deontic(&s);
    assert_eq!(modal, Modal::May);
    let np = single(subject);
    assert_eq!(np.head, "user");
    let relative = np.relative.as_ref().expect("relative");
    assert_eq!(relative.marker, RelMarker::Who);
    match &relative.body {
        RelativeBody::Copular { copula: ClauseCopula::Is, predicate, .. } => {
            assert_eq!(*predicate, Predicate::Words { words: vec!["authenticated".into()] });
        }
        other => panic!("expected copular relative, got {other:?}"),
    }
    assert_eq!(vp.verb, "open");
    assert_eq!(single(vp.object.as_ref().expect("object")).head, "session");
}

#[test]
fn a23_at_most_comparison() {
    let s = one("The retry count is at most 3.");
    let (_, _, adverb, predicate) = description(&s);
    assert_eq!(adverb, None);
    assert_eq!(
        *predicate,
        Predicate::Comparison(Comparison {
            op: ComparisonOp::AtMost,
            value: Measure::Quantity { number: "3".into(), unit: None },
            upper: None,
        })
    );
}

#[test]
fn a24_between_unit_attaches_to_the_measure_it_follows() {
    let s = one("The delay is between 5 and 30 seconds.");
    let (_, _, _, predicate) = description(&s);
    assert_eq!(
        *predicate,
        Predicate::Comparison(Comparison {
            op: ComparisonOp::Between,
            value: Measure::Quantity { number: "5".into(), unit: None },
            upper: Some(Measure::Quantity { number: "30".into(), unit: Some("seconds".into()) }),
        })
    );
}

#[test]
fn a25_bare_plural_description() {
    let s = one("Requests are logged.");
    let (subject, copula, adverb, predicate) = description(&s);
    let np = single(subject);
    assert_eq!(np.det, None);
    assert_eq!(np.head, "Requests", "surface casing kept on open-class words");
    assert_eq!(copula, Copula::Are);
    assert_eq!(adverb, None);
    assert_eq!(*predicate, Predicate::Words { words: vec!["logged".into()] });
}

#[test]
fn a26_multi_sentence_sources_and_references() {
    let spec = parse(
        "A session means a sequence of requests. \
         When a session expires, the system shall close the session.",
    )
    .expect("must parse");
    assert_eq!(spec.sentences.len(), 2);
    assert_eq!(spec.sentences[0].source, "A session means a sequence of requests.");
    assert_eq!(
        spec.sentences[1].source,
        "When a session expires, the system shall close the session."
    );
    let refs = semantics::references(&spec);
    assert_eq!(refs.len(), 2, "exactly `the system` and `the session`: {refs:?}");
    // Reading order within sentence 1: frame first, then core.
    assert_eq!(refs[0].head, "system");
    assert_eq!(refs[0].sentence, 1);
    assert_eq!(
        refs[0].resolution,
        Resolution::Unresolved,
        "`the system` with no antecedent is deixis, not an error"
    );
    assert_eq!(refs[1].head, "session");
    assert_eq!(
        refs[1].resolution,
        Resolution::Unique { antecedent_sentence: 1 },
        "same-head introductions dedupe to the MOST RECENT (the frame's `a session`)"
    );
}

#[test]
fn a27_modal_recognized_case_insensitively() {
    let s = one("the pump SHALL stop.");
    let (_, modal, negated, _) = deontic(&s);
    assert_eq!(modal, Modal::Shall);
    assert!(!negated);
}

#[test]
fn a28_multibyte_open_class() {
    let s = one("The café shall serve crêpes.");
    let (subject, _, _, vp) = deontic(&s);
    assert_eq!(single(subject).head, "café");
    assert_eq!(single(vp.object.as_ref().expect("object")).head, "crêpes");
}

// ---- frame order / casing edge cases -----------------------------------------------

#[test]
fn f01_frame_keyword_casing_preserved_and_render_canonicalizes() {
    let s = one("WHERE the flag is set, the pump shall stop.");
    assert_eq!(s.frames.scopes[0].keyword, "WHERE");
    assert_eq!(s.render(), "Where the flag is set, the pump shall stop.");

    let s = one("WHILE the engine is running, WHEN the mode is manual, the pump shall stop.");
    assert_eq!(s.frames.states[0].keyword, "WHILE");
    assert_eq!(s.frames.trigger.as_ref().expect("trigger").keyword, "WHEN");
    assert_eq!(s.frames.trigger.as_ref().expect("trigger").kind, TriggerKind::Event);
}

#[test]
fn f02_if_then_casing() {
    let s = one("IF the balance is negative, THEN the account shall be frozen.");
    let trigger = s.frames.trigger.as_ref().expect("trigger");
    assert_eq!(trigger.kind, TriggerKind::Contingency);
    assert_eq!(trigger.keyword, "IF");
    // Render always re-emits `then`.
    assert_eq!(s.render(), "If the balance is negative, then the account shall be frozen.");
}

#[test]
fn f03_canonical_order_where_while_trigger() {
    let s = one(
        "Where the region is EU, where the plan is premium, while the engine runs, \
         when the temperature exceeds the limit, the pump shall stop.",
    );
    assert_eq!(s.frames.scopes.len(), 2);
    assert_eq!(s.frames.states.len(), 1);
    assert!(s.frames.trigger.is_some());
}

#[test]
fn f04_frame_order_violations() {
    // where after while
    assert_eq!(
        parse("While the engine runs, where the plan is premium, the pump shall stop."),
        Err(ParseError::FrameOrder { keyword: "where".into(), after: "While".into() })
    );
    // where after trigger
    assert_eq!(
        parse("When the order ships, where the plan is premium, the pump shall stop."),
        Err(ParseError::FrameOrder { keyword: "where".into(), after: "When".into() })
    );
    // while after trigger (spec reject item)
    assert_eq!(
        parse("When the order ships, while the engine runs, the pump shall stop."),
        Err(ParseError::FrameOrder { keyword: "while".into(), after: "When".into() })
    );
    // while after if-with-then
    assert_eq!(
        parse("If the balance is negative, then while the engine runs, the pump shall stop."),
        Err(ParseError::FrameOrder { keyword: "while".into(), after: "If".into() })
    );
}

#[test]
fn f05_multiple_triggers_keep_surface_keywords() {
    assert_eq!(
        parse("When x occurs, if y occurs, the pump shall stop."),
        Err(ParseError::MultipleTriggers { first: "When".into(), second: "if".into() })
    );
    assert_eq!(
        parse("If x occurs, then if y occurs, the pump shall stop."),
        Err(ParseError::MultipleTriggers { first: "If".into(), second: "if".into() })
    );
    assert_eq!(
        parse("WHEN x occurs, WHEN y occurs, the pump shall stop."),
        Err(ParseError::MultipleTriggers { first: "WHEN".into(), second: "WHEN".into() })
    );
}

#[test]
fn f06_then_without_if() {
    assert_eq!(
        parse("While the engine is running, then the pump shall stop."),
        Err(ParseError::ThenWithoutIf)
    );
    assert_eq!(
        parse("When the order ships, then the pump shall stop."),
        Err(ParseError::ThenWithoutIf)
    );
    assert_eq!(
        parse("Where the flag is set, then the pump shall stop."),
        Err(ParseError::ThenWithoutIf)
    );
}

#[test]
fn f07_unterminated_and_empty_frames() {
    assert_eq!(
        parse("When the order is submitted the system shall record the total."),
        Err(ParseError::UnterminatedFrame { keyword: "When".into() })
    );
    // `then` present but the comma missing is still an unterminated frame.
    assert_eq!(
        parse("If the balance is negative then the account shall be frozen."),
        Err(ParseError::UnterminatedFrame { keyword: "If".into() })
    );
    assert_eq!(
        parse("When , the pump shall stop."),
        Err(ParseError::EmptyFrame { keyword: "When".into() })
    );
    assert_eq!(
        parse("While , the pump shall stop."),
        Err(ParseError::EmptyFrame { keyword: "While".into() })
    );
}

#[test]
fn f08_frame_on_definition_names_surface_keyword() {
    assert_eq!(
        parse("While the engine is running, a workspace means a shared folder."),
        Err(ParseError::FrameOnDefinition { keyword: "While".into() })
    );
    assert_eq!(
        parse("when the order ships, a workspace means a shared folder."),
        Err(ParseError::FrameOnDefinition { keyword: "when".into() })
    );
    assert_eq!(
        parse("If the balance is negative, a workspace means a shared folder."),
        Err(ParseError::FrameOnDefinition { keyword: "If".into() })
    );
}

// ---- core / pivot rejections --------------------------------------------------------

#[test]
fn p01_empty_and_subject_errors() {
    assert_eq!(parse(""), Err(ParseError::Empty));
    assert_eq!(parse("   "), Err(ParseError::Empty));
    assert_eq!(parse("."), Err(ParseError::Empty));
    assert_eq!(parse("The shall run."), Err(ParseError::EmptySubject));
    assert_eq!(parse("shall run."), Err(ParseError::EmptySubject));
    assert_eq!(parse("means a folder."), Err(ParseError::EmptySubject));
    assert_eq!(parse("The pump quickly."), Err(ParseError::MissingPivot));
}

#[test]
fn p02_empty_vp_and_predicate_and_definiens() {
    assert_eq!(parse("The pump shall."), Err(ParseError::EmptyVp));
    assert_eq!(parse("The pump shall not."), Err(ParseError::EmptyVp));
    assert_eq!(parse("The pump is."), Err(ParseError::EmptyPredicate));
    assert_eq!(parse("The delay is greater than."), Err(ParseError::EmptyPredicate));
    assert_eq!(parse("A session means."), Err(ParseError::EmptyDefiniens));
}

#[test]
fn p03_modal_rejections() {
    assert_eq!(parse("The client may not retry."), Err(ParseError::AmbiguousModal));
    assert_eq!(
        parse("The client can retry."),
        Err(ParseError::UnsupportedModal { word: "can".into() })
    );
    // Surface casing of the offending word is preserved.
    assert_eq!(
        parse("The client CAN retry."),
        Err(ParseError::UnsupportedModal { word: "CAN".into() })
    );
    for modal in ["will", "would", "could", "might", "ought"] {
        assert_eq!(
            parse(&format!("The client {modal} retry.")),
            Err(ParseError::UnsupportedModal { word: modal.into() }),
            "for {modal}"
        );
    }
}

#[test]
fn p04_negated_description() {
    assert_eq!(
        parse("The sales amount is not greater than zero."),
        Err(ParseError::NegatedDescription)
    );
    assert_eq!(parse("Requests are not logged."), Err(ParseError::NegatedDescription));
}

#[test]
fn p05_mid_sentence_frame() {
    assert_eq!(
        parse("The tracing library should default export to X when no endpoint is configured."),
        Err(ParseError::MidSentenceFrame { keyword: "when".into() })
    );
    // `unless` without its leading comma is also a mid-sentence frame keyword.
    assert_eq!(
        parse("The pump shall stop unless the override is active."),
        Err(ParseError::MidSentenceFrame { keyword: "unless".into() })
    );
    assert_eq!(
        parse("The pump shall stop while the engine runs."),
        Err(ParseError::MidSentenceFrame { keyword: "while".into() })
    );
}

#[test]
fn p06_error_messages_are_actionable() {
    let msg = |e: ParseError| e.to_string();
    assert!(msg(ParseError::EmptyVp).contains("response"));
    assert!(msg(ParseError::AmbiguousModal).contains("shall not"));
    assert!(msg(ParseError::UnsupportedModal { word: "can".into() })
        .contains("shall, must, should, or may"));
    assert!(msg(ParseError::NegatedDescription).contains("never"));
    let mid = msg(ParseError::MidSentenceFrame { keyword: "when".into() });
    assert!(mid.contains("lead"), "message should say conditions lead the sentence: {mid}");
    // No assume/guarantee vocabulary in any parse diagnostic.
    for e in [
        ParseError::Empty,
        ParseError::MissingPivot,
        ParseError::EmptySubject,
        ParseError::EmptyVp,
        ParseError::EmptyPredicate,
        ParseError::EmptyDefiniens,
        ParseError::AmbiguousModal,
        ParseError::NegatedDescription,
        ParseError::ThenWithoutIf,
        ParseError::MixedCoordination,
    ] {
        let m = msg(e).to_lowercase();
        assert!(!m.contains("assumption") && !m.contains("guarantee"), "A/G vocabulary in: {m}");
    }
}

#[test]
fn p07_error_kinds_cover_spec_set() {
    let cases: Vec<(ParseError, &str)> = vec![
        (ParseError::Empty, "empty"),
        (ParseError::UnterminatedFrame { keyword: "When".into() }, "unterminated_frame"),
        (ParseError::EmptyFrame { keyword: "When".into() }, "empty_frame"),
        (ParseError::FrameOrder { keyword: "while".into(), after: "When".into() }, "frame_order"),
        (
            ParseError::MultipleTriggers { first: "When".into(), second: "if".into() },
            "multiple_triggers",
        ),
        (ParseError::ThenWithoutIf, "then_without_if"),
        (ParseError::FrameOnDefinition { keyword: "While".into() }, "frame_on_definition"),
        (ParseError::MidSentenceFrame { keyword: "when".into() }, "mid_sentence_frame"),
        (ParseError::MissingPivot, "missing_pivot"),
        (ParseError::UnsupportedModal { word: "can".into() }, "unsupported_modal"),
        (ParseError::AmbiguousModal, "ambiguous_modal"),
        (ParseError::NegatedDescription, "negated_description"),
        (ParseError::EmptySubject, "empty_subject"),
        (ParseError::EmptyVp, "empty_vp"),
        (ParseError::EmptyPredicate, "empty_predicate"),
        (ParseError::EmptyDefiniens, "empty_definiens"),
        (ParseError::MixedCoordination, "mixed_coordination"),
        (ParseError::UnexpectedTokens { token: "x".into() }, "unexpected_tokens"),
    ];
    for (error, kind) in cases {
        assert_eq!(error.kind(), kind);
    }
}

// ---- coordination markers ---------------------------------------------------------

#[test]
fn m01_both_and_either_groups() {
    let s = one("Both the pump and the valve shall stop.");
    match &s.core {
        Core::Deontic { subject: NpGroup::Coordinated { conj, marker, items }, .. } => {
            assert_eq!(*conj, Conj::And);
            assert_eq!(*marker, Some(GroupMarker::Both));
            assert_eq!(items.len(), 2);
            assert_eq!(items[0].head, "pump");
            assert_eq!(items[1].head, "valve");
        }
        other => panic!("expected marked coordination, got {other:?}"),
    }
    let s = one("Either the cache or the database shall answer.");
    match &s.core {
        Core::Deontic { subject: NpGroup::Coordinated { conj, marker, items }, .. } => {
            assert_eq!(*conj, Conj::Or);
            assert_eq!(*marker, Some(GroupMarker::Either));
            assert_eq!(items.len(), 2);
        }
        other => panic!("expected marked coordination, got {other:?}"),
    }
}

#[test]
fn m02_marker_mismatches_reject() {
    assert_eq!(
        parse("The system shall record the total and or the tax."),
        Err(ParseError::MixedCoordination)
    );
    assert_eq!(
        parse("The system shall record the total and the tax or the fee."),
        Err(ParseError::MixedCoordination)
    );
    // both must pair with `and` over exactly two items
    assert_eq!(
        parse("Both the pump or the valve shall stop."),
        Err(ParseError::MixedCoordination)
    );
    assert_eq!(
        parse("Both the pump and the valve and the fan shall stop."),
        Err(ParseError::MixedCoordination)
    );
    assert_eq!(parse("Both the pump shall stop."), Err(ParseError::MixedCoordination));
    // either must pair with `or`
    assert_eq!(
        parse("Either the pump and the valve shall stop."),
        Err(ParseError::MixedCoordination)
    );
}

#[test]
fn m03_unmarked_three_item_group_is_legal() {
    let s = one("The pump and the valve and the fan shall stop.");
    match &s.core {
        Core::Deontic { subject: NpGroup::Coordinated { conj: Conj::And, marker: None, items }, .. } => {
            assert_eq!(items.len(), 3);
        }
        other => panic!("expected 3-item coordination, got {other:?}"),
    }
}

#[test]
fn m04_coordinated_definition_term_rejects() {
    assert_eq!(
        parse("A pump and a valve means a machine."),
        Err(ParseError::UnexpectedTokens { token: "and".into() })
    );
}

// ---- relative clauses containing pivot-level words ----------------------------------

#[test]
fn r01_relative_verbal_with_object() {
    let s = one("Each request that carries a token shall be logged.");
    let (subject, _, _, vp) = deontic(&s);
    let np = single(subject);
    assert_eq!(np.head, "request");
    let relative = np.relative.as_ref().expect("relative");
    assert_eq!(relative.marker, RelMarker::That);
    match &relative.body {
        RelativeBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "carries");
            assert_eq!(single(object.as_ref().expect("object")).head, "token");
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
    assert_eq!(vp.verb, "be");
}

#[test]
fn r02_relative_with_coordinated_object() {
    let s = one("The user who holds a key or a badge may enter.");
    let (subject, modal, _, vp) = deontic(&s);
    assert_eq!(modal, Modal::May);
    let np = single(subject);
    let relative = np.relative.as_ref().expect("relative");
    match &relative.body {
        RelativeBody::Verbal { verb, object, .. } => {
            assert_eq!(verb, "holds");
            match object.as_ref().expect("object") {
                NpGroup::Coordinated { conj: Conj::Or, marker: None, items } => {
                    assert_eq!(items.len(), 2);
                    assert_eq!(items[0].head, "key");
                    assert_eq!(items[1].head, "badge");
                }
                other => panic!("expected or-coordination, got {other:?}"),
            }
        }
        other => panic!("expected verbal relative, got {other:?}"),
    }
    assert_eq!(vp.verb, "enter");
}

#[test]
fn r03_relative_copula_does_not_end_subject() {
    // The `is` inside the relative must not be taken as the sentence pivot.
    let s = one("The account that is frozen is never active.");
    let (subject, copula, adverb, predicate) = description(&s);
    let np = single(subject);
    assert_eq!(np.head, "account");
    assert!(matches!(
        np.relative.as_deref(),
        Some(Relative { body: RelativeBody::Copular { copula: ClauseCopula::Is, .. }, .. })
    ));
    assert_eq!(copula, Copula::Is);
    assert_eq!(adverb, Some(DescriptionAdverb::Never));
    assert_eq!(*predicate, Predicate::Words { words: vec!["active".into()] });
}

// ---- definiens NP-vs-clause choice ---------------------------------------------------

#[test]
fn d01_copular_definiens_is_a_clause() {
    let s = one("A valid token means the signature is correct.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Clause(clause) => {
            assert_eq!(single(&clause.subject).head, "signature");
            assert!(matches!(
                &clause.body,
                ClauseBody::Copular { copula: ClauseCopula::Is, predicate, ..  }
                    if *predicate == Predicate::Words { words: vec!["correct".into()] }
            ));
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
}

#[test]
fn d02_remains_definiens_is_a_clause() {
    let s = one("A frozen account means the account remains locked.");
    let (term, definiens) = definition(&s);
    assert_eq!(term.modifiers, vec!["frozen".to_string()]);
    assert_eq!(term.head, "account");
    match definiens {
        Definiens::Clause(clause) => {
            assert!(matches!(
                &clause.body,
                ClauseBody::Copular { copula: ClauseCopula::Remains, .. }
            ));
        }
        other => panic!("expected clause definiens, got {other:?}"),
    }
}

#[test]
fn d03_np_definiens_with_roles() {
    let s = one("An export means a transfer to the collector via OTLP.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Np { np, roles } => {
            assert_eq!(single(np).head, "transfer");
            assert!(matches!(
                roles.as_slice(),
                [RolePp::Recipient(_), RolePp::Means { marker: MeansMarker::Via, .. }]
            ));
        }
        other => panic!("expected np definiens with roles, got {other:?}"),
    }
}

// ---- measures and units --------------------------------------------------------------

#[test]
fn u01_units_attach_to_their_own_measure() {
    let s = one("The delay is between 5 seconds and 30 seconds.");
    let (_, _, _, predicate) = description(&s);
    assert_eq!(
        *predicate,
        Predicate::Comparison(Comparison {
            op: ComparisonOp::Between,
            value: Measure::Quantity { number: "5".into(), unit: Some("seconds".into()) },
            upper: Some(Measure::Quantity { number: "30".into(), unit: Some("seconds".into()) }),
        })
    );
}

#[test]
fn u02_number_words_kept_as_written_in_measures() {
    let s = one("The system shall respond within ten seconds.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(
        vp.roles,
        vec![RolePp::Deadline(Measure::Quantity {
            number: "ten".into(),
            unit: Some("seconds".into()),
        })]
    );
}

#[test]
fn u03_np_measures() {
    let s = one("The delay is greater than the timeout.");
    let (_, _, _, predicate) = description(&s);
    match predicate {
        Predicate::Comparison(Comparison { op: ComparisonOp::GreaterThan, value: Measure::Np { np }, upper: None }) => {
            assert_eq!(single(np).head, "timeout");
        }
        other => panic!("expected np-measure comparison, got {other:?}"),
    }
    // Mixed: numeric lower bound, np upper bound.
    let s = one("The delay is between zero and the timeout.");
    let (_, _, _, predicate) = description(&s);
    match predicate {
        Predicate::Comparison(Comparison { op: ComparisonOp::Between, value, upper: Some(Measure::Np { np }) }) => {
            assert_eq!(*value, Measure::Quantity { number: "zero".into(), unit: None });
            assert_eq!(single(np).head, "timeout");
        }
        other => panic!("expected between with np upper bound, got {other:?}"),
    }
}

#[test]
fn u04_quantifier_determiners_with_numbers_and_number_words() {
    let s = one("At least 3 replicas are available.");
    let (subject, _, _, _) = description(&s);
    assert_eq!(single(subject).det, Some(Det::AtLeast { n: 3 }));
    assert_eq!(single(subject).head, "replicas");

    let s = one("Exactly two nodes shall respond.");
    let (subject, _, _, vp) = deontic(&s);
    assert_eq!(single(subject).det, Some(Det::Exactly { n: 2 }));
    assert_eq!(vp.verb, "respond");
}

#[test]
fn u05_equal_to_inside_be_complement() {
    // `to` is a role preposition in vp position; `equal to` must win.
    let s = one("The account balance shall be equal to zero.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.verb, "be");
    assert_eq!(
        vp.complement,
        Some(Predicate::Comparison(Comparison {
            op: ComparisonOp::EqualTo,
            value: Measure::Quantity { number: "zero".into(), unit: None },
            upper: None,
        }))
    );
    assert!(vp.roles.is_empty());
}

#[test]
fn u06_plain_at_is_a_prepositional_predicate() {
    let s = one("The sensor is at the door.");
    let (_, _, _, predicate) = description(&s);
    match predicate {
        Predicate::Pp { preposition, np } => {
            assert_eq!(preposition, "at");
            assert_eq!(single(np).head, "door");
        }
        other => panic!("expected `at` pp predicate, got {other:?}"),
    }
}

// ---- the remaining thematic roles ---------------------------------------------------

#[test]
fn t01_duration_rate_source_goal() {
    let s = one("The daemon shall retain the log for 30 days.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(
        vp.roles,
        vec![RolePp::Duration(Measure::Quantity { number: "30".into(), unit: Some("days".into()) })]
    );

    let s = one("The system shall poll per second.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.roles, vec![RolePp::Rate { unit: "second".into() }]);
    assert!(vp.object.is_none());

    let s = one("The service shall copy the record from the queue into the archive.");
    let (_, _, _, vp) = deontic(&s);
    match vp.roles.as_slice() {
        [RolePp::Source(source), RolePp::Goal(goal)] => {
            assert_eq!(single(source).head, "queue");
            assert_eq!(single(goal).head, "archive");
        }
        other => panic!("expected [Source, Goal], got {other:?}"),
    }
}

#[test]
fn t02_before_and_after_take_clauses() {
    let s = one("The system shall flush the buffer before the connection closes.");
    let (_, _, _, vp) = deontic(&s);
    match vp.roles.as_slice() {
        [RolePp::Before(clause)] => {
            assert_eq!(single(&clause.subject).head, "connection");
            assert!(matches!(&clause.body, ClauseBody::Verbal { verb, object: None, .. } if verb == "closes"));
        }
        other => panic!("expected [Before(clause)], got {other:?}"),
    }
    let s = one("The daemon shall compact the store after the snapshot completes.");
    let (_, _, _, vp) = deontic(&s);
    assert!(matches!(vp.roles.as_slice(), [RolePp::After(_)]));
}

#[test]
fn t03_be_with_roles_and_no_complement() {
    let s = one("The receipt shall be from the gateway.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.verb, "be");
    assert_eq!(vp.complement, None);
    assert!(matches!(vp.roles.as_slice(), [RolePp::Source(_)]));

    // be + open-class complement + role
    let s = one("The alert shall be sent to the operator.");
    let (_, _, _, vp) = deontic(&s);
    assert_eq!(vp.complement, Some(Predicate::Words { words: vec!["sent".into()] }));
    assert!(matches!(vp.roles.as_slice(), [RolePp::Recipient(_)]));
}

// ---- exception / purpose ordering ----------------------------------------------------

#[test]
fn e01_exception_before_purpose_ok_reverse_rejected() {
    // Round 11 (fail-closed verb boundary): `retains control` is a
    // boundary-less bare run — the ambiguous class — so the purpose clause
    // carries a determiner on its object now.
    let s = one(
        "The pump shall stop, unless the override is active, \
         so that the operator retains the control.",
    );
    assert!(s.exception.is_some());
    assert!(matches!(s.purpose, Some(Purpose::SoThat(_))));

    assert_eq!(
        parse(
            "The pump shall stop, so that the operator retains the control, \
             unless the override is active."
        ),
        Err(ParseError::UnexpectedTokens { token: "unless".into() })
    );
}

// ---- render round-trips (spec: corpus items 1,3,4,5,7,9,12,14,18,19) ------------------

/// Compare specifications ignoring `source`. Frame keywords are additionally
/// folded to canonical casing because render is canonical while the tree keeps
/// surface casing (see finding: the spec's "ignoring `source`" alone cannot
/// hold for corpus item 7, whose input writes `when` in lowercase).
fn normalize(mut spec: Specification) -> Specification {
    for sentence in &mut spec.sentences {
        sentence.source = String::new();
        for frame in &mut sentence.frames.scopes {
            frame.keyword = "Where".to_string();
        }
        for frame in &mut sentence.frames.states {
            frame.keyword = "While".to_string();
        }
        if let Some(trigger) = &mut sentence.frames.trigger {
            trigger.keyword = match trigger.kind {
                TriggerKind::Event => "When".to_string(),
                TriggerKind::Contingency => "If".to_string(),
            };
        }
    }
    spec
}

#[test]
fn rt01_render_round_trips_for_the_spec_listed_items() {
    let corpus = [
        // item 1
        "The pump shall stop.",
        // item 3
        "The sales amount is always greater than zero.",
        // item 4
        "When the order is submitted, the system shall record the total.",
        // item 5
        "If the balance is negative, then the account shall be frozen.",
        // item 7
        "While the engine is running, when the temperature exceeds the limit, \
         the controller shall open the valve.",
        // item 9
        "A session means a sequence of requests from one client.",
        // item 12
        "The tracing library should install TraceContext and Baggage propagators.",
        // item 14
        "The gateway shall send the receipt to the customer via TLS.",
        // item 18
        "The pump shall stop, unless the override is active.",
        // item 19
        "The daemon shall persist the node, so that the auditor traces the decision.",
    ];
    for input in corpus {
        let parsed = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
        let rendered = parsed.render();
        let reparsed = parse(&rendered).unwrap_or_else(|e| {
            panic!("render of {input:?} must re-parse; {rendered:?} gave: {e}")
        });
        assert_eq!(
            normalize(reparsed),
            normalize(parsed),
            "round trip diverged for {input:?} via {rendered:?}"
        );
    }
}

#[test]
fn rt02_render_round_trips_markers_and_measures() {
    for input in [
        "Both the pump and the valve shall stop.",
        "Either the cache or the database shall answer.",
        "The delay is between 5 and 30 seconds.",
        "The system shall poll per second.",
        "Each request shall be logged.",
        "The system shall log each request, in order to preserve the audit trail.",
        "At least 3 replicas are available.",
    ] {
        let parsed = parse(input).unwrap_or_else(|e| panic!("{input:?} must parse, got: {e}"));
        let rendered = parsed.render();
        let reparsed = parse(&rendered).unwrap_or_else(|e| {
            panic!("render of {input:?} must re-parse; {rendered:?} gave: {e}")
        });
        assert_eq!(normalize(reparsed), normalize(parsed), "diverged via {rendered:?}");
    }
}

// ---- semantics: acts, force, denote, ingest_contract for every speech act -------------

#[test]
fn s01_speech_acts() {
    let acts = [
        ("The pump shall stop.", SpeechAct::Obligation),
        ("The pump must stop.", SpeechAct::Obligation),
        ("The daemon shall not store derived views.", SpeechAct::Prohibition),
        ("The daemon must not store derived views.", SpeechAct::Prohibition),
        ("The daemon should retry.", SpeechAct::Recommendation),
        ("The daemon should not retry.", SpeechAct::Recommendation),
        ("The client may retry.", SpeechAct::Permission),
        ("Requests are logged.", SpeechAct::Description),
        ("A session means a sequence of requests.", SpeechAct::Definition),
    ];
    for (input, expected) in acts {
        assert_eq!(semantics::speech_act(&one(input)), expected, "for {input:?}");
    }
}

#[test]
fn s02_force() {
    assert_eq!(semantics::force(&one("The pump shall stop.")), Some(Force::Binding));
    assert_eq!(semantics::force(&one("The pump must stop.")), Some(Force::Binding));
    assert_eq!(semantics::force(&one("The pump should stop.")), Some(Force::Recommended));
    assert_eq!(semantics::force(&one("The pump may stop.")), None);
    assert_eq!(semantics::force(&one("The pump is stopped.")), None);
    assert_eq!(semantics::force(&one("A pump means a device.")), None);
}

#[test]
fn s03_denote_covers_all_cores() {
    // Definition -> Vocabulary, scopes carried over.
    match semantics::denote(&one(
        "where the premium plan is enabled, a workspace means a shared folder.",
    )) {
        Denotation::Vocabulary { scopes, term, .. } => {
            assert_eq!(scopes.len(), 1);
            assert_eq!(term.head, "workspace");
        }
        other => panic!("expected vocabulary, got {other:?}"),
    }
    // Description with `never` -> negative State.
    match semantics::denote(&one("The temperature is never above the limit.")) {
        Denotation::Behavior(a) => {
            assert!(matches!(a.claim, Claim::State { polarity: Polarity::Negative, .. }));
        }
        other => panic!("expected behavior, got {other:?}"),
    }
    // shall not -> negative binding Action.
    match semantics::denote(&one("The daemon shall not store derived views.")) {
        Denotation::Behavior(a) => {
            assert!(matches!(
                a.claim,
                Claim::Action { polarity: Polarity::Negative, force: Force::Binding, .. }
            ));
        }
        other => panic!("expected behavior, got {other:?}"),
    }
    // should not -> negative recommended Action.
    match semantics::denote(&one("The daemon should not retry.")) {
        Denotation::Behavior(a) => {
            assert!(matches!(
                a.claim,
                Claim::Action { polarity: Polarity::Negative, force: Force::Recommended, .. }
            ));
        }
        other => panic!("expected behavior, got {other:?}"),
    }
    // may -> Admissibility.
    match semantics::denote(&one("The client may retry.")) {
        Denotation::Admissibility(a) => {
            assert!(matches!(a.claim, Claim::Admissible { .. }));
        }
        other => panic!("expected admissibility, got {other:?}"),
    }
    // Frames and exception propagate into the assertion.
    match semantics::denote(&one(
        "While the engine is running, when the temperature exceeds the limit, \
         the controller shall open the valve, unless the override is active.",
    )) {
        Denotation::Behavior(a) => {
            assert_eq!(a.states.len(), 1);
            assert!(a.trigger.is_some());
            assert!(a.exception.is_some());
            assert_eq!(single(&a.subject).head, "controller");
        }
        other => panic!("expected behavior, got {other:?}"),
    }
}

#[test]
fn s04_ingest_contract_for_every_act() {
    // Definition: no contract reading.
    assert!(semantics::ingest_contract(&one("A session means a sequence of requests.")).is_none());

    let c = semantics::ingest_contract(&one("The pump shall stop.")).expect("obligation");
    assert_eq!(c.assumption.render(), "⊤");
    assert_eq!(c.act, SpeechAct::Obligation);
    assert_eq!(c.force, Some(Force::Binding));
    assert_eq!(single(&c.guarantee.subject).head, "pump");
    assert!(matches!(
        c.guarantee.claim,
        Claim::Action { polarity: Polarity::Affirmative, force: Force::Binding, .. }
    ));

    let c = semantics::ingest_contract(&one("The daemon shall not store derived views."))
        .expect("prohibition");
    assert_eq!(c.act, SpeechAct::Prohibition);
    assert_eq!(c.force, Some(Force::Binding));
    assert!(matches!(c.guarantee.claim, Claim::Action { polarity: Polarity::Negative, .. }));

    let c = semantics::ingest_contract(&one("The daemon should retry.")).expect("recommendation");
    assert_eq!(c.act, SpeechAct::Recommendation);
    assert_eq!(c.force, Some(Force::Recommended));

    // PIN CHANGED (improvement round 1, change 5): a permission ADMITS
    // behavior rather than constraining it, so as a lone sentence it yields
    // no (⊤, G) reading — it enters a contract only through pairing, on the
    // environment side. The denotation stays Admissibility.
    assert!(semantics::ingest_contract(&one("The client may retry.")).is_none());
    assert!(matches!(
        semantics::denote(&one("The client may retry.")),
        Denotation::Admissibility(a) if matches!(a.claim, Claim::Admissible { .. })
    ));

    let c = semantics::ingest_contract(&one("Requests are logged.")).expect("description");
    assert_eq!(c.act, SpeechAct::Description);
    assert_eq!(c.force, None);
    assert!(matches!(c.guarantee.claim, Claim::State { polarity: Polarity::Affirmative, .. }));
    assert_eq!(c.assumption.render(), "⊤");
}

#[test]
fn s05_references_dedupe_by_head_to_most_recent() {
    let spec = parse(
        "A session means a shared context. \
         A session means a sequence of requests. \
         When the session expires, the daemon shall archive the session.",
    )
    .expect("must parse");
    let refs = semantics::references(&spec);
    let session_refs: Vec<_> = refs.iter().filter(|r| r.head == "session").collect();
    assert_eq!(session_refs.len(), 2, "frame `the session` and object `the session`: {refs:?}");
    for reference in &session_refs {
        assert_eq!(
            reference.resolution,
            Resolution::Unique { antecedent_sentence: 1 },
            "same-head introductions must dedupe to the most recent, never Ambiguous"
        );
    }
    let daemon = refs.iter().find(|r| r.head == "daemon").expect("the daemon");
    assert_eq!(daemon.resolution, Resolution::Unresolved, "deixis, not an error");

    // Antecedent in an earlier sentence resolves too.
    let spec = parse("A session means a sequence of requests. The system shall close the session.")
        .expect("must parse");
    let refs = semantics::references(&spec);
    let session = refs.iter().find(|r| r.head == "session").expect("the session");
    assert_eq!(session.resolution, Resolution::Unique { antecedent_sentence: 0 });
}

// ---- totality ------------------------------------------------------------------------

#[test]
fn z01_totality_spec_fuzz_list_never_panics() {
    let inputs = [
        "€",
        "中",
        "中文",
        "南南 shall stop.",
        "🔥 shall stop",
        "th×foo shall bar",
        "When x, the×foo the pump shall stop",
        "éé shall stop.",
        "When x, 日本 the pump shall stop.",
        "×",
        "The pump shall stop..",
        "a , b",
        ",",
        "The pump shall stop, unless",
        "both and",
        // extra adversarial punctuation / truncation
        "The pump is at.",
        "The delay is between the minimum and the maximum.",
        "...",
        "The pump shall stop,.",
        "unless",
        "so that",
        "in order to",
        "If , then the pump shall stop.",
    ];
    for input in inputs {
        let _ = parse(input); // Ok or Err — never a panic.
    }
}

#[test]
fn z02_totality_random_soups_never_panic() {
    // Independent LCG (different seed and vocabulary from the implementer's).
    let mut state: u64 = 0x00c0_ffee_dead_beef;
    let mut next = move || {
        state = state
            .wrapping_mul(2862933555777941757)
            .wrapping_add(3037000493);
        (state >> 32) as u32
    };
    let vocabulary = [
        "the", "a", "an", "no", "each", "pump", "valve", "shall", "must", "should", "may",
        "not", "is", "are", "remains", "means", "when", "while", "where", "if", "unless",
        "then", "so", "that", "who", "in", "order", "to", "of", "and", "or", "both",
        "either", "at", "least", "most", "exactly", "between", "greater", "less", "than",
        "equal", "within", "for", "per", "before", "after", "from", "into", "via", "using",
        "about", "be", "always", "never", "0", "3", "5.5", "ten", ",", ".", "..", ".,",
        "×", "⊤", "café", "日本", "🔥", "http://192.168.10.4:4318",
    ];
    for _ in 0..800 {
        let length = (next() % 14) as usize;
        let mut soup = String::new();
        for _ in 0..length {
            let word = vocabulary[next() as usize % vocabulary.len()];
            soup.push_str(word);
            if next() % 6 == 0 {
                soup.push_str(word);
            }
            soup.push(if next() % 9 == 0 { '\n' } else { ' ' });
        }
        let _ = parse(&soup); // Ok or Err — never a panic.
    }
}

// ---- resolved audit findings (formerly ignored) ----------------------------------------

// FINDING RESOLVED AS A SPEC SELF-INCONSISTENCY: the spec's `means` section
// says "try clause ... else NP", but a literal clause-first order would break
// corpus item 8 (`a shared folder` would misread as subject `a shared` +
// verb `folder`). With open-class words opaque, `the request expires` and
// `a shared folder` are the same DET WORD WORD shape, so no syntactic
// tie-break can separate them. The acceptance corpus is normative
// ("MUST hold"), so the NP-first reading wins and this test pins that
// deterministic choice instead of the originally-expected clause reading.
#[test]
fn x01_definiens_np_priority_is_deterministic() {
    let s = one("A timeout means the request expires.");
    let (_, definiens) = definition(&s);
    match definiens {
        Definiens::Np { np, roles } => {
            assert_eq!(single(np).head, "expires");
            assert_eq!(single(np).modifiers, vec!["request".to_string()]);
            assert!(roles.is_empty());
        }
        other => panic!("expected np definiens (the deterministic reading), got {other:?}"),
    }
}

#[test]
fn x02_totality_deep_of_chain() {
    // Used to overflow the stack and abort the process; the recognizer now
    // bounds noun-phrase nesting and answers with a precise error.
    let mut input = String::with_capacity(1_200_000);
    for _ in 0..200_000 {
        input.push_str("x of ");
    }
    input.push_str("x shall stop.");
    assert!(matches!(parse(&input), Err(ParseError::PhraseTooDeep { .. })));
}

// FINDING REJECTED: the audit read constraint 4 ("keywords are contextual")
// as freeing can/will/would/... outside pivot position, e.g. `the will` as an
// object noun. But the reject corpus REQUIRES `The client can retry.` →
// UnsupportedModal{can}: that diagnosis only exists because the subject NP
// stops at `can` — i.e. because the unsupported modals are NP stop words. If
// they were free open-class words, `client can retry` would fold into the
// subject and the sentence would misreport as MissingPivot. Reserving them
// everywhere is the price of the mandated diagnostic; this test pins it.
// Since improvement round 1 (change 6) the backtick escape hatch frees the
// word where it is meant as content: `` the `will` `` parses (see corpus
// b01); the BARE word stays reserved, as pinned here.
#[test]
fn x03_unsupported_modals_stay_reserved_for_their_diagnostic() {
    assert_eq!(
        parse("The client can retry."),
        Err(ParseError::UnsupportedModal { word: "can".into() })
    );
    // The same reservation makes bare `will` unusable as an object noun.
    assert!(parse("The system shall record the will.").is_err());
    // The escape hatch: backticks free it.
    assert!(parse("The system shall record the `will`.").is_ok());
}

#[test]
fn x04_truncated_pp_predicate_should_be_empty_predicate() {
    assert_eq!(parse("The pump is at."), Err(ParseError::EmptyPredicate));
}

#[test]
fn x05_between_with_np_bounds() {
    let s = one("The delay is between the minimum and the maximum.");
    let (_, _, _, predicate) = description(&s);
    match predicate {
        Predicate::Comparison(Comparison {
            op: ComparisonOp::Between,
            value: Measure::Np { np: low },
            upper: Some(Measure::Np { np: high }),
        }) => {
            assert_eq!(single(low).head, "minimum");
            assert_eq!(single(high).head, "maximum");
        }
        other => panic!("expected between with two np measures, got {other:?}"),
    }
}
