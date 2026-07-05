//! The constrained natural-language grammar.
//!
//! A specification statement is written in an EARS-derived controlled language.
//! The grammar is a **total recognizer**: every input is either accepted (and
//! yields exactly one parse) or rejected with a precise syntax error. There is
//! no confidence score, no probabilistic parse, and no human-in-the-loop review
//! of the result — parseability is a *language requirement*, not an inference.
//!
//! The accepted forms, following EARS:
//!
//! ```text
//! Ubiquitous:  The <subject> shall <response>.
//! Conditional: <While|When|If|Where> <condition>, [then] the <subject> shall <response>.
//! Complex:     <kw> <c1>, <kw> <c2>, ... the <subject> shall <response>.
//! ```
//!
//! The A/G projection is mechanical and unambiguous:
//!   * every leading condition clause becomes part of the **assumption** (the
//!     conjunction of the clauses); with no condition clause the assumption is
//!     `⊤` (the ubiquitous case);
//!   * the `the <subject> shall <response>` clause becomes the **guarantee**.

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// The four EARS condition keywords. Matched case-insensitively; the original
/// casing is preserved in the parsed [`Condition`].
const CONDITION_KEYWORDS: [&str; 4] = ["While", "When", "If", "Where"];

/// The guarantee marker. A well-formed statement contains exactly one guarantee
/// clause, introduced by the subject determiner and pivoting on this modal.
const GUARANTEE_MODAL: &str = "shall";

/// The subject determiner that opens the guarantee clause.
const SUBJECT_DETERMINER: &str = "the";

/// A single leading condition clause, e.g. `When the order is submitted`.
///
/// The `keyword` retains the surface casing (`While`/`When`/`If`/`Where`); the
/// `text` is the condition phrase with the keyword and the trailing comma
/// stripped.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Condition {
    pub keyword: String,
    pub text: String,
}

/// The assumption projected from a statement.
///
/// `Top` is the ubiquitous case (`⊤`): the guarantee holds unconditionally.
/// `Conditions` is the conjunction of the leading condition clauses.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Assumption {
    Top,
    Conditions { clauses: Vec<Condition> },
}

impl Assumption {
    /// Render the assumption as a human-readable phrase (`⊤` for the ubiquitous
    /// case). Storage keeps the structured form; this is for display only.
    pub fn render(&self) -> String {
        match self {
            Assumption::Top => "⊤".to_string(),
            Assumption::Conditions { clauses } => clauses
                .iter()
                .map(|c| format!("{} {}", c.keyword, c.text))
                .collect::<Vec<_>>()
                .join(", "),
        }
    }
}

/// The guarantee projected from the `the <subject> shall <response>` clause.
///
/// `subject` is the noun phrase between the determiner and the modal; `response`
/// is everything after the modal. Neither is further decomposed at ingest —
/// subject resolution and a formal predicate language are deliberately deferred.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Guarantee {
    pub subject: String,
    pub response: String,
}

impl Guarantee {
    pub fn render(&self) -> String {
        format!("the {} shall {}", self.subject, self.response)
    }
}

/// The assume-guarantee contract projected from a statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Contract {
    pub assumption: Assumption,
    pub guarantee: Guarantee,
}

/// A syntax error. The grammar being a total recognizer, this is the only way a
/// statement can fail to produce a [`Contract`].
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseError {
    #[error("statement is empty")]
    Empty,
    #[error("a condition clause opened with '{keyword}' must be closed by a comma before the guarantee clause")]
    MissingComma { keyword: String },
    #[error("condition clause opened with '{keyword}' has no text")]
    EmptyCondition { keyword: String },
    #[error(
        "the guarantee clause must be of the form '{det} <subject> {modal} <response>' but no '{modal}' was found",
        det = SUBJECT_DETERMINER,
        modal = GUARANTEE_MODAL,
    )]
    MissingModal,
    #[error(
        "the guarantee clause must start with the determiner '{det}' but starts with '{found}'",
        det = SUBJECT_DETERMINER,
    )]
    MissingDeterminer { found: String },
    #[error("the guarantee clause has no subject between '{det}' and '{modal}'", det = SUBJECT_DETERMINER, modal = GUARANTEE_MODAL)]
    EmptySubject,
    #[error("the guarantee clause has no response after '{modal}'", modal = GUARANTEE_MODAL)]
    EmptyResponse,
}

/// Parse a constrained-NL statement into its assume-guarantee [`Contract`].
///
/// Total recognizer: returns `Ok` with a single unambiguous parse, or `Err`
/// with a precise [`ParseError`].
pub fn parse(input: &str) -> Result<Contract, ParseError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err(ParseError::Empty);
    }
    // Strip at most one trailing sentence period; internal periods are left to
    // the clause text.
    let body = trimmed.strip_suffix('.').unwrap_or(trimmed).trim();
    if body.is_empty() {
        return Err(ParseError::Empty);
    }

    // Consume zero or more leading condition clauses, greedily. Each clause runs
    // from its keyword to the next comma. An optional `then` after the comma
    // (EARS' `If ..., then ...`) is discarded.
    let mut clauses: Vec<Condition> = Vec::new();
    let mut rest = body.to_string();
    while let Some(keyword) = leading_condition_keyword(&rest) {
        let comma = rest.find(',').ok_or_else(|| ParseError::MissingComma {
            keyword: rest[..keyword.len()].to_string(),
        })?;
        let text = rest[keyword.len()..comma].trim().to_string();
        if text.is_empty() {
            return Err(ParseError::EmptyCondition {
                keyword: rest[..keyword.len()].to_string(),
            });
        }
        clauses.push(Condition {
            keyword: rest[..keyword.len()].to_string(),
            text,
        });
        let mut after = rest[comma + 1..].trim_start().to_string();
        after = strip_leading_then(&after);
        rest = after;
    }

    let guarantee = parse_guarantee(rest.trim())?;
    let assumption = if clauses.is_empty() {
        Assumption::Top
    } else {
        Assumption::Conditions { clauses }
    };
    Ok(Contract {
        assumption,
        guarantee,
    })
}

/// If `s` begins with a condition keyword at a word boundary, return the keyword
/// slice (from [`CONDITION_KEYWORDS`], canonical casing) so the caller can slice
/// by its byte length.
fn leading_condition_keyword(s: &str) -> Option<&'static str> {
    CONDITION_KEYWORDS
        .into_iter()
        .find(|kw| starts_with_word(s, kw))
}

/// Whether `s` begins with the ASCII `word` (case-insensitive) followed by a
/// whitespace boundary. Boundary-safe: `str::get` returns `None` rather than
/// panicking when `word.len()` falls inside a multibyte char, which is exactly
/// the "not this keyword" outcome we want.
fn starts_with_word(s: &str, word: &str) -> bool {
    s.get(..word.len())
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case(word))
        && s[word.len()..]
            .chars()
            .next()
            .is_some_and(char::is_whitespace)
}

/// Discard an optional leading `then ` (case-insensitive, word-bounded).
fn strip_leading_then(s: &str) -> String {
    const THEN: &str = "then";
    if starts_with_word(s, THEN) {
        s[THEN.len()..].trim_start().to_string()
    } else {
        s.to_string()
    }
}

/// Parse the guarantee clause `the <subject> shall <response>`.
fn parse_guarantee(clause: &str) -> Result<Guarantee, ParseError> {
    let has_modal = find_word(clause, GUARANTEE_MODAL).is_some();

    // The clause must open with the determiner at a word boundary.
    let opens_with_determiner = starts_with_word(clause, SUBJECT_DETERMINER);
    if !opens_with_determiner {
        // A missing modal is the more fundamental defect; report it first.
        if !has_modal {
            return Err(ParseError::MissingModal);
        }
        let found = clause.split_whitespace().next().unwrap_or("").to_string();
        return Err(ParseError::MissingDeterminer { found });
    }

    let after_determiner = clause[SUBJECT_DETERMINER.len()..].trim_start();
    let modal_at = find_word(after_determiner, GUARANTEE_MODAL).ok_or(ParseError::MissingModal)?;
    let subject = after_determiner[..modal_at].trim().to_string();
    let response = after_determiner[modal_at + GUARANTEE_MODAL.len()..]
        .trim()
        .to_string();
    if subject.is_empty() {
        return Err(ParseError::EmptySubject);
    }
    if response.is_empty() {
        return Err(ParseError::EmptyResponse);
    }
    Ok(Guarantee { subject, response })
}

/// Find the byte offset of `word` in `haystack` as a whole ASCII word
/// (alphanumeric boundaries), case-insensitively. Returns the offset into
/// `haystack`. `word` must be ASCII.
fn find_word(haystack: &str, word: &str) -> Option<usize> {
    let hay = haystack.as_bytes();
    let w = word.as_bytes();
    if w.is_empty() || hay.len() < w.len() {
        return None;
    }
    let mut i = 0;
    while i + w.len() <= hay.len() {
        if hay[i..i + w.len()].eq_ignore_ascii_case(w) {
            let before_ok = i == 0 || !hay[i - 1].is_ascii_alphanumeric();
            let after_idx = i + w.len();
            let after_ok = after_idx == hay.len() || !hay[after_idx].is_ascii_alphanumeric();
            if before_ok && after_ok {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn conds(cs: &[(&str, &str)]) -> Assumption {
        Assumption::Conditions {
            clauses: cs
                .iter()
                .map(|(k, t)| Condition {
                    keyword: k.to_string(),
                    text: t.to_string(),
                })
                .collect(),
        }
    }

    #[test]
    fn ubiquitous_projects_top() {
        let c = parse("The sales amount shall be greater than zero.").unwrap();
        assert_eq!(c.assumption, Assumption::Top);
        assert_eq!(c.guarantee.subject, "sales amount");
        assert_eq!(c.guarantee.response, "be greater than zero");
    }

    #[test]
    fn trailing_period_is_optional() {
        let c = parse("The pump shall stop").unwrap();
        assert_eq!(c.guarantee.subject, "pump");
        assert_eq!(c.guarantee.response, "stop");
    }

    #[test]
    fn conditional_projects_assumption() {
        let c = parse("When the order is submitted, the system shall record the total.").unwrap();
        assert_eq!(c.assumption, conds(&[("When", "the order is submitted")]));
        assert_eq!(c.guarantee.subject, "system");
        assert_eq!(c.guarantee.response, "record the total");
    }

    #[test]
    fn if_then_drops_then() {
        let c = parse("If the balance is negative, then the account shall be frozen.").unwrap();
        assert_eq!(c.assumption, conds(&[("If", "the balance is negative")]));
        assert_eq!(c.guarantee.response, "be frozen");
    }

    #[test]
    fn complex_conjoins_conditions() {
        let c = parse(
            "While the engine is running, when the temperature exceeds the limit, the controller shall open the valve.",
        )
        .unwrap();
        assert_eq!(
            c.assumption,
            conds(&[
                ("While", "the engine is running"),
                ("when", "the temperature exceeds the limit"),
            ])
        );
        assert_eq!(c.guarantee.subject, "controller");
    }

    #[test]
    fn keyword_casing_is_preserved() {
        let c = parse("when the order ships, the system shall notify the customer").unwrap();
        assert_eq!(c.assumption, conds(&[("when", "the order ships")]));
    }

    #[test]
    fn reject_empty() {
        assert_eq!(parse("   "), Err(ParseError::Empty));
        assert_eq!(parse("."), Err(ParseError::Empty));
    }

    #[test]
    fn reject_missing_modal() {
        // The original, non-conforming "is always greater than zero" phrasing.
        assert_eq!(
            parse("The sales amount is always greater than zero."),
            Err(ParseError::MissingModal)
        );
    }

    #[test]
    fn reject_conditional_without_comma() {
        assert_eq!(
            parse("When the order is submitted the system shall record the total."),
            Err(ParseError::MissingComma {
                keyword: "When".to_string()
            })
        );
    }

    #[test]
    fn reject_missing_determiner() {
        assert_eq!(
            parse("System shall record the total."),
            Err(ParseError::MissingDeterminer {
                found: "System".to_string()
            })
        );
    }

    #[test]
    fn reject_empty_subject() {
        assert_eq!(parse("The shall run."), Err(ParseError::EmptySubject));
    }

    #[test]
    fn reject_empty_response() {
        assert_eq!(parse("The pump shall."), Err(ParseError::EmptyResponse));
    }

    #[test]
    fn reject_empty_condition() {
        assert_eq!(
            parse("When , the pump shall stop."),
            Err(ParseError::EmptyCondition {
                keyword: "When".to_string()
            })
        );
    }

    #[test]
    fn total_recognizer_never_panics_on_multibyte_input() {
        // Every one of these previously panicked at a fixed-byte prefix slice.
        // A total recognizer must return Ok or Err for any input, never panic.
        let inputs = [
            "€",
            "中",
            "中文",
            "南南 shall stop.",
            "🔥 shall stop",
            "th\u{d7}foo shall bar",
            "When x, the\u{d7}foo the pump shall stop",
            "éé shall stop.",
            "When x, 日本 the pump shall stop.",
            "\u{d7}",
        ];
        for s in inputs {
            // Must not panic; either variant is an acceptable total-recognizer result.
            let _ = parse(s);
        }
    }

    #[test]
    fn multibyte_subject_and_response_parse() {
        let c = parse("The café shall serve crêpes.").unwrap();
        assert_eq!(c.assumption, Assumption::Top);
        assert_eq!(c.guarantee.subject, "café");
        assert_eq!(c.guarantee.response, "serve crêpes");
    }

    #[test]
    fn multibyte_condition_is_captured() {
        let c = parse("When the café is open, the barista shall greet the guest.").unwrap();
        assert_eq!(c.assumption, conds(&[("When", "the café is open")]));
        assert_eq!(c.guarantee.subject, "barista");
    }

    #[test]
    fn modal_inside_subject_word_is_not_a_boundary() {
        // "marshalling" contains "shall" but is not the modal; the real modal wins.
        let c = parse("The marshalling yard shall be clear.").unwrap();
        assert_eq!(c.guarantee.subject, "marshalling yard");
        assert_eq!(c.guarantee.response, "be clear");
    }
}
