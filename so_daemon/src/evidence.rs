//! Evidence interpretation: turning a resolved `--evidence` value into a
//! normalized input, ready for capture.
//!
//! A value is dual-mode:
//!   * a **JSON object** (or array of objects) — `kind` and `locator` required,
//!     optional `origin`; this is how a caller records the epistemic *kind* of
//!     the grounding at ingest time;
//!   * a **bare string** — treated as a `locator` with `kind: unknown`; the
//!     shorthand for "here is grounding, I am not classifying it now".
//!
//! The `@file` / `-`(stdin) input channels are resolved to text **client-side**
//! (they name the client's own streams). The daemon persists that concrete text
//! verbatim on the Node; the asynchronous Evidence Consumer then calls this module
//! to validate its shape and normalize the locator before capture.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::domain::{Kind, Locator};

/// Source-artifact provenance supplied by the caller (sense ① origin), used to
/// override or seed what the origin enricher would otherwise discover.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OriginInput {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub author: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub created_at: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_at: Option<String>,
}

impl OriginInput {
    pub fn is_empty(&self) -> bool {
        self.author.is_none() && self.created_at.is_none() && self.updated_at.is_none()
    }
}

/// A normalized evidence request, ready for snapshot + origin enrichment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceInput {
    pub kind: Kind,
    pub locator: Locator,
    pub origin: OriginInput,
}

/// The JSON object shape accepted for an evidence value. `kind` is required
/// (serde fails the parse if absent — a bare string is the way to say
/// "unknown"), as is `locator`.
#[derive(Debug, Deserialize)]
struct EvidenceJson {
    kind: Kind,
    locator: String,
    #[serde(default)]
    origin: OriginInput,
}

impl EvidenceJson {
    fn into_input(self) -> EvidenceInput {
        EvidenceInput {
            kind: self.kind,
            locator: Locator::parse(&self.locator),
            origin: self.origin,
        }
    }
}

/// Accepts an object or an array of objects.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum EvidenceJsonPayload {
    One(EvidenceJson),
    Many(Vec<EvidenceJson>),
}

#[derive(Debug, Error)]
pub enum EvidenceError {
    #[error("invalid evidence JSON: {0}")]
    Json(#[from] serde_json::Error),
    #[error("empty evidence value")]
    Empty,
}

/// Interpret a single (already channel-resolved) `--evidence` value into one or
/// more [`EvidenceInput`]s: JSON (object or array) if it begins with `{`/`[`,
/// otherwise a bare locator string.
pub fn parse_value(value: &str) -> Result<Vec<EvidenceInput>, EvidenceError> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Err(EvidenceError::Empty);
    }
    if trimmed.starts_with('{') || trimmed.starts_with('[') {
        let payload: EvidenceJsonPayload = serde_json::from_str(trimmed)?;
        let inputs = match payload {
            EvidenceJsonPayload::One(o) => vec![o.into_input()],
            EvidenceJsonPayload::Many(v) => v.into_iter().map(EvidenceJson::into_input).collect(),
        };
        Ok(inputs)
    } else {
        // Bare string: a locator with an unrecorded kind.
        Ok(vec![EvidenceInput {
            kind: Kind::Unknown,
            locator: Locator::parse(trimmed),
            origin: OriginInput::default(),
        }])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_string_is_unknown_locator() {
        let ev = parse_value("src/order/total.rs:32:10").unwrap();
        assert_eq!(ev.len(), 1);
        assert_eq!(ev[0].kind, Kind::Unknown);
        assert_eq!(
            ev[0].locator,
            Locator::File {
                path: "src/order/total.rs".to_string(),
                line: Some(32),
                col: Some(10),
            }
        );
    }

    #[test]
    fn bare_url_is_detected() {
        let ev = parse_value("https://rules.acme.com/sales#positive").unwrap();
        assert_eq!(ev[0].kind, Kind::Unknown);
        assert_eq!(
            ev[0].locator,
            Locator::Url {
                url: "https://rules.acme.com/sales#positive".to_string()
            }
        );
    }

    #[test]
    fn json_object_records_kind() {
        let ev =
            parse_value(r#"{"kind":"constitutive","locator":"src/order/total.rs:32:10"}"#).unwrap();
        assert_eq!(ev.len(), 1);
        assert_eq!(ev[0].kind, Kind::Constitutive);
    }

    #[test]
    fn json_array_yields_many() {
        let ev = parse_value(
            r#"[{"kind":"assertoric","locator":"https://rules.acme.com/x"},
                {"kind":"circumstantial","locator":"logs/run.txt:8"}]"#,
        )
        .unwrap();
        assert_eq!(ev.len(), 2);
        assert_eq!(ev[0].kind, Kind::Assertoric);
        assert_eq!(ev[1].kind, Kind::Circumstantial);
    }

    #[test]
    fn json_origin_is_captured() {
        let ev = parse_value(
            r#"{"kind":"testimonial","locator":"docs/spec.md","origin":{"author":"jane","created_at":"2024-01-02T03:04:05Z"}}"#,
        )
        .unwrap();
        assert_eq!(ev[0].origin.author.as_deref(), Some("jane"));
        assert_eq!(
            ev[0].origin.created_at.as_deref(),
            Some("2024-01-02T03:04:05Z")
        );
        assert_eq!(ev[0].origin.updated_at, None);
    }

    #[test]
    fn json_missing_kind_is_error() {
        // kind is required in JSON; a bare string is the way to say "unknown".
        let err = parse_value(r#"{"locator":"src/x.rs"}"#);
        assert!(err.is_err());
    }

    #[test]
    fn json_invalid_kind_is_error() {
        let err = parse_value(r#"{"kind":"vibes","locator":"src/x.rs"}"#);
        assert!(err.is_err());
    }

    #[test]
    fn empty_value_is_error() {
        assert!(matches!(parse_value("   "), Err(EvidenceError::Empty)));
    }

    #[test]
    fn path_without_line_is_bare() {
        let ev = parse_value("docs/policy.md").unwrap();
        assert_eq!(
            ev[0].locator,
            Locator::File {
                path: "docs/policy.md".to_string(),
                line: None,
                col: None,
            }
        );
    }

    #[test]
    fn path_with_only_line() {
        let ev = parse_value("src/x.rs:12").unwrap();
        assert_eq!(
            ev[0].locator,
            Locator::File {
                path: "src/x.rs".to_string(),
                line: Some(12),
                col: None,
            }
        );
    }
}
