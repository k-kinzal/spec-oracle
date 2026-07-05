//! Evidence classification and locator.
//!
//! [`Kind`] is the epistemic kind of a grounding; [`Locator`] is where the
//! grounding lives. Both appear in a persisted node's evidence. The *parsing*
//! of a `--evidence` argument into these types and the *capture* of what a
//! locator points at are daemon behavior; the protocol crate only carries the
//! generated wire mirror.

use serde::{Deserialize, Serialize};

/// The epistemic kind of a piece of evidence.
///
/// A modality axis (how the claim is grounded) plus `Counter` as a cross-cutting
/// stance (evidence *against* the guarantee) and `Unknown` as the explicit
/// "not classified at ingest" value. Kind is always recorded — the absence of a
/// judgement is itself recorded as `Unknown`, never left implicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Kind {
    /// Constitutes the fact by definition/rule (a schema, a type, an invariant).
    Constitutive,
    /// Deductive or exhaustive proof (a checked proof, a model-checking result).
    Demonstrative,
    /// A witness attests to it (a report, a person, a changelog note).
    Testimonial,
    /// An assertion of intent or policy (a rule to be upheld, a decision).
    Assertoric,
    /// Indirect signs consistent with the fact (metrics, logs, correlations).
    Circumstantial,
    /// Evidence against the guarantee.
    Counter,
    /// Not classified at ingest.
    Unknown,
}

/// A resolved evidence locator. The variant is derived from the surface string:
/// an `http`/`https` URL becomes [`Locator::Url`]; anything else is a filesystem
/// path with an optional `:line[:col]` suffix.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Locator {
    File {
        path: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        line: Option<u32>,
        #[serde(skip_serializing_if = "Option::is_none")]
        col: Option<u32>,
    },
    Url {
        url: String,
    },
}

impl Locator {
    /// Interpret a surface string as a locator. Never fails: any string is a
    /// valid file path if it is not a URL.
    pub fn parse(raw: &str) -> Locator {
        let s = raw.trim();
        if is_url(s) {
            return Locator::Url { url: s.to_string() };
        }
        // Peel an optional `:col` then `:line` off the right, but only when they
        // are purely numeric — this keeps paths that merely contain colons intact.
        let (path, line, col) = split_path_line_col(s);
        Locator::File { path, line, col }
    }

    pub fn render(&self) -> String {
        match self {
            Locator::Url { url } => url.clone(),
            Locator::File { path, line, col } => match (line, col) {
                (Some(l), Some(c)) => format!("{path}:{l}:{c}"),
                (Some(l), None) => format!("{path}:{l}"),
                _ => path.clone(),
            },
        }
    }
}

fn is_url(s: &str) -> bool {
    s.starts_with("http://") || s.starts_with("https://")
}

fn split_path_line_col(s: &str) -> (String, Option<u32>, Option<u32>) {
    // Try `path:line:col`, then `path:line`, then bare `path`.
    if let Some((head, last)) = s.rsplit_once(':') {
        if let Ok(n1) = last.parse::<u32>() {
            if let Some((head2, mid)) = head.rsplit_once(':') {
                if let Ok(n2) = mid.parse::<u32>() {
                    return (head2.to_string(), Some(n2), Some(n1));
                }
            }
            return (head.to_string(), Some(n1), None);
        }
    }
    (s.to_string(), None, None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_path_with_line_and_col() {
        assert_eq!(
            Locator::parse("src/order/total.rs:32:10"),
            Locator::File {
                path: "src/order/total.rs".to_string(),
                line: Some(32),
                col: Some(10),
            }
        );
    }

    #[test]
    fn parses_bare_path_and_line_only() {
        assert_eq!(
            Locator::parse("docs/policy.md"),
            Locator::File {
                path: "docs/policy.md".to_string(),
                line: None,
                col: None,
            }
        );
        assert_eq!(
            Locator::parse("src/x.rs:12"),
            Locator::File {
                path: "src/x.rs".to_string(),
                line: Some(12),
                col: None,
            }
        );
    }

    #[test]
    fn detects_url() {
        assert_eq!(
            Locator::parse("https://rules.acme.com/x#y"),
            Locator::Url {
                url: "https://rules.acme.com/x#y".to_string()
            }
        );
    }

    #[test]
    fn render_round_trips_the_surface_form() {
        for s in ["a/b.rs", "a/b.rs:1", "a/b.rs:1:2", "https://e.com/x"] {
            assert_eq!(Locator::parse(s).render(), s);
        }
    }
}
