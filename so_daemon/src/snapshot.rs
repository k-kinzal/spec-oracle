//! Snapshot capture (provenance sense ②: our own observation).
//!
//! When evidence is ingested, the daemon *captures* what the locator pointed at
//! **at that moment** and hashes it, so the grounding can later be checked for
//! drift independently of the live source. This is a self-observed fact: unlike
//! the source's own provenance (sense ①), the snapshot is something we did and
//! can stand behind.
//!
//! * File locators capture the cited line region (with a few lines of context)
//!   and pin the repository commit, warning when the working tree is dirty.
//! * URL locators fetch the resource, recording status, content type, and the
//!   `Last-Modified` header as the anchor.
//!
//! The raw captured bytes are hashed (SHA-256); the caller persists them in the
//! content-addressed blob store. The [`Anchor`]/[`Snapshot`] value types are
//! defined in the daemon domain; this module produces them.
//!
//! Capture reads the daemon's own filesystem and reaches the network, so it must
//! run off the async reactor (the daemon dispatches it via `spawn_blocking`).

use std::io::Read;
use std::path::Path;
use std::time::Duration;

use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::domain::{Anchor, Locator, Snapshot};

use crate::evidence::OriginInput;

/// Lines of context captured on each side of a cited line.
const FILE_CONTEXT_LINES: usize = 3;

/// Upper bound on a fetched URL body, to keep captures bounded.
const MAX_FETCH_BYTES: usize = 1_048_576; // 1 MiB

/// HTTP timeout for URL captures.
const FETCH_TIMEOUT: Duration = Duration::from_secs(20);

/// The result of a capture: the snapshot, the raw bytes to persist as a blob,
/// and any origin hints discovered while capturing (sense ①, e.g. URL metadata).
pub struct Capture {
    pub snapshot: Snapshot,
    pub blob: Vec<u8>,
    pub origin_hints: OriginInput,
}

#[derive(Debug, Error)]
pub enum SnapshotError {
    #[error("evidence file not found: {0}")]
    NotFound(String),
    #[error("failed to read evidence file '{path}': {source}")]
    Read {
        path: String,
        source: std::io::Error,
    },
    #[error("line {line} is out of range for '{path}' ({total} lines)")]
    LineOutOfRange {
        path: String,
        line: u32,
        total: usize,
    },
    #[error("failed to fetch '{url}': {source}")]
    Fetch {
        url: String,
        #[source]
        source: Box<ureq::Error>,
    },
    #[error("failed to read response body from '{url}': {source}")]
    Body { url: String, source: std::io::Error },
}

/// Capture a locator at the given wall-clock instant (RFC 3339, UTC).
pub fn capture(locator: &Locator, now: &str) -> Result<Capture, SnapshotError> {
    let span = tracing::debug_span!(
        "spec.snapshot.capture",
        "spec.locator.type" = locator_type(locator),
        "spec.locator.has_line" = locator_has_line(locator),
    );
    let _entered = span.enter();
    match locator {
        Locator::File { path, line, col } => capture_file(path, *line, *col, now),
        Locator::Url { url } => capture_url(url, now),
    }
}

fn capture_file(
    path: &str,
    line: Option<u32>,
    _col: Option<u32>,
    now: &str,
) -> Result<Capture, SnapshotError> {
    let p = Path::new(path);
    if !p.exists() {
        return Err(SnapshotError::NotFound(path.to_string()));
    }
    let raw = std::fs::read(p).map_err(|source| SnapshotError::Read {
        path: path.to_string(),
        source,
    })?;
    let text = String::from_utf8_lossy(&raw);

    // Select the region: the cited line plus context, or the whole file if no
    // line was cited.
    let (region_text, region_bytes) = match line {
        Some(l) => {
            let lines: Vec<&str> = text.lines().collect();
            let idx = (l as usize).checked_sub(1);
            let total = lines.len();
            match idx {
                Some(i) if i < total => {
                    let start = i.saturating_sub(FILE_CONTEXT_LINES);
                    let end = (i + FILE_CONTEXT_LINES + 1).min(total);
                    let region = lines[start..end].join("\n");
                    let bytes = region.clone().into_bytes();
                    (region, bytes)
                }
                _ => {
                    return Err(SnapshotError::LineOutOfRange {
                        path: path.to_string(),
                        line: l,
                        total,
                    })
                }
            }
        }
        None => (text.to_string(), raw.clone()),
    };

    let anchor = git_anchor(p);
    let content_hash = hash_hex(&region_bytes);
    Ok(Capture {
        snapshot: Snapshot {
            content: region_text,
            content_hash,
            bytes: region_bytes.len(),
            captured_at: now.to_string(),
            anchor,
        },
        blob: region_bytes,
        origin_hints: OriginInput::default(),
    })
}

/// Pin the git commit for a file, flagging a dirty working tree. Falls back to
/// [`Anchor::Worktree`] when the file is not under version control.
///
/// git runs with its working directory set to the file's parent, so the pathspec
/// must be the file name relative to that directory — not the full (possibly
/// repo-relative) locator, which would be resolved against the parent again and
/// match nothing.
fn git_anchor(path: &Path) -> Anchor {
    let dir = path.parent().filter(|p| !p.as_os_str().is_empty());
    let commit = run_git(dir, &["rev-parse", "HEAD"]);
    match commit {
        Some(commit) if !commit.is_empty() => {
            let dirty = match path.file_name() {
                Some(name) => run_git(
                    dir,
                    &["status", "--porcelain", "--", &name.to_string_lossy()],
                )
                .map(|s| !s.trim().is_empty())
                .unwrap_or(false),
                None => false,
            };
            Anchor::Git { commit, dirty }
        }
        _ => Anchor::Worktree,
    }
}

pub(crate) fn run_git(dir: Option<&Path>, args: &[&str]) -> Option<String> {
    let mut cmd = std::process::Command::new("git");
    if let Some(d) = dir {
        cmd.current_dir(d);
    }
    cmd.args(args);
    let out = cmd.output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn capture_url(url: &str, now: &str) -> Result<Capture, SnapshotError> {
    let _span = tracing::debug_span!("spec.snapshot.fetch_url").entered();
    let agent = ureq::AgentBuilder::new().timeout(FETCH_TIMEOUT).build();
    let resp = match agent.get(url).call() {
        Ok(r) => r,
        // A 4xx/5xx still yields a response we can snapshot.
        Err(ureq::Error::Status(_, r)) => r,
        Err(e) => {
            return Err(SnapshotError::Fetch {
                url: url.to_string(),
                source: Box::new(e),
            })
        }
    };
    let status = resp.status();
    let content_type = resp.header("Content-Type").map(str::to_string);
    let last_modified = resp.header("Last-Modified").map(str::to_string);

    let mut buf = Vec::new();
    resp.into_reader()
        .take(MAX_FETCH_BYTES as u64)
        .read_to_end(&mut buf)
        .map_err(|source| SnapshotError::Body {
            url: url.to_string(),
            source,
        })?;

    let text = String::from_utf8_lossy(&buf).to_string();
    let origin_hints = extract_web_origin(&text);
    let content_hash = hash_hex(&buf);
    Ok(Capture {
        snapshot: Snapshot {
            content: text,
            content_hash,
            bytes: buf.len(),
            captured_at: now.to_string(),
            anchor: Anchor::Web {
                retrieved_at: now.to_string(),
                status,
                content_type,
                last_modified,
            },
        },
        blob: buf,
        origin_hints,
    })
}

fn locator_type(locator: &Locator) -> &'static str {
    match locator {
        Locator::File { .. } => "file",
        Locator::Url { .. } => "url",
    }
}

fn locator_has_line(locator: &Locator) -> bool {
    matches!(locator, Locator::File { line: Some(_), .. })
}

/// Best-effort extraction of authorship/date hints from HTML meta tags.
fn extract_web_origin(html: &str) -> OriginInput {
    OriginInput {
        author: meta_content(html, "author").or_else(|| meta_property(html, "article:author")),
        created_at: meta_property(html, "article:published_time"),
        updated_at: meta_property(html, "article:modified_time"),
    }
}

fn meta_content(html: &str, name: &str) -> Option<String> {
    find_meta(html, "name", name)
}

fn meta_property(html: &str, property: &str) -> Option<String> {
    find_meta(html, "property", property)
}

/// A deliberately small, dependency-free scan for `<meta {attr}="{value}"
/// content="...">`. Not a full HTML parser — best effort, order-insensitive.
fn find_meta(html: &str, attr: &str, value: &str) -> Option<String> {
    let needle = format!("{attr}=\"{value}\"");
    let lower = html.to_ascii_lowercase();
    let mut from = 0;
    while let Some(rel) = lower[from..].find(&needle) {
        let at = from + rel;
        // Find the enclosing tag start.
        let tag_start = lower[..at].rfind("<meta").unwrap_or(at);
        let tag_end = lower[at..].find('>').map(|e| at + e).unwrap_or(html.len());
        let tag = &html[tag_start..tag_end];
        if let Some(content) = attr_value(tag, "content") {
            if !content.trim().is_empty() {
                return Some(content.trim().to_string());
            }
        }
        from = tag_end;
    }
    None
}

fn attr_value(tag: &str, attr: &str) -> Option<String> {
    let lower = tag.to_ascii_lowercase();
    let key = format!("{attr}=\"");
    let start = lower.find(&key)? + key.len();
    let end = tag[start..].find('"')? + start;
    Some(tag[start..end].to_string())
}

pub(crate) fn hash_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    let mut s = String::with_capacity(digest.len() * 2);
    for b in digest {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn hash_is_stable_sha256() {
        // Known SHA-256 of "abc".
        assert_eq!(
            hash_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn capture_file_region_with_context() {
        let mut f = tempfile::NamedTempFile::new().unwrap();
        writeln!(f, "line1\nline2\nline3\nline4\nline5\nline6\nline7").unwrap();
        let path = f.path().to_string_lossy().to_string();
        let loc = Locator::File {
            path,
            line: Some(4),
            col: None,
        };
        let cap = capture(&loc, "2026-07-05T00:00:00Z").unwrap();
        // Line 4 with 3 lines of context on each side → lines 1..=7.
        assert!(cap.snapshot.content.contains("line1"));
        assert!(cap.snapshot.content.contains("line4"));
        assert!(cap.snapshot.content.contains("line7"));
        assert_eq!(cap.snapshot.content_hash, hash_hex(cap.blob.as_slice()));
        assert_eq!(cap.snapshot.captured_at, "2026-07-05T00:00:00Z");
    }

    #[test]
    fn capture_file_narrow_context_at_top() {
        let mut f = tempfile::NamedTempFile::new().unwrap();
        writeln!(f, "alpha\nbeta\ngamma").unwrap();
        let path = f.path().to_string_lossy().to_string();
        let loc = Locator::File {
            path,
            line: Some(1),
            col: None,
        };
        let cap = capture(&loc, "t").unwrap();
        assert!(cap.snapshot.content.starts_with("alpha"));
    }

    #[test]
    fn capture_file_missing_is_error() {
        let loc = Locator::File {
            path: "/no/such/file/xyz.rs".to_string(),
            line: None,
            col: None,
        };
        assert!(matches!(
            capture(&loc, "t"),
            Err(SnapshotError::NotFound(_))
        ));
    }

    #[test]
    fn capture_file_line_out_of_range() {
        let mut f = tempfile::NamedTempFile::new().unwrap();
        writeln!(f, "only one line").unwrap();
        let path = f.path().to_string_lossy().to_string();
        let loc = Locator::File {
            path,
            line: Some(99),
            col: None,
        };
        assert!(matches!(
            capture(&loc, "t"),
            Err(SnapshotError::LineOutOfRange { line: 99, .. })
        ));
    }

    #[test]
    fn extract_web_origin_from_meta() {
        let html = r#"<html><head>
            <meta name="author" content="Jane Doe">
            <meta property="article:published_time" content="2024-01-02T00:00:00Z">
            </head></html>"#;
        let o = extract_web_origin(html);
        assert_eq!(o.author.as_deref(), Some("Jane Doe"));
        assert_eq!(o.created_at.as_deref(), Some("2024-01-02T00:00:00Z"));
    }
}
