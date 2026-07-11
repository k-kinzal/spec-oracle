//! GitHub Evidence Meta Plugin.
//!
//! GitHub evidence URLs are resolved to an immutable commit through the GitHub
//! REST API. For `/blob/REF/PATH` URLs the Plugin captures the file at that
//! commit from `raw.githubusercontent.com`; other repository URLs snapshot the
//! commit API response. Bytes remain in the BlobStore and the Node receives
//! only the resulting hash and related commit information.

use std::io::Read;
use std::time::Duration;

use percent_encoding::percent_decode_str;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use url::Url;

use crate::domain::{Locator, Node};
use crate::jobs::{NodeMetaPlugin, PluginContext, PluginRegistration};

const MAX_FETCH_BYTES: usize = 16 * 1024 * 1024;
const FETCH_TIMEOUT: Duration = Duration::from_secs(20);

pub struct GithubEvidencePlugin;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Target {
    source_url: String,
    owner: String,
    repository: String,
    reference: String,
    path: Option<Vec<String>>,
}

impl NodeMetaPlugin for GithubEvidencePlugin {
    fn handles(&self, node: &Node) -> bool {
        github_targets(node).next().is_some()
    }

    fn run(&self, node: &Node, context: &PluginContext<'_>) -> Result<Value, String> {
        let targets: Vec<Target> = github_targets(node).collect();
        let mut resolved = Vec::with_capacity(targets.len());
        for target in targets {
            resolved.push(resolve(target, context)?);
        }
        Ok(json!({ "evidence": resolved }))
    }
}

fn github_targets(node: &Node) -> impl Iterator<Item = Target> + '_ {
    node.meta.evidence.iter().filter_map(|evidence| {
        let Locator::Url { url } = &evidence.locator else {
            return None;
        };
        parse_target(url)
    })
}

fn parse_target(source: &str) -> Option<Target> {
    let url = Url::parse(source).ok()?;
    if url.scheme() != "https" || !matches!(url.host_str(), Some("github.com")) {
        return None;
    }
    let segments: Vec<String> = url
        .path_segments()?
        .filter(|segment| !segment.is_empty())
        .map(decode_segment)
        .collect();
    if segments.len() < 2 {
        return None;
    }
    let owner = segments[0].clone();
    let repository = segments[1].trim_end_matches(".git").to_string();
    if owner.is_empty() || repository.is_empty() {
        return None;
    }

    let (reference, path) = match segments.get(2).map(String::as_str) {
        Some("commit") => (segments.get(3)?.clone(), None),
        Some("blob") => {
            let reference = segments.get(3)?.clone();
            let path: Vec<String> = segments.iter().skip(4).cloned().collect();
            if path.is_empty() {
                return None;
            }
            (reference, Some(path))
        }
        Some("tree") => (segments.get(3)?.clone(), None),
        _ => ("HEAD".to_string(), None),
    };

    Some(Target {
        source_url: source.to_string(),
        owner,
        repository,
        reference,
        path,
    })
}

fn resolve(target: Target, context: &PluginContext<'_>) -> Result<Value, String> {
    let api_url = api_commit_url(&target)?;
    let api_bytes = fetch(&api_url, "application/vnd.github+json")?;
    let commit: Value = serde_json::from_slice(&api_bytes)
        .map_err(|error| format!("GitHub commit response was not JSON: {error}"))?;
    let sha = commit
        .get("sha")
        .and_then(Value::as_str)
        .ok_or_else(|| "GitHub commit response did not contain sha".to_string())?;
    let commit_url = commit
        .get("html_url")
        .and_then(Value::as_str)
        .unwrap_or_default();

    let (snapshot_bytes, snapshot_url) = match &target.path {
        Some(path) => {
            let raw_url = raw_content_url(&target, sha, path)?;
            let bytes = fetch(&raw_url, "application/octet-stream")?;
            (bytes, raw_url)
        }
        None => (api_bytes, api_url),
    };
    let content_hash = hash_bytes(&snapshot_bytes);
    context
        .blobs
        .put_blob(&content_hash, &snapshot_bytes)
        .map_err(|error| error.to_string())?;

    Ok(json!({
        "source_url": target.source_url,
        "repository": format!("{}/{}", target.owner, target.repository),
        "commit": sha,
        "commit_url": commit_url,
        "author": commit.pointer("/commit/author/name").and_then(Value::as_str),
        "authored_at": commit.pointer("/commit/author/date").and_then(Value::as_str),
        "committed_at": commit.pointer("/commit/committer/date").and_then(Value::as_str),
        "path": target.path.map(|parts| parts.join("/")),
        "snapshot": {
            "url": snapshot_url,
            "content_hash": content_hash,
            "bytes": snapshot_bytes.len(),
            "captured_at": context.now,
        }
    }))
}

fn api_commit_url(target: &Target) -> Result<String, String> {
    let mut url = Url::parse("https://api.github.com").expect("static GitHub API URL");
    url.path_segments_mut()
        .map_err(|_| "GitHub API URL cannot be a base".to_string())?
        .extend([
            "repos",
            target.owner.as_str(),
            target.repository.as_str(),
            "commits",
            target.reference.as_str(),
        ]);
    Ok(url.into())
}

fn raw_content_url(target: &Target, sha: &str, path: &[String]) -> Result<String, String> {
    let mut url =
        Url::parse("https://raw.githubusercontent.com").expect("static GitHub raw-content URL");
    let mut segments = url
        .path_segments_mut()
        .map_err(|_| "GitHub raw-content URL cannot be a base".to_string())?;
    segments.extend([target.owner.as_str(), target.repository.as_str(), sha]);
    segments.extend(path.iter().map(String::as_str));
    drop(segments);
    Ok(url.into())
}

fn fetch(url: &str, accept: &str) -> Result<Vec<u8>, String> {
    let agent = ureq::AgentBuilder::new().timeout(FETCH_TIMEOUT).build();
    let mut request = agent
        .get(url)
        .set("Accept", accept)
        .set("X-GitHub-Api-Version", "2022-11-28")
        .set("User-Agent", "spec-oracle");
    if let Ok(token) = std::env::var("GITHUB_TOKEN") {
        if !token.trim().is_empty() {
            request = request.set("Authorization", &format!("Bearer {token}"));
        }
    }
    let response = request
        .call()
        .map_err(|error| format!("failed to fetch '{url}': {error}"))?;
    let mut bytes = Vec::new();
    response
        .into_reader()
        .take((MAX_FETCH_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("failed to read '{url}': {error}"))?;
    if bytes.len() > MAX_FETCH_BYTES {
        return Err(format!(
            "response from '{url}' exceeds {MAX_FETCH_BYTES} bytes"
        ));
    }
    Ok(bytes)
}

fn decode_segment(segment: &str) -> String {
    percent_decode_str(segment).decode_utf8_lossy().into_owned()
}

fn hash_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn make_github() -> Box<dyn NodeMetaPlugin> {
    Box::new(GithubEvidencePlugin)
}

inventory::submit! {
    PluginRegistration::new("github-evidence", make_github)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_blob_url_into_repository_ref_and_path() {
        let target =
            parse_target("https://github.com/openai/openai-rust/blob/main/src/lib.rs#L10").unwrap();
        assert_eq!(target.owner, "openai");
        assert_eq!(target.repository, "openai-rust");
        assert_eq!(target.reference, "main");
        assert_eq!(target.path.unwrap(), ["src", "lib.rs"]);
    }

    #[test]
    fn parses_commit_and_repository_urls() {
        let commit = parse_target("https://github.com/o/r/commit/abc123").unwrap();
        assert_eq!(commit.reference, "abc123");
        assert!(commit.path.is_none());

        let repository = parse_target("https://github.com/o/r").unwrap();
        assert_eq!(repository.reference, "HEAD");
    }

    #[test]
    fn ignores_non_github_and_non_https_urls() {
        assert!(parse_target("https://example.com/o/r").is_none());
        assert!(parse_target("http://github.com/o/r").is_none());
    }

    #[test]
    fn generated_urls_encode_path_segments() {
        let target = parse_target("https://github.com/o/r/blob/main/a%20b.txt").unwrap();
        assert_eq!(
            api_commit_url(&target).unwrap(),
            "https://api.github.com/repos/o/r/commits/main"
        );
        assert_eq!(
            raw_content_url(&target, "abc", target.path.as_ref().unwrap()).unwrap(),
            "https://raw.githubusercontent.com/o/r/abc/a%20b.txt"
        );
    }
}
