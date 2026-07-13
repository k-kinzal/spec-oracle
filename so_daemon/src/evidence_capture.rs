//! Asynchronous Evidence capture for an accepted Specification Node.
//!
//! The Add path persists caller-supplied descriptors verbatim and performs no
//! Evidence interpretation or I/O. This Job expands those descriptors, captures
//! each locator, stores snapshot bytes by content hash, enriches origin, and
//! atomically appends the captured Evidence plus its durable Job result.

use serde_json::json;

use crate::domain::{Evidence, Node};
use crate::evidence::{self, EvidenceInput};
use crate::jobs::{JobOutput, NodeMetaPlugin, PluginContext, PluginRegistration};
use crate::{origin, snapshot};

pub const PLUGIN_NAME: &str = "evidence-capture";
pub const CAPTURE_VERSION: &str = "evidence-capture/v1";

pub fn needs_capture(node: &Node) -> bool {
    !node.meta.evidence_requests.is_empty()
        && !node.meta.updates.values().any(|update| {
            update.source == PLUGIN_NAME
                && update
                    .value
                    .get("version")
                    .and_then(serde_json::Value::as_str)
                    == Some(CAPTURE_VERSION)
        })
}

pub struct EvidenceCapturePlugin;

impl NodeMetaPlugin for EvidenceCapturePlugin {
    fn handles(&self, node: &Node) -> bool {
        needs_capture(node)
    }

    fn run(&self, node: &Node, context: &PluginContext<'_>) -> Result<JobOutput, String> {
        let inputs = match parse_requests(&node.meta.evidence_requests) {
            Ok(inputs) => inputs,
            Err(error) => {
                // Shape errors cannot be repaired by retrying I/O. Preserve the
                // accepted specification and append a durable rejected result.
                tracing::warn!(
                    "error.message" = %error,
                    "Evidence descriptor rejected by asynchronous capture Job"
                );
                return Ok(JobOutput::metadata(json!({
                    "version": CAPTURE_VERSION,
                    "status": "rejected",
                    "error": error.to_string(),
                })));
            }
        };

        let enrichers = origin::registered_enrichers();
        let mut captured = Vec::with_capacity(inputs.len());
        for (index, input) in inputs.into_iter().enumerate() {
            let span = tracing::info_span!(
                "spec.job.evidence.capture",
                "spec.evidence.index" = index as u64,
                "spec.evidence.kind" = ?input.kind,
                "spec.snapshot.bytes" = tracing::field::Empty,
                "spec.snapshot.hash" = tracing::field::Empty,
            );
            let _entered = span.enter();
            let capture = snapshot::capture(&input.locator, context.now)
                .map_err(|error| error.to_string())?;
            tracing::Span::current().record("spec.snapshot.bytes", capture.snapshot.bytes as u64);
            tracing::Span::current()
                .record("spec.snapshot.hash", capture.snapshot.content_hash.as_str());
            context
                .blobs
                .put_blob(&capture.snapshot.content_hash, &capture.blob)
                .map_err(|error| error.to_string())?;
            let final_origin = origin::finalize(
                &input.locator,
                &input.origin,
                &capture.origin_hints,
                &enrichers,
            );
            captured.push(Evidence {
                kind: input.kind,
                locator: input.locator,
                snapshot: capture.snapshot,
                origin: final_origin,
            });
        }

        let value = json!({
            "version": CAPTURE_VERSION,
            "status": "captured",
            "evidence_count": captured.len(),
            // Preserve the complete capture in this versioned append-only
            // Job result even though meta.evidence is the convenient
            // current captured view.
            "evidence": captured,
        });
        Ok(JobOutput::captured_evidence(value, captured))
    }
}

fn parse_requests(values: &[String]) -> Result<Vec<EvidenceInput>, evidence::EvidenceError> {
    let mut inputs = Vec::new();
    for value in values {
        inputs.extend(evidence::parse_value(value)?);
    }
    Ok(inputs)
}

fn make_plugin() -> Box<dyn NodeMetaPlugin> {
    Box::new(EvidenceCapturePlugin)
}

inventory::submit! {
    PluginRegistration::new(PLUGIN_NAME, make_plugin)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, Node};

    fn node(requests: Vec<String>) -> Node {
        Node {
            id: "n1".into(),
            statement: "The pump shall stop.".into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: requests,
                evidence: vec![],
                created_at: "t".into(),
                cli: "spec".into(),
                cli_version: "test".into(),
                updates: Default::default(),
            },
        }
    }

    #[test]
    fn only_nodes_with_unfinished_requests_need_capture() {
        assert!(!needs_capture(&node(vec![])));
        let mut pending = node(vec!["README.md".into()]);
        assert!(needs_capture(&pending));
        pending.meta.updates.insert(
            "job".into(),
            crate::domain::MetaUpdate {
                source: PLUGIN_NAME.into(),
                applied_at: "t".into(),
                value: json!({"version": CAPTURE_VERSION, "status": "captured"}),
            },
        );
        assert!(!needs_capture(&pending));
    }

    #[test]
    fn malformed_requests_are_durable_rejections_not_retry_errors() {
        let graph = crate::store::InMemoryNodeStore::new();
        let temp = tempfile::tempdir().unwrap();
        let blobs = crate::store::FileBlobStore::open(temp.path()).unwrap();
        let output = EvidenceCapturePlugin
            .run(
                &node(vec!["{".into()]),
                &PluginContext {
                    blobs: &blobs,
                    graph: &graph,
                    now: "t",
                },
            )
            .expect("a permanent descriptor error is a durable Job result");
        assert_eq!(output.value["status"], "rejected");
        assert!(output.value["error"]
            .as_str()
            .unwrap()
            .contains("invalid evidence JSON"));
        assert!(output.evidence.is_none());
    }
}
