//! Asynchronous Evidence capture for an accepted Specification Node.
//!
//! The Add path persists caller-supplied descriptors verbatim and performs no
//! Evidence interpretation or I/O. This Consumer expands those descriptors, captures
//! each locator, stores snapshot bytes by content hash, enriches origin, and
//! creates or reuses content-addressed Evidence graph Nodes, and atomically
//! appends the captured Evidence plus its durable Consumer result.

use serde_json::{json, Value};

use crate::domain::{Derivation, DerivedNode, Edge, EdgeKind, Evidence, Node};
use crate::evidence::{self, EvidenceInput};
use crate::store::{BlobStore, GraphStore};
use crate::{origin, snapshot};

pub const PLUGIN_NAME: &str = "evidence-capture";
pub const CAPTURE_VERSION: &str = "evidence-capture/v2";
/// Persisted marker for an explicit complete Evidence-request replacement.
/// Its generation participates in the capture fingerprint, so a daemon crash
/// cannot make a refresh with unchanged descriptors look already complete.
pub const REQUEST_UPDATE_SOURCE: &str = "evidence-requests";

pub fn evidence_derivation() -> Derivation {
    Derivation {
        method: PLUGIN_NAME.to_string(),
        version: CAPTURE_VERSION.to_string(),
    }
}

pub fn needs_capture(node: &Node) -> bool {
    let fingerprint = request_fingerprint(node);
    !node.meta.evidence_requests.is_empty()
        && !node.meta.updates.values().any(|update| {
            update.source == PLUGIN_NAME
                && update
                    .value
                    .get("version")
                    .and_then(serde_json::Value::as_str)
                    == Some(CAPTURE_VERSION)
                && update
                    .value
                    .get("request_fingerprint")
                    .and_then(serde_json::Value::as_str)
                    == Some(fingerprint.as_str())
        })
}

pub struct EvidenceCaptureRecord {
    pub metadata: Value,
    pub evidence: Vec<Evidence>,
    pub captured: bool,
}

pub fn capture(
    node: &Node,
    graph: &(dyn GraphStore + Send + Sync),
    blobs: &(dyn BlobStore + Send + Sync),
    now: &str,
) -> Result<EvidenceCaptureRecord, String> {
    let request_fingerprint = request_fingerprint(node);
    let inputs = match parse_requests(&node.meta.evidence_requests) {
        Ok(inputs) => inputs,
        Err(error) => {
            // Shape errors cannot be repaired by retrying I/O. Preserve the
            // accepted specification and append a durable rejected result.
            tracing::warn!(
                "error.message" = %error,
                "Evidence descriptor rejected by asynchronous capture Consumer"
            );
            return Ok(EvidenceCaptureRecord {
                metadata: json!({
                    "version": CAPTURE_VERSION,
                    "request_fingerprint": request_fingerprint,
                    "status": "rejected",
                    "error": error.to_string(),
                }),
                evidence: Vec::new(),
                captured: false,
            });
        }
    };

    let request_count = inputs.len();
    let enrichers = origin::registered_enrichers();
    let mut captured = Vec::with_capacity(request_count);
    let mut unavailable = Vec::new();
    for (index, input) in inputs.into_iter().enumerate() {
        let span = tracing::info_span!(
            "spec.consumer.evidence.capture",
            "spec.evidence.index" = index as u64,
            "spec.evidence.kind" = ?input.kind,
            "spec.snapshot.bytes" = tracing::field::Empty,
            "spec.snapshot.hash" = tracing::field::Empty,
        );
        let _entered = span.enter();
        let capture = match snapshot::capture(&input.locator, now) {
            Ok(capture) => capture,
            Err(error) => {
                let Some(reason) = durable_unavailability_reason(&error) else {
                    return Err(error.to_string());
                };
                tracing::warn!(
                    "spec.evidence.index" = index as u64,
                    "spec.evidence.kind" = input.kind.as_str(),
                    "spec.evidence.locator" = %input.locator.render(),
                    "evidence.unavailable.reason" = reason,
                    "error.message" = %error,
                    "Evidence locator was unavailable at capture time"
                );
                unavailable.push(json!({
                    "request_index": index,
                    "kind": input.kind.as_str(),
                    "locator": input.locator.render(),
                    "status": "unavailable",
                    "reason": reason,
                    "error": error.to_string(),
                }));
                continue;
            }
        };
        tracing::Span::current().record("spec.snapshot.bytes", capture.snapshot.bytes as u64);
        tracing::Span::current()
            .record("spec.snapshot.hash", capture.snapshot.content_hash.as_str());
        blobs
            .put_blob(&capture.snapshot.content_hash, &capture.blob)
            .map_err(|error| error.to_string())?;
        let final_origin = origin::finalize(
            &input.locator,
            &input.origin,
            &capture.origin_hints,
            &enrichers,
        );
        let evidence = Evidence {
            kind: input.kind,
            locator: input.locator,
            snapshot: capture.snapshot,
            origin: final_origin,
        };
        captured.push(evidence);
    }

    let mut evidence_nodes_inserted = 0_usize;
    let mut evidence_edges_inserted = 0_usize;
    for evidence in &captured {
        let evidence_node = DerivedNode::evidence(evidence.clone());
        let edge = Edge::projection(
            EdgeKind::GroundedBy,
            &node.id,
            evidence_node.id(),
            evidence_derivation(),
            now,
        )
        .expect("captured Evidence always forms a valid projection");
        let write = graph
            .put_derived_node(&evidence_node, &edge)
            .map_err(|error| error.to_string())?;
        evidence_nodes_inserted += usize::from(write.node_inserted);
        evidence_edges_inserted += usize::from(write.edge_inserted);
    }

    let status = if unavailable.is_empty() {
        "captured"
    } else if captured.is_empty() {
        "unavailable"
    } else {
        "partial"
    };
    let value = json!({
        "version": CAPTURE_VERSION,
        "request_fingerprint": request_fingerprint,
        "status": status,
        "request_count": request_count,
        "evidence_count": captured.len(),
        "unavailable_count": unavailable.len(),
        "unavailable": unavailable,
        "evidence_nodes_inserted": evidence_nodes_inserted,
        "evidence_edges_inserted": evidence_edges_inserted,
        // Preserve the complete capture in this versioned append-only
        // Consumer result even though meta.evidence is the convenient
        // current captured view.
        "evidence": captured,
    });
    Ok(EvidenceCaptureRecord {
        metadata: value,
        evidence: captured,
        captured: status != "unavailable",
    })
}

fn durable_unavailability_reason(error: &snapshot::SnapshotError) -> Option<&'static str> {
    match error {
        snapshot::SnapshotError::NotFound(_) => Some("file_not_found"),
        snapshot::SnapshotError::Read { source, .. }
            if source.kind() == std::io::ErrorKind::NotFound =>
        {
            Some("file_not_found")
        }
        snapshot::SnapshotError::LineOutOfRange { .. } => Some("line_out_of_range"),
        snapshot::SnapshotError::Read { .. }
        | snapshot::SnapshotError::Fetch { .. }
        | snapshot::SnapshotError::Body { .. } => None,
    }
}

fn request_fingerprint(node: &Node) -> String {
    let mut values = node.meta.evidence_requests.clone();
    values.sort();
    values.dedup();
    let mut parts: Vec<&str> = values.iter().map(String::as_str).collect();
    if !node.meta.evidence_request_generation.is_empty() {
        parts.push(node.meta.evidence_request_generation.as_str());
    }
    crate::identity::derive_id("evidence-requests", &parts)
}

fn parse_requests(values: &[String]) -> Result<Vec<EvidenceInput>, evidence::EvidenceError> {
    let mut inputs = Vec::new();
    for value in values {
        inputs.extend(evidence::parse_value(value)?);
    }
    Ok(inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, Node};
    use crate::store::GraphStore;

    fn node(requests: Vec<String>) -> Node {
        Node {
            id: "n1".into(),
            statement: "The pump shall stop.".into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: requests,
                evidence_request_generation: String::new(),
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
        pending.meta.updates.get_mut("job").unwrap().value["request_fingerprint"] =
            json!(request_fingerprint(&pending));
        assert!(!needs_capture(&pending));

        pending.meta.evidence_requests.push("another.rs:1".into());
        assert!(needs_capture(&pending));
    }

    #[test]
    fn explicit_generation_forces_unchanged_descriptors_to_recapture() {
        let mut captured = node(vec!["README.md:1".into()]);
        let fingerprint = request_fingerprint(&captured);
        captured.meta.updates.insert(
            "old-capture".into(),
            crate::domain::MetaUpdate {
                source: PLUGIN_NAME.into(),
                applied_at: "t1".into(),
                value: json!({
                    "version": CAPTURE_VERSION,
                    "request_fingerprint": fingerprint,
                    "status": "captured"
                }),
            },
        );
        assert!(!needs_capture(&captured));

        captured.meta.evidence_request_generation = "replacement-2".into();
        assert!(
            needs_capture(&captured),
            "persisted replacement generation survives a crash and invalidates the prior capture"
        );
    }

    #[test]
    fn malformed_requests_are_durable_rejections_not_retry_errors() {
        let graph = crate::store::InMemoryNodeStore::new();
        let temp = tempfile::tempdir().unwrap();
        let blobs = crate::store::FileBlobStore::open(temp.path()).unwrap();
        let capture = capture(&node(vec!["{".into()]), &graph, &blobs, "t")
            .expect("a permanent descriptor error is a durable Consumer result");
        let value = &capture.metadata;
        assert_eq!(value["status"], "rejected");
        assert!(value["error"]
            .as_str()
            .unwrap()
            .contains("invalid evidence JSON"));
        assert!(capture.evidence.is_empty());
        assert!(!capture.captured);
    }

    #[test]
    fn missing_file_is_a_durable_unavailable_result() {
        let graph = crate::store::InMemoryNodeStore::new();
        let temp = tempfile::tempdir().unwrap();
        let blobs = crate::store::FileBlobStore::open(temp.path()).unwrap();
        let missing = temp.path().join("removed.md");
        let request = json!({
            "kind": "constitutive",
            "locator": missing.to_string_lossy(),
        })
        .to_string();

        let capture = capture(&node(vec![request]), &graph, &blobs, "t").unwrap();

        assert!(!capture.captured);
        assert!(capture.evidence.is_empty());
        assert_eq!(capture.metadata["status"], "unavailable");
        assert_eq!(capture.metadata["request_count"], 1);
        assert_eq!(capture.metadata["evidence_count"], 0);
        assert_eq!(capture.metadata["unavailable_count"], 1);
        assert_eq!(
            capture.metadata["unavailable"][0]["reason"],
            "file_not_found"
        );
        assert_eq!(
            capture.metadata["unavailable"][0]["locator"],
            missing.to_string_lossy().as_ref()
        );
    }

    #[test]
    fn capture_keeps_available_requests_when_another_is_unavailable() {
        let graph = crate::store::InMemoryNodeStore::new();
        let temp = tempfile::tempdir().unwrap();
        let blobs = crate::store::FileBlobStore::open(temp.path()).unwrap();
        let available = temp.path().join("available.txt");
        let missing = temp.path().join("removed.txt");
        std::fs::write(&available, "captured bytes").unwrap();
        let requests = [available, missing]
            .into_iter()
            .map(|path| {
                json!({
                    "kind": "assertoric",
                    "locator": path.to_string_lossy(),
                })
                .to_string()
            })
            .collect();

        let capture = capture(&node(requests), &graph, &blobs, "t").unwrap();

        assert!(capture.captured);
        assert_eq!(capture.evidence.len(), 1);
        assert_eq!(capture.metadata["status"], "partial");
        assert_eq!(capture.metadata["request_count"], 2);
        assert_eq!(capture.metadata["evidence_count"], 1);
        assert_eq!(capture.metadata["unavailable_count"], 1);
        let edges = graph
            .list_edges(&["n1".into()], &[evidence_derivation()])
            .unwrap();
        assert_eq!(edges.len(), 1);
    }

    #[test]
    fn transient_snapshot_failures_remain_retryable() {
        let read_error = snapshot::SnapshotError::Read {
            path: "restricted".into(),
            source: std::io::Error::new(std::io::ErrorKind::PermissionDenied, "denied"),
        };
        assert_eq!(durable_unavailability_reason(&read_error), None);
        let disappeared = snapshot::SnapshotError::Read {
            path: "removed".into(),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "gone"),
        };
        assert_eq!(
            durable_unavailability_reason(&disappeared),
            Some("file_not_found")
        );
    }

    #[test]
    fn capture_persists_one_reusable_evidence_node_and_projection_edge() {
        let graph = crate::store::InMemoryNodeStore::new();
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("evidence.txt");
        std::fs::write(&path, "captured bytes").unwrap();
        let blobs = crate::store::FileBlobStore::open(&temp.path().join("blobs")).unwrap();
        let source = node(vec![path.to_string_lossy().into_owned()]);

        let capture = capture(&source, &graph, &blobs, "2026-07-14T00:00:00Z").unwrap();
        let value = &capture.metadata;
        assert_eq!(value["evidence_nodes_inserted"], 1);
        assert_eq!(value["evidence_edges_inserted"], 1);

        let edges = graph
            .list_edges(&[source.id], &[evidence_derivation()])
            .unwrap();
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].kind, EdgeKind::GroundedBy);
        let nodes = graph.get_derived_nodes(&[edges[0].target.clone()]).unwrap();
        assert!(matches!(nodes.as_slice(), [DerivedNode::Evidence { .. }]));
    }
}
