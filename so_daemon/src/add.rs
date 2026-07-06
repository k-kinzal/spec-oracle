//! The `spec add` use case: lossless ingest of a constrained-NL statement and
//! its evidence into a node.
//!
//! This is the ELT "extract/load" boundary — it captures irreducible facts and
//! defers all classification. The pipeline, per evidence:
//!   1. parse the statement into an assume-guarantee contract (grammar);
//!   2. normalize each (channel-resolved) `--evidence` value (evidence);
//!   3. snapshot the locator's content and hash it (snapshot, sense ②);
//!   4. finalize the source provenance (origin, sense ①);
//!   5. assemble the node with its creation facts (sense ③) and persist it.
//!
//! Runs entirely synchronously (filesystem, git, network, blocking DB driver).
//! The daemon calls it from `spawn_blocking`, off the async reactor.

use thiserror::Error;

use crate::domain::{Evidence, Locator, Meta, Node};
use so_lang::grammar;

use crate::evidence::{self, EvidenceInput};
use crate::origin;
use crate::snapshot;
use crate::store::{BlobStore, NodeStore};

/// Inputs to the use case. Time and identity are injected so the core stays
/// deterministic and testable; the stores are injected separately so ingest is
/// independent of any particular backend.
///
/// `evidence_values` are already channel-resolved: the client turned any
/// `@file`/`-`(stdin) descriptor into concrete text before it crossed the wire,
/// so each entry here is either a bare locator or an evidence JSON payload.
pub struct AddRequest<'a> {
    pub statement: &'a str,
    pub evidence_values: &'a [String],
    /// Node creation instant (RFC 3339, UTC) — sense ③.
    pub now: &'a str,
    pub cli: &'a str,
    pub cli_version: &'a str,
}

#[derive(Debug, Error)]
pub enum AddError {
    #[error("syntax error in statement: {0}")]
    Grammar(#[from] grammar::ParseError),
    #[error("evidence error: {0}")]
    Evidence(#[from] evidence::EvidenceError),
    #[error("snapshot error: {0}")]
    Snapshot(#[from] snapshot::SnapshotError),
    #[error("store error: {0}")]
    Store(#[from] crate::store::StoreError),
}

impl AddError {
    pub(crate) fn category(&self) -> &'static str {
        match self {
            AddError::Grammar(_) => "grammar",
            AddError::Evidence(_) => "evidence",
            AddError::Snapshot(_) => "snapshot",
            AddError::Store(_) => "store",
        }
    }

    pub(crate) fn stage(&self) -> &'static str {
        match self {
            AddError::Grammar(_) => "parse_statement",
            AddError::Evidence(_) => "parse_evidence",
            AddError::Snapshot(_) => "capture_evidence",
            AddError::Store(_) => "persist",
        }
    }

    pub(crate) fn diagnostic_kind(&self) -> &'static str {
        match self {
            AddError::Grammar(e) => parse_error_kind(e),
            AddError::Evidence(_) => "evidence_error",
            AddError::Snapshot(_) => "snapshot_error",
            AddError::Store(_) => "store_error",
        }
    }
}

/// Run `spec add`, returning the persisted node.
///
/// The snapshot bytes are written to `blobs` (content-addressed); the node —
/// carrying only the hash pointer, not the bytes — is written to `nodes`.
pub fn run(
    req: &AddRequest,
    nodes: &dyn NodeStore,
    blobs: &dyn BlobStore,
) -> Result<Node, AddError> {
    let policy = so_tracing::capture_policy();
    let run_span = tracing::info_span!(
        "spec.add.run",
        "spec.telemetry.capture" = policy.as_str(),
        "spec.statement.length" = req.statement.len() as u64,
        "spec.evidence.input_count" = req.evidence_values.len() as u64,
        "spec.evidence.normalized_count" = tracing::field::Empty,
        "spec.statement.hash" = tracing::field::Empty,
        "spec.statement.text" = tracing::field::Empty,
        "spec.parse.success" = tracing::field::Empty,
        "spec.parse.error.kind" = tracing::field::Empty,
        "spec.parse.expected_form" = tracing::field::Empty,
        "error.category" = tracing::field::Empty,
        "error.stage" = tracing::field::Empty,
        "node.id" = tracing::field::Empty,
    );
    let _run_entered = run_span.enter();
    record_statement_by_policy(policy, req.statement);

    // 1. Statement → contract. A syntax error aborts before any capture.
    let contract = {
        let parse_span = tracing::debug_span!(
            "spec.add.parse_statement",
            "spec.telemetry.capture" = policy.as_str(),
            "spec.parse.success" = tracing::field::Empty,
            "spec.parse.error.kind" = tracing::field::Empty,
            "spec.parse.expected_form" = tracing::field::Empty,
            "spec.statement.hash" = tracing::field::Empty,
            "spec.statement.text" = tracing::field::Empty,
            "error.category" = tracing::field::Empty,
            "error.stage" = tracing::field::Empty,
        );
        so_tracing::record_statement_on_span(&parse_span, policy, req.statement);
        let _span = parse_span.enter();
        match grammar::parse(req.statement) {
            Ok(contract) => {
                tracing::Span::current().record("spec.parse.success", true);
                run_span.record("spec.parse.success", true);
                contract
            }
            Err(e) => {
                record_parse_failure(policy, req.statement, &e, &run_span);
                return Err(e.into());
            }
        }
    };

    // 2. Normalize every --evidence value (each may expand to several).
    let mut inputs: Vec<EvidenceInput> = Vec::new();
    {
        let _span = tracing::debug_span!("spec.add.parse_evidence").entered();
        for value in req.evidence_values {
            inputs.extend(evidence::parse_value(value)?);
        }
    }
    tracing::Span::current().record("spec.evidence.normalized_count", inputs.len() as u64);

    let enrichers = origin::registered_enrichers();

    // 3–4. Capture + enrich each evidence entry.
    let mut evidence = Vec::with_capacity(inputs.len());
    for (index, input) in inputs.into_iter().enumerate() {
        let evidence_span = tracing::info_span!(
            "spec.add.capture_evidence",
            "spec.evidence.index" = index as u64,
            "spec.evidence.kind" = ?input.kind,
            "spec.locator.type" = locator_type(&input.locator),
            "spec.snapshot.bytes" = tracing::field::Empty,
            "spec.snapshot.hash" = tracing::field::Empty,
        );
        let _evidence_entered = evidence_span.enter();

        let capture = snapshot::capture(&input.locator, req.now)?;
        tracing::Span::current().record("spec.snapshot.bytes", capture.snapshot.bytes as u64);
        tracing::Span::current()
            .record("spec.snapshot.hash", capture.snapshot.content_hash.as_str());

        {
            let _span = tracing::debug_span!("spec.add.persist_blob").entered();
            blobs.put_blob(&capture.snapshot.content_hash, &capture.blob)?;
        }

        let final_origin = {
            let _span = tracing::debug_span!("spec.add.finalize_origin").entered();
            origin::finalize(
                &input.locator,
                &input.origin,
                &capture.origin_hints,
                &enrichers,
            )
        };
        evidence.push(Evidence {
            kind: input.kind,
            locator: input.locator,
            snapshot: capture.snapshot,
            origin: final_origin,
        });
    }

    // 5. Assemble and persist.
    let node = Node {
        id: new_id(),
        statement: req.statement.trim().to_string(),
        assumption: contract.assumption,
        guarantee: contract.guarantee,
        meta: Meta {
            evidence,
            created_at: req.now.to_string(),
            cli: req.cli.to_string(),
            cli_version: req.cli_version.to_string(),
        },
    };
    tracing::Span::current().record("node.id", node.id.as_str());
    {
        let _span = tracing::debug_span!("spec.add.persist_node").entered();
        nodes.add_contract(&node)?;
    }
    tracing::info!("node.id" = %node.id, "contract node persisted");
    Ok(node)
}

fn new_id() -> String {
    uuid::Uuid::new_v4().to_string()
}

fn record_statement_by_policy(policy: so_tracing::CapturePolicy, statement: &str) {
    if policy.allows_diagnostic() {
        let hash = so_tracing::statement_hash(statement);
        tracing::Span::current().record("spec.statement.hash", hash.as_str());
    }
    if policy.allows_content() {
        tracing::Span::current().record("spec.statement.text", statement);
    }
}

fn record_parse_failure(
    policy: so_tracing::CapturePolicy,
    statement: &str,
    error: &grammar::ParseError,
    run_span: &tracing::Span,
) {
    let error_kind = parse_error_kind(error);
    let expected_form = parse_expected_form(error);

    let parse_span = tracing::Span::current();
    for span in [&parse_span, run_span] {
        span.record("spec.parse.success", false);
        span.record("error.category", "grammar");
        span.record("error.stage", "parse_statement");
    }

    match policy {
        so_tracing::CapturePolicy::Ops => {
            tracing::warn!(
                "error.category" = "grammar",
                "error.stage" = "parse_statement",
                "spec.telemetry.capture" = policy.as_str(),
                "statement parse failed"
            );
        }
        so_tracing::CapturePolicy::Diagnostic => {
            let hash = so_tracing::statement_hash(statement);
            for span in [&parse_span, run_span] {
                span.record("spec.parse.error.kind", error_kind);
                span.record("spec.parse.expected_form", expected_form);
                span.record("spec.statement.hash", hash.as_str());
            }
            tracing::warn!(
                "error.category" = "grammar",
                "error.stage" = "parse_statement",
                "error.kind" = error_kind,
                "spec.parse.expected_form" = expected_form,
                "spec.statement.hash" = %hash,
                "spec.telemetry.capture" = policy.as_str(),
                "statement parse failed"
            );
        }
        so_tracing::CapturePolicy::Content => {
            let hash = so_tracing::statement_hash(statement);
            for span in [&parse_span, run_span] {
                span.record("spec.parse.error.kind", error_kind);
                span.record("spec.parse.expected_form", expected_form);
                span.record("spec.statement.hash", hash.as_str());
                span.record("spec.statement.text", statement);
            }
            tracing::warn!(
                "error.category" = "grammar",
                "error.stage" = "parse_statement",
                "error.kind" = error_kind,
                "error.message" = %error,
                "spec.parse.expected_form" = expected_form,
                "spec.statement.hash" = %hash,
                "spec.statement.text" = %statement,
                "spec.telemetry.capture" = policy.as_str(),
                "statement parse failed"
            );
        }
    }
}

fn parse_error_kind(error: &grammar::ParseError) -> &'static str {
    match error {
        grammar::ParseError::Empty => "empty",
        grammar::ParseError::MissingComma { .. } => "missing_comma",
        grammar::ParseError::EmptyCondition { .. } => "empty_condition",
        grammar::ParseError::MissingModal => "missing_modal",
        grammar::ParseError::EmptySubject => "empty_subject",
        grammar::ParseError::EmptyResponse => "empty_response",
    }
}

fn parse_expected_form(error: &grammar::ParseError) -> &'static str {
    match error {
        grammar::ParseError::Empty => "non_empty_statement",
        grammar::ParseError::MissingComma { .. } => "condition_clause_comma_before_guarantee",
        grammar::ParseError::EmptyCondition { .. } => "condition_clause_text",
        grammar::ParseError::MissingModal
        | grammar::ParseError::EmptySubject
        | grammar::ParseError::EmptyResponse => "guarantee_clause",
    }
}

fn locator_type(locator: &Locator) -> &'static str {
    match locator {
        Locator::File { .. } => "file",
        Locator::Url { .. } => "url",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::Kind;
    use crate::store::{FileBlobStore, InMemoryNodeStore};
    use so_lang::grammar::Assumption;
    use std::io::Write;
    use std::path::Path;

    /// A hermetic pair of stores for exercising ingest without a real backend.
    fn stores(tmp: &Path) -> (InMemoryNodeStore, FileBlobStore) {
        let blobs = FileBlobStore::open(&tmp.join("blobs")).unwrap();
        (InMemoryNodeStore::new(), blobs)
    }

    #[test]
    fn add_ubiquitous_with_file_evidence() {
        let tmp = tempfile::tempdir().unwrap();
        // An evidence file to snapshot.
        let ev_path = tmp.path().join("total.rs");
        let mut f = std::fs::File::create(&ev_path).unwrap();
        writeln!(f, "line1\nline2\nassert!(total > 0);\nline4").unwrap();

        let ev_value = format!(
            r#"{{"kind":"constitutive","locator":"{}:3"}}"#,
            ev_path.to_string_lossy()
        );
        let req = AddRequest {
            statement: "The sales amount shall be greater than zero.",
            evidence_values: &[ev_value],
            now: "2026-07-05T00:00:00Z",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let node = run(&req, &nodes, &blobs).unwrap();

        assert_eq!(node.assumption, Assumption::Top);
        assert_eq!(node.guarantee.subject, "sales amount");
        assert_eq!(node.meta.evidence.len(), 1);
        assert_eq!(node.meta.evidence[0].kind, Kind::Constitutive);
        // The captured content is present on the returned (in-memory) node …
        assert!(node.meta.evidence[0].snapshot.content.contains("total > 0"));
        assert_eq!(node.meta.created_at, "2026-07-05T00:00:00Z");
        assert_eq!(node.meta.cli_version, "test");

        // … the node is retrievable …
        let loaded = nodes.get_contract(&node.id).unwrap().unwrap();
        assert_eq!(loaded, node);
        // … and the snapshot bytes live in the blob store under their hash.
        let hash = &node.meta.evidence[0].snapshot.content_hash;
        let blob = blobs.get_blob(hash).unwrap().expect("blob must be present");
        assert!(String::from_utf8_lossy(&blob).contains("total > 0"));
    }

    #[test]
    fn add_without_evidence_is_allowed() {
        let tmp = tempfile::tempdir().unwrap();
        let req = AddRequest {
            statement: "When the order ships, the system shall notify the customer.",
            evidence_values: &[],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let node = run(&req, &nodes, &blobs).unwrap();
        assert!(node.meta.evidence.is_empty());
        assert!(matches!(node.assumption, Assumption::Conditions { .. }));
    }

    #[test]
    fn add_rejects_bad_grammar_before_capture() {
        let tmp = tempfile::tempdir().unwrap();
        let req = AddRequest {
            statement: "sales amount is positive",
            evidence_values: &["/no/such/file".to_string()],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        // Grammar failure must precede (and pre-empt) the missing-file snapshot.
        assert!(matches!(
            run(&req, &nodes, &blobs),
            Err(AddError::Grammar(_))
        ));
        // Nothing was persisted.
        assert!(nodes.is_empty());
    }

    #[test]
    fn add_bare_string_evidence_is_unknown() {
        let tmp = tempfile::tempdir().unwrap();
        let ev_path = tmp.path().join("note.txt");
        std::fs::write(&ev_path, "grounding note").unwrap();
        let req = AddRequest {
            statement: "The pump shall stop.",
            evidence_values: &[ev_path.to_string_lossy().to_string()],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let node = run(&req, &nodes, &blobs).unwrap();
        assert_eq!(node.meta.evidence[0].kind, Kind::Unknown);
    }
}
