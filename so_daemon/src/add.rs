//! The `spec add` use case: lossless ingest of a specification (one or more
//! sentences of the constrained specification language) and its evidence.
//!
//! This is the ELT "extract/load" boundary — it captures irreducible facts and
//! defers all classification. The pipeline:
//!   1. parse the whole specification (syntax); a syntax error aborts before
//!      any capture;
//!   2. normalize each (channel-resolved) `--evidence` value (evidence);
//!   3. snapshot each locator's content and hash it (snapshot, sense ②);
//!   4. finalize the source provenance (origin, sense ①);
//!   5. assemble and persist one node per sentence, each carrying the raw
//!      sentence text, the language version, and the *shared* captured
//!      evidence, plus its creation facts (sense ③).
//!
//! Evidence is captured once per request and cloned onto every node: the
//! grounding was given for the specification as a whole. Derived readings
//! (speech acts, contract views) are never computed here — they are response-
//! time views, not ingest facts.
//!
//! Persistence is all-or-nothing per request: a failure before step 5 persists
//! nothing, and if a later sentence's node fails to persist in step 5, the
//! nodes already persisted for this request are deleted again (best-effort
//! rollback) before the error is returned — so a failed `spec add` leaves no
//! partial specification behind and can simply be re-run. (Blobs are
//! content-addressed, so any left behind by a failure are harmless and are
//! reused on retry.)
//!
//! Runs entirely synchronously (filesystem, git, network, blocking DB driver).
//! The daemon calls it from `spawn_blocking`, off the async reactor.

use thiserror::Error;

use crate::domain::{Evidence, Locator, Meta, Node};

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
    /// The specification: one or more sentences of the constrained
    /// specification language.
    pub specification: &'a str,
    pub evidence_values: &'a [String],
    /// Node creation instant (RFC 3339, UTC) — sense ③.
    pub now: &'a str,
    pub cli: &'a str,
    pub cli_version: &'a str,
}

#[derive(Debug, Error)]
pub enum AddError {
    #[error("syntax error in specification: {0}")]
    Grammar(#[from] so_lang::parse::ParseError),
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
            AddError::Grammar(_) => "parse_specification",
            AddError::Evidence(_) => "parse_evidence",
            AddError::Snapshot(_) => "capture_evidence",
            AddError::Store(_) => "persist",
        }
    }

    pub(crate) fn diagnostic_kind(&self) -> &'static str {
        match self {
            AddError::Grammar(e) => e.kind(),
            AddError::Evidence(_) => "evidence_error",
            AddError::Snapshot(_) => "snapshot_error",
            AddError::Store(_) => "store_error",
        }
    }
}

/// Run `spec add`, returning the persisted nodes — one per sentence, in input
/// order.
///
/// The snapshot bytes are written to `blobs` (content-addressed); each node —
/// carrying only the hash pointer, not the bytes — is written to `nodes`.
pub fn run(
    req: &AddRequest,
    nodes: &dyn NodeStore,
    blobs: &dyn BlobStore,
) -> Result<Vec<Node>, AddError> {
    let policy = so_tracing::capture_policy();
    let run_span = tracing::info_span!(
        "spec.add.run",
        "spec.telemetry.capture" = policy.as_str(),
        "spec.specification.length" = req.specification.len() as u64,
        "spec.evidence.input_count" = req.evidence_values.len() as u64,
        "spec.evidence.normalized_count" = tracing::field::Empty,
        "spec.sentence.count" = tracing::field::Empty,
        "spec.specification.hash" = tracing::field::Empty,
        "spec.specification.text" = tracing::field::Empty,
        "spec.parse.success" = tracing::field::Empty,
        "spec.parse.error.kind" = tracing::field::Empty,
        "error.category" = tracing::field::Empty,
        "error.stage" = tracing::field::Empty,
        "node.id" = tracing::field::Empty,
        "node.count" = tracing::field::Empty,
    );
    let result = {
        let _run_entered = run_span.enter();
        run_pipeline(req, nodes, blobs, policy, &run_span)
    };
    // Attribute every failure on the run span, whatever the stage. (The
    // grammar path already recorded these via `record_parse_failure`;
    // re-recording the same values is harmless.)
    if let Err(e) = &result {
        run_span.record("error.category", e.category());
        run_span.record("error.stage", e.stage());
    }
    result
}

/// The pipeline body of [`run`], executed inside the `spec.add.run` span.
fn run_pipeline(
    req: &AddRequest,
    nodes: &dyn NodeStore,
    blobs: &dyn BlobStore,
    policy: so_tracing::CapturePolicy,
    run_span: &tracing::Span,
) -> Result<Vec<Node>, AddError> {
    record_specification_by_policy(policy, req.specification);

    // 1. Parse the whole specification. A syntax error aborts before any
    // capture; the parse tree is used only to split and slice the sentences.
    let specification = {
        let parse_span = tracing::debug_span!(
            "spec.add.parse_specification",
            "spec.telemetry.capture" = policy.as_str(),
            "spec.parse.success" = tracing::field::Empty,
            "spec.parse.error.kind" = tracing::field::Empty,
            "spec.specification.hash" = tracing::field::Empty,
            "spec.specification.text" = tracing::field::Empty,
            "error.category" = tracing::field::Empty,
            "error.stage" = tracing::field::Empty,
        );
        so_tracing::record_specification_on_span(&parse_span, policy, req.specification);
        let _span = parse_span.enter();
        match so_lang::parse::parse(req.specification) {
            Ok(specification) => {
                tracing::Span::current().record("spec.parse.success", true);
                run_span.record("spec.parse.success", true);
                specification
            }
            Err(e) => {
                record_parse_failure(policy, req.specification, &e, run_span);
                return Err(e.into());
            }
        }
    };
    run_span.record(
        "spec.sentence.count",
        specification.sentences.len() as u64,
    );

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

    // 3–4. Capture + enrich each evidence entry — once for the whole
    // specification; every sentence shares this grounding.
    let mut evidence = Vec::with_capacity(inputs.len());
    for (index, input) in inputs.into_iter().enumerate() {
        let evidence_span = tracing::info_span!(
            "spec.add.capture_evidence",
            "spec.evidence.index" = index as u64,
            "spec.evidence.kind" = ?input.kind,
            "spec.locator.type" = locator_type(&input.locator),
            "spec.snapshot.bytes" = tracing::field::Empty,
            "spec.snapshot.hash" = tracing::field::Empty,
            "error.category" = tracing::field::Empty,
            "error.stage" = tracing::field::Empty,
        );
        let _evidence_entered = evidence_span.enter();

        let capture = snapshot::capture(&input.locator, req.now)
            .map_err(|e| record_error_on_span(&evidence_span, e.into()))?;
        tracing::Span::current().record("spec.snapshot.bytes", capture.snapshot.bytes as u64);
        tracing::Span::current()
            .record("spec.snapshot.hash", capture.snapshot.content_hash.as_str());

        {
            let _span = tracing::debug_span!("spec.add.persist_blob").entered();
            blobs
                .put_blob(&capture.snapshot.content_hash, &capture.blob)
                .map_err(|e| record_error_on_span(&evidence_span, e.into()))?;
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

    // 5. Assemble and persist one node per sentence, sharing the evidence.
    // All-or-nothing: a failure rolls back the nodes already persisted for
    // this request (best-effort) so no partial specification is left behind.
    let mut persisted = Vec::with_capacity(specification.sentences.len());
    for sentence in &specification.sentences {
        let node = Node {
            id: new_id(),
            statement: sentence.source.clone(),
            lang_version: so_lang::LANG_VERSION.to_string(),
            meta: Meta {
                evidence: evidence.clone(),
                created_at: req.now.to_string(),
                cli: req.cli.to_string(),
                cli_version: req.cli_version.to_string(),
            },
        };
        let stored = {
            let _span = tracing::debug_span!("spec.add.persist_node").entered();
            nodes.add_node(&node)
        };
        if let Err(e) = stored {
            roll_back_persisted(nodes, &persisted);
            return Err(e.into());
        }
        tracing::debug!("node.id" = %node.id, "specification node persisted");
        persisted.push(node);
    }
    if let Some(first) = persisted.first() {
        run_span.record("node.id", first.id.as_str());
    }
    run_span.record("node.count", persisted.len() as u64);
    tracing::info!(
        "node.count" = persisted.len() as u64,
        "specification ingest persisted all nodes"
    );
    Ok(persisted)
}

fn new_id() -> String {
    uuid::Uuid::new_v4().to_string()
}

/// Record a failure's category/stage on `span`, then hand the error back —
/// shaped for use inside `map_err` just before `?` propagates it.
fn record_error_on_span(span: &tracing::Span, e: AddError) -> AddError {
    span.record("error.category", e.category());
    span.record("error.stage", e.stage());
    e
}

/// Best-effort rollback of the nodes persisted before a later sentence of the
/// same specification failed to persist. A node whose delete itself fails is
/// reported by id so an operator can remove it manually.
fn roll_back_persisted(nodes: &dyn NodeStore, persisted: &[Node]) {
    let _span = tracing::info_span!(
        "spec.add.rollback",
        "node.count" = persisted.len() as u64,
    )
    .entered();
    for node in persisted {
        if let Err(e) = nodes.delete_node(&node.id) {
            tracing::warn!(
                "node.id" = %node.id,
                "error.message" = %e,
                "ingest rollback could not delete an already-persisted node; remove it manually"
            );
        }
    }
}

fn record_specification_by_policy(policy: so_tracing::CapturePolicy, specification: &str) {
    if policy.allows_diagnostic() {
        let hash = so_tracing::specification_hash(specification);
        tracing::Span::current().record("spec.specification.hash", hash.as_str());
    }
    if policy.allows_content() {
        tracing::Span::current().record("spec.specification.text", specification);
    }
}

fn record_parse_failure(
    policy: so_tracing::CapturePolicy,
    specification: &str,
    error: &so_lang::parse::ParseError,
    run_span: &tracing::Span,
) {
    let error_kind = error.kind();

    let parse_span = tracing::Span::current();
    for span in [&parse_span, run_span] {
        span.record("spec.parse.success", false);
        span.record("error.category", "grammar");
        span.record("error.stage", "parse_specification");
    }

    match policy {
        so_tracing::CapturePolicy::Ops => {
            tracing::warn!(
                "error.category" = "grammar",
                "error.stage" = "parse_specification",
                "spec.telemetry.capture" = policy.as_str(),
                "specification parse failed"
            );
        }
        so_tracing::CapturePolicy::Diagnostic => {
            let hash = so_tracing::specification_hash(specification);
            for span in [&parse_span, run_span] {
                span.record("spec.parse.error.kind", error_kind);
                span.record("spec.specification.hash", hash.as_str());
            }
            tracing::warn!(
                "error.category" = "grammar",
                "error.stage" = "parse_specification",
                "error.kind" = error_kind,
                "spec.specification.hash" = %hash,
                "spec.telemetry.capture" = policy.as_str(),
                "specification parse failed"
            );
        }
        so_tracing::CapturePolicy::Content => {
            let hash = so_tracing::specification_hash(specification);
            for span in [&parse_span, run_span] {
                span.record("spec.parse.error.kind", error_kind);
                span.record("spec.specification.hash", hash.as_str());
                span.record("spec.specification.text", specification);
            }
            tracing::warn!(
                "error.category" = "grammar",
                "error.stage" = "parse_specification",
                "error.kind" = error_kind,
                "error.message" = %error,
                "spec.specification.hash" = %hash,
                "spec.specification.text" = %specification,
                "spec.telemetry.capture" = policy.as_str(),
                "specification parse failed"
            );
        }
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
    use std::io::Write;
    use std::path::Path;

    /// A hermetic pair of stores for exercising ingest without a real backend.
    fn stores(tmp: &Path) -> (InMemoryNodeStore, FileBlobStore) {
        let blobs = FileBlobStore::open(&tmp.join("blobs")).unwrap();
        (InMemoryNodeStore::new(), blobs)
    }

    #[test]
    fn add_single_sentence_with_file_evidence() {
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
            specification: "The sales amount shall be greater than zero.",
            evidence_values: &[ev_value],
            now: "2026-07-05T00:00:00Z",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let persisted = run(&req, &nodes, &blobs).unwrap();
        assert_eq!(persisted.len(), 1);
        let node = &persisted[0];

        // The raw sentence text is the stored truth, with the language version.
        assert_eq!(node.statement, "The sales amount shall be greater than zero.");
        assert_eq!(node.lang_version, so_lang::LANG_VERSION);
        assert_eq!(node.meta.evidence.len(), 1);
        assert_eq!(node.meta.evidence[0].kind, Kind::Constitutive);
        // The captured content is present on the returned (in-memory) node …
        assert!(node.meta.evidence[0].snapshot.content.contains("total > 0"));
        assert_eq!(node.meta.created_at, "2026-07-05T00:00:00Z");
        assert_eq!(node.meta.cli_version, "test");

        // … the node is retrievable …
        let loaded = nodes.get_node(&node.id).unwrap().unwrap();
        assert_eq!(&loaded, node);
        // … and the snapshot bytes live in the blob store under their hash.
        let hash = &node.meta.evidence[0].snapshot.content_hash;
        let blob = blobs.get_blob(hash).unwrap().expect("blob must be present");
        assert!(String::from_utf8_lossy(&blob).contains("total > 0"));
    }

    #[test]
    fn add_multi_sentence_yields_one_node_per_sentence_sharing_evidence() {
        let tmp = tempfile::tempdir().unwrap();
        let ev_path = tmp.path().join("note.txt");
        std::fs::write(&ev_path, "shared grounding").unwrap();

        let req = AddRequest {
            specification: "A session means a sequence of requests. \
                            When a session expires, the system shall close the session.",
            evidence_values: &[ev_path.to_string_lossy().to_string()],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let persisted = run(&req, &nodes, &blobs).unwrap();

        assert_eq!(persisted.len(), 2);
        // One node per sentence, in input order, holding the raw slice.
        assert_eq!(persisted[0].statement, "A session means a sequence of requests.");
        assert_eq!(
            persisted[1].statement,
            "When a session expires, the system shall close the session."
        );
        // Fresh distinct ids; identical shared evidence.
        assert_ne!(persisted[0].id, persisted[1].id);
        assert_eq!(persisted[0].meta.evidence, persisted[1].meta.evidence);
        assert_eq!(persisted[0].meta.evidence.len(), 1);
        // Both were persisted.
        assert_eq!(nodes.len(), 2);
    }

    #[test]
    fn add_without_evidence_is_allowed() {
        let tmp = tempfile::tempdir().unwrap();
        let req = AddRequest {
            specification: "When the order ships, the system shall notify the customer.",
            evidence_values: &[],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let persisted = run(&req, &nodes, &blobs).unwrap();
        assert_eq!(persisted.len(), 1);
        assert!(persisted[0].meta.evidence.is_empty());
    }

    #[test]
    fn add_rejects_bad_grammar_before_capture() {
        let tmp = tempfile::tempdir().unwrap();
        let req = AddRequest {
            // No pivot word — a precise syntax error.
            specification: "The pump quickly.",
            evidence_values: &["/no/such/file".to_string()],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        // Grammar failure must precede (and pre-empt) the missing-file snapshot.
        assert!(matches!(
            run(&req, &nodes, &blobs),
            Err(AddError::Grammar(so_lang::parse::ParseError::MissingPivot))
        ));
        // Nothing was persisted.
        assert!(nodes.is_empty());
    }

    /// A store that fails after a fixed number of successful adds, for
    /// exercising the all-or-nothing persist contract.
    struct FailingNodeStore {
        inner: InMemoryNodeStore,
        fail_after: usize,
        adds: std::cell::Cell<usize>,
    }

    impl crate::store::NodeStore for FailingNodeStore {
        fn add_node(&self, node: &Node) -> Result<(), crate::store::StoreError> {
            self.adds.set(self.adds.get() + 1);
            if self.adds.get() > self.fail_after {
                return Err(crate::store::StoreError::Backend(
                    "simulated backend outage".to_string(),
                ));
            }
            self.inner.add_node(node)
        }

        fn get_node(&self, id: &str) -> Result<Option<Node>, crate::store::StoreError> {
            self.inner.get_node(id)
        }

        fn delete_node(&self, id: &str) -> Result<(), crate::store::StoreError> {
            self.inner.delete_node(id)
        }
    }

    #[test]
    fn store_failure_mid_specification_rolls_back_earlier_nodes() {
        let tmp = tempfile::tempdir().unwrap();
        let req = AddRequest {
            specification: "A session means a sequence of requests. \
                            When a session expires, the system shall close the session.",
            evidence_values: &[],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (_, blobs) = stores(tmp.path());
        // First sentence persists, second fails: the first must be rolled back.
        let nodes = FailingNodeStore {
            inner: InMemoryNodeStore::new(),
            fail_after: 1,
            adds: std::cell::Cell::new(0),
        };
        assert!(matches!(
            run(&req, &nodes, &blobs),
            Err(AddError::Store(_))
        ));
        // All-or-nothing: no partial specification is left behind.
        assert!(nodes.inner.is_empty());
    }

    #[test]
    fn add_bare_string_evidence_is_unknown() {
        let tmp = tempfile::tempdir().unwrap();
        let ev_path = tmp.path().join("note.txt");
        std::fs::write(&ev_path, "grounding note").unwrap();
        let req = AddRequest {
            specification: "The pump shall stop.",
            evidence_values: &[ev_path.to_string_lossy().to_string()],
            now: "t",
            cli: "spec",
            cli_version: "test",
        };
        let (nodes, blobs) = stores(tmp.path());
        let persisted = run(&req, &nodes, &blobs).unwrap();
        assert_eq!(persisted[0].meta.evidence[0].kind, Kind::Unknown);
    }
}
