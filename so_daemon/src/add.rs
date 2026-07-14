//! The synchronous `spec add` boundary.
//!
//! An Add performs exactly two domain operations: parse exactly one constrained
//! natural-language sentence, then persist exactly one Specification Node. Raw
//! Evidence descriptors are copied into the Node as retryable Job input; they
//! are not interpreted, resolved, captured, or enriched here. Every derived or
//! I/O-bearing operation starts from the subsequent `NodeAdded` event.

use thiserror::Error;

use crate::domain::{Meta, Node};
use crate::store::NodeStore;

pub struct AddRequest<'a> {
    /// Identity assigned once when the command enters the Add Mailbox.
    pub message_id: &'a str,
    pub specification: &'a str,
    /// Channel-resolved but otherwise opaque Evidence descriptors.
    pub evidence_values: &'a [String],
    pub now: &'a str,
    pub cli: &'a str,
    pub cli_version: &'a str,
}

pub struct AddOutcome {
    pub node: Node,
    pub inserted: bool,
}

#[derive(Debug, Error)]
pub enum AddError {
    #[error("syntax error in specification: {0}")]
    Grammar(#[from] so_lang::parse::ParseError),
    #[error("spec add accepts exactly one sentence, but {found} sentences were provided")]
    SentenceCount { found: usize },
    #[error("store error: {0}")]
    Store(#[from] crate::store::StoreError),
}

impl AddError {
    pub(crate) fn category(&self) -> &'static str {
        match self {
            AddError::Grammar(_) | AddError::SentenceCount { .. } => "grammar",
            AddError::Store(_) => "store",
        }
    }

    pub(crate) fn stage(&self) -> &'static str {
        match self {
            AddError::Grammar(_) => "parse_specification",
            AddError::SentenceCount { .. } => "validate_sentence_count",
            AddError::Store(_) => "persist_node",
        }
    }

    pub(crate) fn diagnostic_kind(&self) -> &'static str {
        match self {
            AddError::Grammar(error) => error.kind(),
            AddError::SentenceCount { .. } => "sentence_count",
            AddError::Store(_) => "store_error",
        }
    }
}

pub fn run(req: &AddRequest<'_>, nodes: &dyn NodeStore) -> Result<Node, AddError> {
    Ok(run_with_status(req, nodes)?.node)
}

pub fn run_with_status(
    req: &AddRequest<'_>,
    nodes: &dyn NodeStore,
) -> Result<AddOutcome, AddError> {
    let policy = so_tracing::capture_policy();
    let span = tracing::info_span!(
        "spec.add.run",
        "spec.telemetry.capture" = policy.as_str(),
        "spec.specification.length" = req.specification.len() as u64,
        "spec.evidence.request_count" = req.evidence_values.len() as u64,
        "spec.parse.success" = tracing::field::Empty,
        "spec.sentence.count" = tracing::field::Empty,
        "node.id" = tracing::field::Empty,
        "error.category" = tracing::field::Empty,
        "error.stage" = tracing::field::Empty,
    );
    so_tracing::record_specification_on_span(&span, policy, req.specification);
    let _entered = span.enter();

    let parsed = so_lang::parse::parse(req.specification).map_err(|error| {
        tracing::Span::current().record("spec.parse.success", false);
        tracing::Span::current().record("error.category", "grammar");
        tracing::Span::current().record("error.stage", "parse_specification");
        AddError::Grammar(error)
    })?;
    tracing::Span::current().record("spec.parse.success", true);
    tracing::Span::current().record("spec.sentence.count", parsed.sentences.len() as u64);

    let [sentence] = parsed.sentences.as_slice() else {
        let error = AddError::SentenceCount {
            found: parsed.sentences.len(),
        };
        tracing::Span::current().record("error.category", error.category());
        tracing::Span::current().record("error.stage", error.stage());
        return Err(error);
    };

    if let Some(existing) = nodes.find_node(&sentence.source, so_lang::LANG_VERSION)? {
        let has_new_evidence = req
            .evidence_values
            .iter()
            .any(|request| !existing.meta.evidence_requests.contains(request));
        let node = if has_new_evidence {
            nodes.merge_evidence_requests(&existing.id, req.evidence_values)?
        } else {
            existing
        };
        tracing::Span::current().record("node.id", node.id.as_str());
        tracing::info!("node.id" = %node.id, inserted = false, "existing specification node reused");
        return Ok(AddOutcome {
            node,
            inserted: false,
        });
    }

    let node = Node {
        // Specification identity is its accepted source sentence under the
        // language version. Mailbox identity still scopes Events and Jobs, but
        // submitting the same Node content again must reuse the stored Node.
        id: crate::mailbox::derive_id("node", &[so_lang::LANG_VERSION, &sentence.source]),
        statement: sentence.source.clone(),
        lang_version: so_lang::LANG_VERSION.to_string(),
        meta: Meta {
            evidence_requests: req.evidence_values.to_vec(),
            evidence_request_generation: String::new(),
            evidence: Vec::new(),
            created_at: req.now.to_string(),
            cli: req.cli.to_string(),
            cli_version: req.cli_version.to_string(),
            updates: Default::default(),
        },
    };
    let inserted = nodes.add_node(&node).map_err(|error| {
        tracing::Span::current().record("error.category", "store");
        tracing::Span::current().record("error.stage", "persist_node");
        AddError::Store(error)
    })?;
    let node = if inserted {
        node
    } else {
        nodes
            .get_node(&node.id)?
            .ok_or_else(|| crate::store::StoreError::MissingNode(node.id.clone()))?
    };
    tracing::Span::current().record("node.id", node.id.as_str());
    tracing::info!("node.id" = %node.id, inserted, "specification node accepted");
    Ok(AddOutcome { node, inserted })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::{GraphStore, InMemoryNodeStore, NodeStore};

    fn request<'a>(specification: &'a str, evidence: &'a [String]) -> AddRequest<'a> {
        AddRequest {
            message_id: "message-1",
            specification,
            evidence_values: evidence,
            now: "2026-07-12T00:00:00Z",
            cli: "spec",
            cli_version: "test",
        }
    }

    #[test]
    fn add_persists_one_node_without_touching_evidence_locator() {
        let store = InMemoryNodeStore::new();
        let values = vec!["this/file/does/not/exist.rs:999".to_string()];
        let node = run(&request("The pump shall stop.", &values), &store).unwrap();

        assert_eq!(node.statement, "The pump shall stop.");
        assert_eq!(node.meta.evidence_requests, values);
        assert!(node.meta.evidence.is_empty());
        assert_eq!(store.get_node(&node.id).unwrap(), Some(node));
    }

    #[test]
    fn multiple_sentences_are_rejected_without_persisting_a_node() {
        let store = InMemoryNodeStore::new();
        let error = run(
            &request(
                "The pump shall stop. The controller shall log the event.",
                &[],
            ),
            &store,
        )
        .unwrap_err();
        assert!(matches!(error, AddError::SentenceCount { found: 2 }));
        assert_eq!(store.count_nodes().unwrap(), 0);
    }

    #[test]
    fn syntax_errors_are_rejected_before_persistence() {
        let store = InMemoryNodeStore::new();
        assert!(matches!(
            run(&request("The pump quickly.", &[]), &store),
            Err(AddError::Grammar(_))
        ));
        assert_eq!(store.count_nodes().unwrap(), 0);
    }

    #[test]
    fn identical_specifications_reuse_one_stable_immutable_node() {
        let store = InMemoryNodeStore::new();
        let first = run(&request("The pump shall stop.", &[]), &store).unwrap();
        let second = run(&request("The pump shall stop.", &[]), &store).unwrap();
        assert_eq!(first.id, second.id);
        assert_eq!(store.count_nodes().unwrap(), 1);

        let other = AddRequest {
            message_id: "message-2",
            ..request("The pump shall stop.", &[])
        };
        let third = run(&other, &store).unwrap();
        assert_eq!(first.id, third.id);
        assert_eq!(first, third);
        assert_eq!(store.count_nodes().unwrap(), 1);

        let different = run(&request("The pump shall start.", &[]), &store).unwrap();
        assert_ne!(first.id, different.id);
        assert_eq!(store.count_nodes().unwrap(), 2);
    }

    #[test]
    fn identical_legacy_node_is_reused_even_when_its_id_is_not_content_addressed() {
        let store = InMemoryNodeStore::new();
        let legacy = Node {
            id: "legacy-random-id".into(),
            statement: "The pump shall stop.".into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: vec![],
                evidence_request_generation: String::new(),
                evidence: vec![],
                created_at: "old".into(),
                cli: "spec".into(),
                cli_version: "old".into(),
                updates: Default::default(),
            },
        };
        store.add_node(&legacy).unwrap();
        let reused = run(&request("The pump shall stop.", &[]), &store).unwrap();
        assert_eq!(reused, legacy);
        assert_eq!(store.count_nodes().unwrap(), 1);
    }

    #[test]
    fn new_evidence_is_merged_into_the_reused_specification_node() {
        let store = InMemoryNodeStore::new();
        let first_values = ["first.rs:1".to_string()];
        let first = run(&request("The pump shall stop.", &first_values), &store).unwrap();
        let second_values = ["second.rs:2".to_string(), "first.rs:1".to_string()];
        let reused = run(&request("The pump shall stop.", &second_values), &store).unwrap();
        assert_eq!(first.id, reused.id);
        assert_eq!(store.count_nodes().unwrap(), 1);
        assert_eq!(reused.meta.evidence_requests, ["first.rs:1", "second.rs:2"]);
    }
}
