//! Manual Evidence judgments and the Evidence property-graph projection.
//!
//! This is deliberately narrower than a generic manual Edge API. Operators may
//! capture or reuse Evidence and assert only that it affirms or denies an
//! existing Specification or Evidence value.

use std::collections::{BTreeMap, BTreeSet};

use crate::domain::{Derivation, DerivedNode, Edge, EdgeKind, Evidence, Node, VertexKind};
use crate::evidence;
use crate::graph_query::{
    GraphQuery, GraphSchema, PropertyGraph, PropertyValue, QueryEdge, QueryNode,
};
use crate::store::{BlobStore, EvidenceGraphPage, GraphStore, StoreError};
use crate::{origin, snapshot};
use thiserror::Error;

pub const MANUAL_EVIDENCE_METHOD: &str = "manual-evidence";
pub const MANUAL_EVIDENCE_VERSION: &str = "manual-evidence/v1";

pub fn derivation() -> Derivation {
    Derivation {
        method: MANUAL_EVIDENCE_METHOD.into(),
        version: MANUAL_EVIDENCE_VERSION.into(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Relation {
    Affirms,
    Denies,
}

impl Relation {
    pub fn edge_kind(self) -> EdgeKind {
        match self {
            Self::Affirms => EdgeKind::EvidenceAffirms,
            Self::Denies => EdgeKind::EvidenceDenies,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AddEvidenceRelationResult {
    pub evidence_node: DerivedNode,
    pub edge: Edge,
    pub evidence_node_inserted: bool,
    pub edge_inserted: bool,
}

#[derive(Debug, Error)]
pub enum EvidenceRelationError {
    #[error("Evidence source must not be empty")]
    EmptyEvidence,
    #[error("Evidence target must not be empty")]
    EmptyTarget,
    #[error("invalid Evidence descriptor: {0}")]
    Descriptor(#[from] evidence::EvidenceError),
    #[error("spec evidence add accepts exactly one Evidence descriptor")]
    MultipleDescriptors,
    #[error("Evidence Node '{0}' does not exist")]
    MissingEvidence(String),
    #[error("target '{0}' does not exist")]
    MissingTarget(String),
    #[error("target '{0}' is not a Specification or Evidence Node")]
    InvalidTarget(String),
    #[error("failed to capture Evidence: {0}")]
    Capture(#[from] snapshot::SnapshotError),
    #[error(transparent)]
    Store(#[from] StoreError),
    #[error("invalid Evidence Edge: {0}")]
    InvalidEdge(String),
}

/// Capture or reuse one Evidence value and append its manual judgment.
pub fn add_relation(
    graph: &(dyn GraphStore + Send + Sync),
    blobs: &(dyn BlobStore + Send + Sync),
    source: &str,
    target: &str,
    relation: Relation,
    now: &str,
) -> Result<AddEvidenceRelationResult, EvidenceRelationError> {
    let source = source.trim();
    let target = target.trim();
    if source.is_empty() {
        return Err(EvidenceRelationError::EmptyEvidence);
    }
    if target.is_empty() {
        return Err(EvidenceRelationError::EmptyTarget);
    }

    let target_kind = if graph.get_node(target)?.is_some() {
        VertexKind::Specification
    } else {
        match graph.get_derived_nodes(&[target.to_string()])?.as_slice() {
            [DerivedNode::Evidence { .. }] => VertexKind::Evidence,
            [] => return Err(EvidenceRelationError::MissingTarget(target.into())),
            _ => return Err(EvidenceRelationError::InvalidTarget(target.into())),
        }
    };

    let (evidence_node, evidence_node_inserted) = if source.starts_with("evidence-") {
        let nodes = graph.get_derived_nodes(&[source.to_string()])?;
        let node = nodes
            .into_iter()
            .next()
            .filter(|node| matches!(node, DerivedNode::Evidence { .. }))
            .ok_or_else(|| EvidenceRelationError::MissingEvidence(source.into()))?;
        (node, false)
    } else {
        let mut inputs = evidence::parse_value(source)?;
        if inputs.len() != 1 {
            return Err(EvidenceRelationError::MultipleDescriptors);
        }
        let input = inputs.pop().expect("one descriptor checked above");
        let capture = snapshot::capture(&input.locator, now)?;
        blobs.put_blob(&capture.snapshot.content_hash, &capture.blob)?;
        let final_origin = origin::finalize(
            &input.locator,
            &input.origin,
            &capture.origin_hints,
            &origin::registered_enrichers(),
        );
        let evidence_node = DerivedNode::evidence(Evidence {
            kind: input.kind,
            locator: input.locator,
            snapshot: capture.snapshot,
            origin: final_origin,
        });
        let inserted = graph.put_derived_node_value(&evidence_node)?;
        (evidence_node, inserted)
    };

    let edge = Edge::evidence_relation(
        relation.edge_kind(),
        evidence_node.id(),
        target,
        target_kind,
        derivation(),
        now,
    )
    .map_err(EvidenceRelationError::InvalidEdge)?;
    let edge_inserted = graph.append_edge(&edge)?;
    Ok(AddEvidenceRelationResult {
        evidence_node,
        edge,
        evidence_node_inserted,
        edge_inserted,
    })
}

pub fn query_schema() -> GraphSchema {
    GraphSchema::new(
        ["Evidence", "Specification"],
        ["GROUNDED_BY", "EVIDENCE_AFFIRMS", "EVIDENCE_DENIES"],
        [
            "id",
            "kind",
            "locator",
            "hash",
            "bytes",
            "captured_at",
            "author",
            "statement",
            "lang_version",
            "created_at",
            "recorded_at",
            "source",
            "target",
        ],
    )
}

pub fn query_page(
    query: &GraphQuery,
    evidence_nodes: &[DerivedNode],
    specification_nodes: &[Node],
    edges: &[Edge],
    after: Option<&str>,
    limit: usize,
) -> EvidenceGraphPage {
    let property_graph = to_property_graph(evidence_nodes, specification_nodes, edges);
    let selection = query.execute(&property_graph, after, limit);
    let selected_evidence: BTreeSet<&str> = selection
        .node_ids
        .iter()
        .filter_map(|id| {
            property_graph
                .nodes
                .get(id)
                .filter(|node| node.labels.contains("Evidence"))
                .map(|_| id.as_str())
        })
        .collect();
    let selected_specifications: BTreeSet<&str> = selection
        .node_ids
        .iter()
        .filter_map(|id| {
            property_graph
                .nodes
                .get(id)
                .filter(|node| node.labels.contains("Specification"))
                .map(|_| id.as_str())
        })
        .collect();
    EvidenceGraphPage {
        evidence_nodes: evidence_nodes
            .iter()
            .filter(|node| selected_evidence.contains(node.id()))
            .cloned()
            .collect(),
        edges: edges
            .iter()
            .filter(|edge| selection.edge_ids.contains(&edge.id))
            .cloned()
            .collect(),
        specification_nodes: specification_nodes
            .iter()
            .filter(|node| selected_specifications.contains(node.id.as_str()))
            .cloned()
            .collect(),
        selected_evidence_ids: selected_evidence.into_iter().map(str::to_string).collect(),
        paths: selection.paths,
        next_cursor: selection.next_cursor,
    }
}

fn to_property_graph(
    evidence_nodes: &[DerivedNode],
    specification_nodes: &[Node],
    edges: &[Edge],
) -> PropertyGraph {
    let mut graph = PropertyGraph::default();
    for node in evidence_nodes {
        let DerivedNode::Evidence { id, evidence } = node else {
            continue;
        };
        let mut properties = BTreeMap::from([
            ("id".into(), PropertyValue::String(id.clone())),
            (
                "kind".into(),
                PropertyValue::String(evidence.kind.as_str().into()),
            ),
            (
                "locator".into(),
                PropertyValue::String(evidence.locator.render()),
            ),
            (
                "hash".into(),
                PropertyValue::String(evidence.snapshot.content_hash.clone()),
            ),
            (
                "bytes".into(),
                PropertyValue::Integer(evidence.snapshot.bytes as i64),
            ),
            (
                "captured_at".into(),
                PropertyValue::String(evidence.snapshot.captured_at.clone()),
            ),
        ]);
        if let Some(author) = &evidence.origin.author {
            properties.insert("author".into(), PropertyValue::String(author.clone()));
        }
        graph.nodes.insert(
            id.clone(),
            QueryNode {
                id: id.clone(),
                labels: BTreeSet::from(["Evidence".into()]),
                properties,
            },
        );
    }
    for node in specification_nodes {
        graph.nodes.insert(
            node.id.clone(),
            QueryNode {
                id: node.id.clone(),
                labels: BTreeSet::from(["Specification".into()]),
                properties: BTreeMap::from([
                    ("id".into(), PropertyValue::String(node.id.clone())),
                    (
                        "statement".into(),
                        PropertyValue::String(node.statement.clone()),
                    ),
                    (
                        "lang_version".into(),
                        PropertyValue::String(node.lang_version.clone()),
                    ),
                    (
                        "created_at".into(),
                        PropertyValue::String(node.meta.created_at.clone()),
                    ),
                ]),
            },
        );
    }
    for edge in edges {
        let Some(relation_type) = relation_type(edge.kind) else {
            continue;
        };
        graph.edges.insert(
            edge.id.clone(),
            QueryEdge {
                id: edge.id.clone(),
                relation_type: relation_type.into(),
                source: edge.source.clone(),
                target: edge.target.clone(),
                properties: BTreeMap::from([
                    ("id".into(), PropertyValue::String(edge.id.clone())),
                    (
                        "kind".into(),
                        PropertyValue::String(edge.kind.as_str().into()),
                    ),
                    (
                        "recorded_at".into(),
                        PropertyValue::String(edge.recorded_at.clone()),
                    ),
                    ("source".into(), PropertyValue::String(edge.source.clone())),
                    ("target".into(), PropertyValue::String(edge.target.clone())),
                ]),
            },
        );
    }
    graph
}

fn relation_type(kind: EdgeKind) -> Option<&'static str> {
    match kind {
        EdgeKind::GroundedBy => Some("GROUNDED_BY"),
        EdgeKind::EvidenceAffirms => Some("EVIDENCE_AFFIRMS"),
        EdgeKind::EvidenceDenies => Some("EVIDENCE_DENIES"),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, Node};
    use crate::graph_query::GraphQuery;
    use crate::store::{FileBlobStore, InMemoryNodeStore, NodeStore};

    #[test]
    fn manual_capture_can_deny_an_existing_evidence_node_and_be_queried() {
        let graph = InMemoryNodeStore::new();
        graph
            .add_node(&Node {
                id: "spec-target".into(),
                statement: "The service shall use the current query language.".into(),
                lang_version: so_lang::LANG_VERSION.into(),
                meta: Meta {
                    evidence_requests: Vec::new(),
                    evidence_request_generation: String::new(),
                    evidence: Vec::new(),
                    created_at: "2026-01-01T00:00:00Z".into(),
                    cli: "test".into(),
                    cli_version: "test".into(),
                    updates: Default::default(),
                },
            })
            .unwrap();
        let temp = tempfile::tempdir().unwrap();
        let blobs = FileBlobStore::open(temp.path()).unwrap();
        let old = temp.path().join("old.md");
        let correction = temp.path().join("correction.md");
        std::fs::write(&old, "the former behavior").unwrap();
        std::fs::write(&correction, "the former behavior is obsolete").unwrap();

        let affirmed = add_relation(
            &graph,
            &blobs,
            old.to_string_lossy().as_ref(),
            "spec-target",
            Relation::Affirms,
            "2026-01-01T00:00:00Z",
        )
        .unwrap();
        let denied = add_relation(
            &graph,
            &blobs,
            correction.to_string_lossy().as_ref(),
            affirmed.evidence_node.id(),
            Relation::Denies,
            "2026-01-02T00:00:00Z",
        )
        .unwrap();

        assert_eq!(denied.edge.kind, EdgeKind::EvidenceDenies);
        assert_eq!(denied.edge.target_kind, VertexKind::Evidence);
        let query = GraphQuery::parse(&format!(
            "MATCH p=(new:Evidence)-[:EVIDENCE_DENIES]->(old:Evidence) \
             WHERE old.id = '{}' RETURN p",
            affirmed.evidence_node.id()
        ))
        .unwrap();
        query.validate(&query_schema()).unwrap();
        let page = graph.query_evidence_graph(&query, None, 10).unwrap();
        assert_eq!(
            page.selected_evidence_ids,
            vec![denied.evidence_node.id().to_string()]
                .into_iter()
                .chain([affirmed.evidence_node.id().to_string()])
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        );
        assert!(page.edges.iter().any(|edge| edge.id == denied.edge.id));
        assert_eq!(page.paths.len(), 1);
    }
}
