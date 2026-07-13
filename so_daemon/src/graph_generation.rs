//! Incremental structure derived from one newly stored specification.
//!
//! Written term forms become shared connector vertices. Their mention edges
//! are exact lexical facts and candidate indexes, not claims of referent
//! identity. No semantic specification-to-specification edge is generated
//! until a graph-side establishment method is defined.

use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use crate::domain::{Derivation, Edge, EdgeKind, Node, TermNode, TextAnchor, VertexKind};
use crate::jobs::{JobOutput, NodeMetaPlugin, PluginContext, PluginRegistration};
use crate::store::{GraphStore, StoreError};

pub const GENERATION_VERSION: &str = "spec-graph/term-form-v2";
const PLUGIN_NAME: &str = "graph-generation";

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GenerationReport {
    pub terms_seen: usize,
    pub terms_inserted: usize,
    pub mention_edges_inserted: usize,
}

#[derive(Debug, Clone)]
struct TermOccurrence {
    term: TermNode,
    anchor: TextAnchor,
}

pub fn generation_version() -> &'static str {
    GENERATION_VERSION
}

pub fn needs_generation(node: &Node) -> bool {
    !node.meta.updates.values().any(|update| {
        update.source == PLUGIN_NAME
            && update.value.get("version").and_then(Value::as_str) == Some(GENERATION_VERSION)
    })
}

pub fn generate_and_persist(
    added: &Node,
    store: &(dyn GraphStore + Send + Sync),
    recorded_at: &str,
) -> Result<GenerationReport, StoreError> {
    let Some(sentence) = parse_current(added) else {
        return Ok(GenerationReport::default());
    };
    let occurrences = term_occurrences(added, &sentence);
    let mut report = GenerationReport {
        terms_seen: occurrences.len(),
        ..GenerationReport::default()
    };
    for occurrence in occurrences {
        let edge = mention_edge(added, &occurrence, recorded_at);
        let write = store.put_term_mention(&occurrence.term, &edge)?;
        report.terms_inserted += usize::from(write.term_inserted);
        report.mention_edges_inserted += usize::from(write.edge_inserted);
    }

    // The shared term nodes are the candidate index. No semantic
    // specification-to-specification Edge is created here. `so-lang` only
    // parses; this daemon-owned projection derives the candidate index, and it
    // is not a proof authority for semantic graph topology.
    Ok(report)
}

fn parse_current(node: &Node) -> Option<so_lang::ast::Sentence> {
    if node.lang_version != so_lang::LANG_VERSION {
        return None;
    }
    so_lang::parse::parse(&node.statement)
        .ok()
        .and_then(|specification| specification.sentences.into_iter().next())
}

fn term_occurrences(node: &Node, sentence: &so_lang::ast::Sentence) -> Vec<TermOccurrence> {
    let value = serde_json::to_value(sentence).expect("sentence AST serializes");
    let mut found = Vec::new();
    walk_terms(node, &value, "", &mut found);
    found.sort_by(|a, b| {
        a.term
            .id
            .cmp(&b.term.id)
            .then_with(|| a.anchor.selector.cmp(&b.anchor.selector))
    });
    found.dedup_by(|a, b| a.term.id == b.term.id && a.anchor.selector == b.anchor.selector);
    found
}

fn walk_terms(node: &Node, value: &Value, path: &str, found: &mut Vec<TermOccurrence>) {
    match value {
        Value::Object(map) => {
            if map.contains_key("head") && map.contains_key("modifiers") {
                if let Ok(np) = serde_json::from_value::<so_lang::ast::Np>(value.clone()) {
                    let mut without_det = np.clone();
                    without_det.det = None;
                    let form = without_det.render().to_lowercase();
                    let head = np.head.to_lowercase();
                    let term = TermNode {
                        id: stable_id("term", &[&node.lang_version, GENERATION_VERSION, &form]),
                        form,
                        head,
                        lang_version: node.lang_version.clone(),
                        derivation_version: GENERATION_VERSION.to_string(),
                    };
                    found.push(TermOccurrence {
                        term,
                        anchor: TextAnchor {
                            selector: if path.is_empty() {
                                "/".to_string()
                            } else {
                                path.to_string()
                            },
                            text: np.render(),
                            role: grammatical_role(path).to_string(),
                        },
                    });
                }
            }
            for (key, child) in map {
                let escaped = key.replace('~', "~0").replace('/', "~1");
                let next = format!("{path}/{escaped}");
                walk_terms(node, child, &next, found);
            }
        }
        Value::Array(items) => {
            for (index, child) in items.iter().enumerate() {
                walk_terms(node, child, &format!("{path}/{index}"), found);
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
    }
}

fn grammatical_role(path: &str) -> &'static str {
    if path.ends_with("/core/term") {
        "definition_term"
    } else if path.contains("/subject") {
        "subject"
    } else if path.contains("/object") {
        "object"
    } else if path.contains("/agent") {
        "agent"
    } else if path.contains("/roles") {
        "role"
    } else if path.contains("/predicate") {
        "predicate"
    } else if path.contains("/definiens") {
        "definition"
    } else {
        "noun"
    }
}

fn mention_edge(node: &Node, occurrence: &TermOccurrence, recorded_at: &str) -> Edge {
    let id = stable_id(
        "edge",
        &[
            GENERATION_VERSION,
            "mentions_term",
            &node.id,
            &occurrence.term.id,
            &occurrence.anchor.selector,
        ],
    );
    Edge {
        id,
        source: node.id.clone(),
        source_kind: VertexKind::Specification,
        target: occurrence.term.id.clone(),
        target_kind: VertexKind::Term,
        kind: EdgeKind::MentionsTerm,
        source_anchor: Some(occurrence.anchor.clone()),
        target_anchor: None,
        basis_spec_ids: Vec::new(),
        derivation: Derivation {
            method: "so-daemon.graph.term-form".to_string(),
            version: GENERATION_VERSION.to_string(),
        },
        recorded_at: recorded_at.to_string(),
    }
}

fn stable_id(kind: &str, parts: &[&str]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(kind.as_bytes());
    for part in parts {
        hasher.update([0]);
        hasher.update(part.as_bytes());
    }
    format!("{kind}-{:x}", hasher.finalize())
}

struct GraphGenerationPlugin;

impl NodeMetaPlugin for GraphGenerationPlugin {
    fn handles(&self, node: &Node) -> bool {
        node.lang_version == so_lang::LANG_VERSION && needs_generation(node)
    }

    fn run(&self, node: &Node, context: &PluginContext<'_>) -> Result<JobOutput, String> {
        let report = generate_and_persist(node, context.graph, context.now)
            .map_err(|error| error.to_string())?;
        Ok(JobOutput::metadata(json!({
            "version": GENERATION_VERSION,
            "terms_seen": report.terms_seen,
            "terms_inserted": report.terms_inserted,
            "mention_edges_inserted": report.mention_edges_inserted,
        })))
    }
}

fn graph_generation_factory() -> Box<dyn NodeMetaPlugin> {
    Box::new(GraphGenerationPlugin)
}

inventory::submit! {
    PluginRegistration::new(PLUGIN_NAME, graph_generation_factory)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Meta, VertexKind};
    use crate::store::{GraphStore, InMemoryNodeStore, NodeStore};

    fn node(id: &str, statement: &str) -> Node {
        Node {
            id: id.into(),
            statement: statement.into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: vec![],
                evidence: vec![],
                created_at: "2026-07-12T00:00:00Z".into(),
                cli: "test".into(),
                cli_version: "test".into(),
                updates: Default::default(),
            },
        }
    }

    #[test]
    fn stop_command_is_a_shared_term_hub_not_a_spec_to_spec_lexical_edge() {
        let store = InMemoryNodeStore::new();
        let a = node(
            "a",
            "When the emergency-stop button is pressed, the button controller shall issue the stop command.",
        );
        let b = node(
            "b",
            "When the motor controller receives the stop command, the motor controller shall disable the drive.",
        );
        store.add_node(&a).unwrap();
        store.add_node(&b).unwrap();
        generate_and_persist(&a, &store, "2026-07-12T00:00:01Z").unwrap();
        generate_and_persist(&b, &store, "2026-07-12T00:00:02Z").unwrap();

        let edges = store
            .list_edges(&["a".into(), "b".into()], GENERATION_VERSION)
            .unwrap();
        let shared_term = edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::MentionsTerm)
            .filter_map(|edge| {
                store
                    .get_term_nodes(std::slice::from_ref(&edge.target))
                    .unwrap()
                    .into_iter()
                    .next()
            })
            .find(|term| term.form == "stop command")
            .unwrap();
        let mentions = edges
            .iter()
            .filter(|edge| edge.target == shared_term.id)
            .collect::<Vec<_>>();
        assert_eq!(mentions.len(), 2);
        assert!(mentions
            .iter()
            .all(|edge| edge.target_kind == VertexKind::Term));
        assert!(!edges.iter().any(|edge| {
            edge.source_kind == VertexKind::Specification
                && edge.target_kind == VertexKind::Specification
        }));
    }
}
