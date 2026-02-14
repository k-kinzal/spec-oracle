use chrono::Utc;
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NodeKind {
    Assertion,
    Constraint,
    Scenario,
    Definition,
    Domain,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EdgeKind {
    Refines,
    DependsOn,
    Contradicts,
    DerivesFrom,
    Synonym,
    Composes,
    Formalizes,  // Target is a more formal version of source
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecNodeData {
    pub id: String,
    pub content: String,
    pub kind: NodeKind,
    pub metadata: HashMap<String, String>,
    #[serde(default)]
    pub created_at: i64,
    #[serde(default)]
    pub modified_at: i64,
    #[serde(default)]
    pub formality_layer: u8,  // 0=natural, 1=structured, 2=formal, 3=executable
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecEdgeData {
    pub id: String,
    pub kind: EdgeKind,
    pub metadata: HashMap<String, String>,
    #[serde(default)]
    pub created_at: i64,
}

#[derive(Debug, Clone)]
pub struct Contradiction {
    pub node_a: SpecNodeData,
    pub node_b: SpecNodeData,
    pub explanation: String,
}

#[derive(Debug, Clone)]
pub struct Omission {
    pub description: String,
    pub related_nodes: Vec<SpecNodeData>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecGraph {
    graph: DiGraph<SpecNodeData, SpecEdgeData>,
    #[serde(skip)]
    id_to_index: HashMap<String, NodeIndex>,
    #[serde(skip)]
    edge_id_to_index: HashMap<String, EdgeIndex>,
}

impl Default for SpecGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl SpecGraph {
    pub fn new() -> Self {
        Self {
            graph: DiGraph::new(),
            id_to_index: HashMap::new(),
            edge_id_to_index: HashMap::new(),
        }
    }

    /// Rebuild lookup indices after deserialization.
    pub fn rebuild_indices(&mut self) {
        self.id_to_index.clear();
        self.edge_id_to_index.clear();
        for idx in self.graph.node_indices() {
            let node = &self.graph[idx];
            self.id_to_index.insert(node.id.clone(), idx);
        }
        for idx in self.graph.edge_indices() {
            let edge = &self.graph[idx];
            self.edge_id_to_index.insert(edge.id.clone(), idx);
        }
    }

    pub fn add_node(
        &mut self,
        content: String,
        kind: NodeKind,
        metadata: HashMap<String, String>,
    ) -> &SpecNodeData {
        let id = Uuid::new_v4().to_string();
        let now = Utc::now().timestamp();
        let data = SpecNodeData {
            id: id.clone(),
            content,
            kind,
            metadata,
            created_at: now,
            modified_at: now,
            formality_layer: 0,  // Default to natural language
        };
        let idx = self.graph.add_node(data);
        self.id_to_index.insert(id, idx);
        &self.graph[idx]
    }

    pub fn get_node(&self, id: &str) -> Option<&SpecNodeData> {
        self.id_to_index.get(id).map(|&idx| &self.graph[idx])
    }

    pub fn remove_node(&mut self, id: &str) -> Option<SpecNodeData> {
        if let Some(&idx) = self.id_to_index.get(id) {
            // Remove related edge index entries
            let edge_indices: Vec<EdgeIndex> = self
                .graph
                .edges_directed(idx, Direction::Outgoing)
                .chain(self.graph.edges_directed(idx, Direction::Incoming))
                .map(|e| e.id())
                .collect();
            for eidx in edge_indices {
                if let Some(edge_data) = self.graph.edge_weight(eidx) {
                    self.edge_id_to_index.remove(&edge_data.id);
                }
            }

            let data = self.graph.remove_node(idx)?;
            self.id_to_index.remove(&data.id);

            // After removal petgraph may swap indices; rebuild to stay consistent.
            self.rebuild_indices();
            Some(data)
        } else {
            None
        }
    }

    pub fn list_nodes(&self, kind_filter: Option<NodeKind>) -> Vec<&SpecNodeData> {
        self.graph
            .node_weights()
            .filter(|n| kind_filter.is_none() || Some(n.kind) == kind_filter)
            .collect()
    }

    pub fn add_edge(
        &mut self,
        source_id: &str,
        target_id: &str,
        kind: EdgeKind,
        metadata: HashMap<String, String>,
    ) -> Result<&SpecEdgeData, GraphError> {
        let &src_idx = self
            .id_to_index
            .get(source_id)
            .ok_or_else(|| GraphError::NodeNotFound(source_id.to_string()))?;
        let &tgt_idx = self
            .id_to_index
            .get(target_id)
            .ok_or_else(|| GraphError::NodeNotFound(target_id.to_string()))?;

        let id = Uuid::new_v4().to_string();
        let now = Utc::now().timestamp();
        let data = SpecEdgeData {
            id: id.clone(),
            kind,
            metadata,
            created_at: now,
        };
        let eidx = self.graph.add_edge(src_idx, tgt_idx, data);
        self.edge_id_to_index.insert(id, eidx);
        Ok(&self.graph[eidx])
    }

    pub fn remove_edge(&mut self, id: &str) -> Option<SpecEdgeData> {
        if let Some(&eidx) = self.edge_id_to_index.get(id) {
            let data = self.graph.remove_edge(eidx)?;
            self.edge_id_to_index.remove(&data.id);
            // Edge removal can invalidate other edge indices; rebuild.
            self.rebuild_indices();
            Some(data)
        } else {
            None
        }
    }

    pub fn list_edges(&self, node_id: Option<&str>) -> Vec<(&SpecEdgeData, &str, &str)> {
        self.graph
            .edge_indices()
            .filter_map(|eidx| {
                let (src_idx, tgt_idx) = self.graph.edge_endpoints(eidx)?;
                let edge_data = &self.graph[eidx];
                let src_data = &self.graph[src_idx];
                let tgt_data = &self.graph[tgt_idx];
                if let Some(nid) = node_id {
                    if src_data.id != nid && tgt_data.id != nid {
                        return None;
                    }
                }
                Some((edge_data, src_data.id.as_str(), tgt_data.id.as_str()))
            })
            .collect()
    }

    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// Detect contradictions: pairs of nodes explicitly connected by a Contradicts edge,
    /// plus structural contradictions (e.g., constraint vs scenario on the same domain
    /// that logically conflict).
    pub fn detect_contradictions(&self) -> Vec<Contradiction> {
        let mut result = Vec::new();

        // Explicit contradiction edges
        for eidx in self.graph.edge_indices() {
            let edge = &self.graph[eidx];
            if edge.kind == EdgeKind::Contradicts {
                if let Some((src_idx, tgt_idx)) = self.graph.edge_endpoints(eidx) {
                    result.push(Contradiction {
                        node_a: self.graph[src_idx].clone(),
                        node_b: self.graph[tgt_idx].clone(),
                        explanation: format!(
                            "Explicit contradiction edge '{}'",
                            edge.id
                        ),
                    });
                }
            }
        }

        // Structural: nodes in the same domain with conflicting kinds
        // (Constraint + Scenario on same domain may indicate tension)
        let domains: Vec<(NodeIndex, &SpecNodeData)> = self
            .graph
            .node_indices()
            .map(|idx| (idx, &self.graph[idx]))
            .filter(|(_, n)| n.kind == NodeKind::Domain)
            .collect();

        for (domain_idx, _domain_data) in &domains {
            let children: Vec<(NodeIndex, &SpecNodeData)> = self
                .graph
                .edges_directed(*domain_idx, Direction::Incoming)
                .filter_map(|e| {
                    if self.graph[e.id()].kind == EdgeKind::Refines
                        || self.graph[e.id()].kind == EdgeKind::DependsOn
                    {
                        let src = e.source();
                        Some((src, &self.graph[src]))
                    } else {
                        None
                    }
                })
                .collect();

            let constraints: Vec<&SpecNodeData> = children
                .iter()
                .filter(|(_, n)| n.kind == NodeKind::Constraint)
                .map(|(_, n)| *n)
                .collect();
            let scenarios: Vec<&SpecNodeData> = children
                .iter()
                .filter(|(_, n)| n.kind == NodeKind::Scenario)
                .map(|(_, n)| *n)
                .collect();

            // Flag when constraints and scenarios coexist under the same domain —
            // this is a potential tension point that warrants review.
            if !constraints.is_empty() && !scenarios.is_empty() {
                for c in &constraints {
                    for s in &scenarios {
                        result.push(Contradiction {
                            node_a: (*c).clone(),
                            node_b: (*s).clone(),
                            explanation: format!(
                                "Potential tension: constraint and scenario under same domain"
                            ),
                        });
                    }
                }
            }
        }

        result
    }

    /// Detect omissions: nodes that have no edges (isolated), domains without
    /// any refinements, scenarios without supporting assertions.
    pub fn detect_omissions(&self) -> Vec<Omission> {
        let mut result = Vec::new();

        // Isolated nodes (no edges at all)
        for idx in self.graph.node_indices() {
            let incoming = self.graph.edges_directed(idx, Direction::Incoming).count();
            let outgoing = self.graph.edges_directed(idx, Direction::Outgoing).count();
            if incoming == 0 && outgoing == 0 {
                result.push(Omission {
                    description: "Isolated node with no relationships".to_string(),
                    related_nodes: vec![self.graph[idx].clone()],
                });
            }
        }

        // Domain nodes without any Refines edges pointing to them
        for idx in self.graph.node_indices() {
            let node = &self.graph[idx];
            if node.kind == NodeKind::Domain {
                let has_refinement = self
                    .graph
                    .edges_directed(idx, Direction::Incoming)
                    .any(|e| self.graph[e.id()].kind == EdgeKind::Refines);
                if !has_refinement {
                    result.push(Omission {
                        description: "Domain has no refinements".to_string(),
                        related_nodes: vec![node.clone()],
                    });
                }
            }
        }

        // Scenarios without supporting assertions
        for idx in self.graph.node_indices() {
            let node = &self.graph[idx];
            if node.kind == NodeKind::Scenario {
                let has_assertion = self
                    .graph
                    .edges_directed(idx, Direction::Incoming)
                    .any(|e| {
                        let src = e.source();
                        self.graph[src].kind == NodeKind::Assertion
                    });
                let has_outgoing_assertion = self
                    .graph
                    .edges_directed(idx, Direction::Outgoing)
                    .any(|e| {
                        let tgt = e.target();
                        self.graph[tgt].kind == NodeKind::Assertion
                    });
                if !has_assertion && !has_outgoing_assertion {
                    result.push(Omission {
                        description: "Scenario has no supporting assertions".to_string(),
                        related_nodes: vec![node.clone()],
                    });
                }
            }
        }

        result
    }

    /// Search nodes by content substring (case-insensitive).
    pub fn search(&self, query: &str) -> Vec<&SpecNodeData> {
        let q = query.to_lowercase();
        self.graph
            .node_weights()
            .filter(|n| n.content.to_lowercase().contains(&q))
            .collect()
    }

    /// Find all synonym groups: nodes connected by Synonym edges.
    pub fn resolve_term(&self, term: &str) -> (Vec<&SpecNodeData>, Vec<String>) {
        let t = term.to_lowercase();

        // Find definition nodes matching the term
        let definitions: Vec<&SpecNodeData> = self
            .graph
            .node_weights()
            .filter(|n| n.kind == NodeKind::Definition && n.content.to_lowercase().contains(&t))
            .collect();

        // Collect synonyms via Synonym edges
        let mut synonyms = Vec::new();
        for def in &definitions {
            if let Some(&idx) = self.id_to_index.get(&def.id) {
                for edge in self
                    .graph
                    .edges_directed(idx, Direction::Outgoing)
                    .chain(self.graph.edges_directed(idx, Direction::Incoming))
                {
                    if self.graph[edge.id()].kind == EdgeKind::Synonym {
                        let other_idx = if edge.source() == idx {
                            edge.target()
                        } else {
                            edge.source()
                        };
                        let other = &self.graph[other_idx];
                        if !synonyms.contains(&other.content) {
                            synonyms.push(other.content.clone());
                        }
                    }
                }
            }
        }

        (definitions, synonyms)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum GraphError {
    #[error("Node not found: {0}")]
    NodeNotFound(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_and_get_node() {
        let mut g = SpecGraph::new();
        let node = g.add_node("User must authenticate".into(), NodeKind::Assertion, HashMap::new());
        let id = node.id.clone();

        let fetched = g.get_node(&id).unwrap();
        assert_eq!(fetched.content, "User must authenticate");
        assert_eq!(fetched.kind, NodeKind::Assertion);
    }

    #[test]
    fn remove_node() {
        let mut g = SpecGraph::new();
        let id = g.add_node("temp".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        assert_eq!(g.node_count(), 1);

        let removed = g.remove_node(&id).unwrap();
        assert_eq!(removed.content, "temp");
        assert_eq!(g.node_count(), 0);
    }

    #[test]
    fn list_nodes_with_filter() {
        let mut g = SpecGraph::new();
        g.add_node("a".into(), NodeKind::Assertion, HashMap::new());
        g.add_node("c".into(), NodeKind::Constraint, HashMap::new());
        g.add_node("b".into(), NodeKind::Assertion, HashMap::new());

        let all = g.list_nodes(None);
        assert_eq!(all.len(), 3);

        let assertions = g.list_nodes(Some(NodeKind::Assertion));
        assert_eq!(assertions.len(), 2);
    }

    #[test]
    fn add_and_list_edges() {
        let mut g = SpecGraph::new();
        let a = g.add_node("parent".into(), NodeKind::Domain, HashMap::new()).id.clone();
        let b = g.add_node("child".into(), NodeKind::Assertion, HashMap::new()).id.clone();

        g.add_edge(&b, &a, EdgeKind::Refines, HashMap::new()).unwrap();
        assert_eq!(g.edge_count(), 1);

        let edges = g.list_edges(Some(&a));
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].0.kind, EdgeKind::Refines);
    }

    #[test]
    fn add_edge_node_not_found() {
        let mut g = SpecGraph::new();
        let a = g.add_node("a".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        let result = g.add_edge(&a, "nonexistent", EdgeKind::DependsOn, HashMap::new());
        assert!(result.is_err());
    }

    #[test]
    fn detect_explicit_contradiction() {
        let mut g = SpecGraph::new();
        let a = g.add_node("X must be > 0".into(), NodeKind::Constraint, HashMap::new()).id.clone();
        let b = g.add_node("X must be <= 0".into(), NodeKind::Constraint, HashMap::new()).id.clone();
        g.add_edge(&a, &b, EdgeKind::Contradicts, HashMap::new()).unwrap();

        let contradictions = g.detect_contradictions();
        assert_eq!(contradictions.len(), 1);
        assert!(contradictions[0].explanation.contains("Explicit contradiction"));
    }

    #[test]
    fn detect_omission_isolated_node() {
        let mut g = SpecGraph::new();
        g.add_node("lonely".into(), NodeKind::Assertion, HashMap::new());

        let omissions = g.detect_omissions();
        assert!(omissions.iter().any(|o| o.description.contains("Isolated")));
    }

    #[test]
    fn detect_omission_domain_without_refinements() {
        let mut g = SpecGraph::new();
        let d = g.add_node("Auth domain".into(), NodeKind::Domain, HashMap::new()).id.clone();
        // Add an edge that is NOT a refinement to keep it non-isolated
        let a = g.add_node("something".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        g.add_edge(&a, &d, EdgeKind::DependsOn, HashMap::new()).unwrap();

        let omissions = g.detect_omissions();
        assert!(omissions.iter().any(|o| o.description.contains("no refinements")));
    }

    #[test]
    fn detect_omission_scenario_without_assertions() {
        let mut g = SpecGraph::new();
        let s = g.add_node("User logs in".into(), NodeKind::Scenario, HashMap::new()).id.clone();
        let d = g.add_node("Auth domain".into(), NodeKind::Domain, HashMap::new()).id.clone();
        g.add_edge(&s, &d, EdgeKind::Refines, HashMap::new()).unwrap();

        let omissions = g.detect_omissions();
        assert!(omissions.iter().any(|o| o.description.contains("no supporting assertions")));
    }

    #[test]
    fn search_nodes() {
        let mut g = SpecGraph::new();
        g.add_node("User authentication required".into(), NodeKind::Assertion, HashMap::new());
        g.add_node("Data encryption at rest".into(), NodeKind::Constraint, HashMap::new());

        let results = g.search("auth");
        assert_eq!(results.len(), 1);
        assert!(results[0].content.contains("authentication"));
    }

    #[test]
    fn resolve_terminology() {
        let mut g = SpecGraph::new();
        let d1 = g.add_node("Authentication".into(), NodeKind::Definition, HashMap::new()).id.clone();
        let d2 = g.add_node("Login".into(), NodeKind::Definition, HashMap::new()).id.clone();
        g.add_edge(&d1, &d2, EdgeKind::Synonym, HashMap::new()).unwrap();

        let (defs, syns) = g.resolve_term("auth");
        assert_eq!(defs.len(), 1);
        assert!(syns.contains(&"Login".to_string()));
    }

    #[test]
    fn serialize_deserialize_roundtrip() {
        let mut g = SpecGraph::new();
        let a = g.add_node("node A".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        let b = g.add_node("node B".into(), NodeKind::Domain, HashMap::new()).id.clone();
        g.add_edge(&a, &b, EdgeKind::Refines, HashMap::new()).unwrap();

        let json = serde_json::to_string(&g).unwrap();
        let mut g2: SpecGraph = serde_json::from_str(&json).unwrap();
        g2.rebuild_indices();

        assert_eq!(g2.node_count(), 2);
        assert_eq!(g2.edge_count(), 1);
        assert!(g2.get_node(&a).is_some());
        assert!(g2.get_node(&b).is_some());
    }
}
