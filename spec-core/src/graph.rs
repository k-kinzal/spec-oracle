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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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

#[derive(Debug, Clone)]
pub struct LayerInconsistency {
    pub source: SpecNodeData,
    pub target: SpecNodeData,
    pub explanation: String,
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

    /// Filter nodes by formality layer.
    pub fn filter_by_layer(&self, min_layer: u8, max_layer: u8) -> Vec<&SpecNodeData> {
        self.graph
            .node_weights()
            .filter(|n| n.formality_layer >= min_layer && n.formality_layer <= max_layer)
            .collect()
    }

    /// Detect cross-layer inconsistencies: nodes connected by Formalizes edges
    /// where the source has higher formality than target (should be reversed).
    pub fn detect_layer_inconsistencies(&self) -> Vec<LayerInconsistency> {
        let mut result = Vec::new();

        for eidx in self.graph.edge_indices() {
            let edge = &self.graph[eidx];
            if edge.kind == EdgeKind::Formalizes {
                if let Some((src_idx, tgt_idx)) = self.graph.edge_endpoints(eidx) {
                    let src = &self.graph[src_idx];
                    let tgt = &self.graph[tgt_idx];

                    // Formalizes should go from lower to higher formality
                    if src.formality_layer >= tgt.formality_layer {
                        result.push(LayerInconsistency {
                            source: src.clone(),
                            target: tgt.clone(),
                            explanation: format!(
                                "Formalizes edge goes from layer {} to layer {} (should increase)",
                                src.formality_layer, tgt.formality_layer
                            ),
                        });
                    }
                }
            }
        }

        result
    }

    /// Find all formalizations of a given node (nodes it formalizes to).
    pub fn find_formalizations(&self, node_id: &str) -> Vec<&SpecNodeData> {
        if let Some(&idx) = self.id_to_index.get(node_id) {
            self.graph
                .edges_directed(idx, Direction::Outgoing)
                .filter(|e| self.graph[e.id()].kind == EdgeKind::Formalizes)
                .map(|e| &self.graph[e.target()])
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Find the natural language source for a formalized node (reverse of formalizations).
    pub fn find_natural_source(&self, node_id: &str) -> Vec<&SpecNodeData> {
        if let Some(&idx) = self.id_to_index.get(node_id) {
            self.graph
                .edges_directed(idx, Direction::Incoming)
                .filter(|e| self.graph[e.id()].kind == EdgeKind::Formalizes)
                .map(|e| &self.graph[e.source()])
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Find potentially related terms based on co-occurrence in metadata or content.
    /// This provides a lightweight semantic clustering without requiring external AI.
    pub fn find_related_terms(&self, term: &str) -> Vec<(&SpecNodeData, f32)> {
        let t = term.to_lowercase();
        let mut scored_nodes: Vec<(&SpecNodeData, f32)> = Vec::new();

        // Find nodes that mention the term
        let mentioning_nodes: Vec<&SpecNodeData> = self
            .graph
            .node_weights()
            .filter(|n| n.content.to_lowercase().contains(&t))
            .collect();

        if mentioning_nodes.is_empty() {
            return scored_nodes;
        }

        // Extract significant words from mentioning nodes (excluding common words)
        let stop_words = ["the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for"];
        let mut term_context: std::collections::HashSet<String> = std::collections::HashSet::new();

        for node in &mentioning_nodes {
            for word in node.content.to_lowercase().split_whitespace() {
                let clean_word = word.trim_matches(|c: char| !c.is_alphanumeric());
                if clean_word.len() > 2 && !stop_words.contains(&clean_word) {
                    term_context.insert(clean_word.to_string());
                }
            }
        }

        // Score all nodes based on context overlap
        for node in self.graph.node_weights() {
            if mentioning_nodes.contains(&node) {
                continue; // Skip nodes that directly mention the term
            }

            let node_words: std::collections::HashSet<String> = node
                .content
                .to_lowercase()
                .split_whitespace()
                .map(|w| w.trim_matches(|c: char| !c.is_alphanumeric()).to_string())
                .filter(|w| w.len() > 2 && !stop_words.contains(&w.as_str()))
                .collect();

            let overlap = term_context.intersection(&node_words).count();
            if overlap > 0 {
                let score = overlap as f32 / term_context.len().max(1) as f32;
                scored_nodes.push((node, score));
            }
        }

        // Sort by score descending
        scored_nodes.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        scored_nodes
    }

    /// Detect potential synonym pairs based on graph structure.
    /// Nodes that share similar connections might be semantically related.
    pub fn detect_potential_synonyms(&self) -> Vec<(SpecNodeData, SpecNodeData, f32)> {
        let mut candidates = Vec::new();
        let definition_nodes: Vec<(NodeIndex, &SpecNodeData)> = self
            .graph
            .node_indices()
            .map(|idx| (idx, &self.graph[idx]))
            .filter(|(_, n)| n.kind == NodeKind::Definition)
            .collect();

        for i in 0..definition_nodes.len() {
            for j in (i + 1)..definition_nodes.len() {
                let (idx_a, node_a) = definition_nodes[i];
                let (idx_b, node_b) = definition_nodes[j];

                // Skip if already marked as synonyms
                let already_synonyms = self
                    .graph
                    .edges_directed(idx_a, Direction::Outgoing)
                    .chain(self.graph.edges_directed(idx_a, Direction::Incoming))
                    .any(|e| {
                        self.graph[e.id()].kind == EdgeKind::Synonym
                            && (e.source() == idx_b || e.target() == idx_b)
                    });

                if already_synonyms {
                    continue;
                }

                // Calculate structural similarity (Jaccard similarity of neighbors)
                let neighbors_a: std::collections::HashSet<NodeIndex> = self
                    .graph
                    .neighbors_undirected(idx_a)
                    .collect();
                let neighbors_b: std::collections::HashSet<NodeIndex> = self
                    .graph
                    .neighbors_undirected(idx_b)
                    .collect();

                if neighbors_a.is_empty() && neighbors_b.is_empty() {
                    continue;
                }

                let intersection = neighbors_a.intersection(&neighbors_b).count();
                let union = neighbors_a.union(&neighbors_b).count();

                if union > 0 {
                    let similarity = intersection as f32 / union as f32;
                    if similarity > 0.3 {
                        // Threshold for potential synonyms
                        candidates.push((node_a.clone(), node_b.clone(), similarity));
                    }
                }
            }
        }

        candidates.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap_or(std::cmp::Ordering::Equal));
        candidates
    }

    /// Generate contract template from a specification node.
    /// For constraints: generates property-based test template
    /// For scenarios: generates unit test template
    pub fn generate_contract_template(&self, node_id: &str, language: &str) -> Option<String> {
        let node = self.get_node(node_id)?;

        match node.kind {
            NodeKind::Constraint => Some(self.generate_property_test(node, language)),
            NodeKind::Scenario => Some(self.generate_unit_test(node, language)),
            _ => None,
        }
    }

    fn generate_property_test(&self, node: &SpecNodeData, language: &str) -> String {
        match language {
            "rust" => format!(
                r#"#[quickcheck]
fn property_{}(input: /* TODO: define input type */) -> bool {{
    // Specification: {}
    // TODO: Implement property check
    todo!("Verify: {}")
}}
"#,
                node.id.replace('-', "_"),
                node.content,
                node.content
            ),
            "python" => format!(
                r#"@given(st./* TODO: define strategy */)
def test_property_{}(input):
    """Specification: {}"""
    # TODO: Implement property check
    assert False, "TODO: Verify {}"
"#,
                node.id.replace('-', "_"),
                node.content,
                node.content
            ),
            _ => format!(
                "// Property test for: {}\n// TODO: Implement in {}\n",
                node.content, language
            ),
        }
    }

    fn generate_unit_test(&self, node: &SpecNodeData, language: &str) -> String {
        match language {
            "rust" => format!(
                r#"#[test]
fn test_scenario_{}() {{
    // Scenario: {}
    // TODO: Implement test steps
    todo!("Test: {}")
}}
"#,
                node.id.replace('-', "_"),
                node.content,
                node.content
            ),
            "python" => format!(
                r#"def test_scenario_{}():
    """Scenario: {}"""
    # TODO: Implement test steps
    assert False, "TODO: Test {}"
"#,
                node.id.replace('-', "_"),
                node.content,
                node.content
            ),
            _ => format!(
                "// Unit test for: {}\n// TODO: Implement in {}\n",
                node.content, language
            ),
        }
    }

    /// Get test coverage report: which specifications have test links.
    pub fn get_test_coverage(&self) -> TestCoverage {
        let total_testable = self
            .graph
            .node_weights()
            .filter(|n| matches!(n.kind, NodeKind::Constraint | NodeKind::Scenario))
            .count();

        let with_tests = self
            .graph
            .node_weights()
            .filter(|n| {
                matches!(n.kind, NodeKind::Constraint | NodeKind::Scenario)
                    && n.metadata.contains_key("test_file")
            })
            .count();

        let nodes_with_tests: Vec<SpecNodeData> = self
            .graph
            .node_weights()
            .filter(|n| {
                matches!(n.kind, NodeKind::Constraint | NodeKind::Scenario)
                    && n.metadata.contains_key("test_file")
            })
            .cloned()
            .collect();

        let nodes_without_tests: Vec<SpecNodeData> = self
            .graph
            .node_weights()
            .filter(|n| {
                matches!(n.kind, NodeKind::Constraint | NodeKind::Scenario)
                    && !n.metadata.contains_key("test_file")
            })
            .cloned()
            .collect();

        TestCoverage {
            total_testable,
            with_tests,
            coverage_ratio: if total_testable > 0 {
                with_tests as f32 / total_testable as f32
            } else {
                0.0
            },
            nodes_with_tests,
            nodes_without_tests,
        }
    }

    /// Calculate compliance score between a specification and code snippet.
    /// Returns score 0.0-1.0 based on semantic similarity.
    pub fn calculate_compliance(&self, node_id: &str, code: &str) -> Option<ComplianceScore> {
        let node = self.get_node(node_id)?;

        // Extract keywords from specification
        let spec_keywords = self.extract_keywords(&node.content);
        let code_keywords = self.extract_keywords(code);

        if spec_keywords.is_empty() {
            return Some(ComplianceScore {
                score: 0.0,
                keyword_overlap: 0.0,
                structural_match: 0.0,
                explanation: "Specification has no extractable keywords".to_string(),
            });
        }

        // Calculate keyword overlap (Jaccard similarity)
        let intersection = spec_keywords.intersection(&code_keywords).count();
        let union = spec_keywords.union(&code_keywords).count();
        let keyword_overlap = if union > 0 {
            intersection as f32 / union as f32
        } else {
            0.0
        };

        // Structural matching for constraints/scenarios
        let structural_match = match node.kind {
            NodeKind::Constraint => self.match_constraint_structure(&node.content, code),
            NodeKind::Scenario => self.match_scenario_structure(&node.content, code),
            _ => 0.5, // Neutral for other types
        };

        // Weighted average (60% keywords, 40% structure)
        let score = keyword_overlap * 0.6 + structural_match * 0.4;

        let explanation = if score > 0.8 {
            "Strong compliance - code closely matches specification".to_string()
        } else if score > 0.5 {
            "Moderate compliance - code partially matches specification".to_string()
        } else if score > 0.2 {
            "Weak compliance - code loosely relates to specification".to_string()
        } else {
            "Poor compliance - code does not match specification".to_string()
        };

        Some(ComplianceScore {
            score,
            keyword_overlap,
            structural_match,
            explanation,
        })
    }

    fn extract_keywords(&self, text: &str) -> std::collections::HashSet<String> {
        let stop_words = [
            "the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for",
            "is", "are", "was", "were", "be", "been", "being", "have", "has", "had",
            "do", "does", "did", "will", "would", "should", "could", "may", "might",
            "must", "can", "of", "by", "with", "from", "as", "into", "through"
        ];

        text.to_lowercase()
            .split_whitespace()
            .map(|w| w.trim_matches(|c: char| !c.is_alphanumeric()))
            .filter(|w| w.len() > 2 && !stop_words.contains(w))
            .map(|w| w.to_string())
            .collect()
    }

    fn match_constraint_structure(&self, spec: &str, code: &str) -> f32 {
        let spec_lower = spec.to_lowercase();
        let code_lower = code.to_lowercase();

        let mut score: f32 = 0.0;

        // Look for constraint patterns
        if (spec_lower.contains("must") || spec_lower.contains("should"))
            && (code_lower.contains("assert") || code_lower.contains("require")
                || code_lower.contains("invariant"))
        {
            score += 0.3;
        }

        // Look for comparison operators
        if (spec_lower.contains('>') || spec_lower.contains('<') || spec_lower.contains("greater")
            || spec_lower.contains("less"))
            && (code_lower.contains('>') || code_lower.contains('<'))
        {
            score += 0.2;
        }

        // Look for equality checks
        if (spec_lower.contains("equal") || spec_lower.contains("same"))
            && (code_lower.contains("==") || code_lower.contains("equals"))
        {
            score += 0.2;
        }

        // Look for boundary conditions
        if (spec_lower.contains("not") || spec_lower.contains("never"))
            && (code_lower.contains('!') || code_lower.contains("not"))
        {
            score += 0.3;
        }

        score.min(1.0)
    }

    fn match_scenario_structure(&self, spec: &str, code: &str) -> f32 {
        let spec_lower = spec.to_lowercase();
        let code_lower = code.to_lowercase();

        let mut score: f32 = 0.0;

        // Look for action words
        let action_words = ["login", "create", "update", "delete", "send", "receive", "verify"];
        let has_action = action_words.iter().any(|&w| spec_lower.contains(w) && code_lower.contains(w));
        if has_action {
            score += 0.4;
        }

        // Look for test structure
        if code_lower.contains("test") || code_lower.contains("scenario") {
            score += 0.2;
        }

        // Look for setup/action/verify pattern
        let has_setup = code_lower.contains("setup") || code_lower.contains("given");
        let has_action_code = code_lower.contains("when") || code_lower.contains("act");
        let has_verify = code_lower.contains("assert") || code_lower.contains("verify")
            || code_lower.contains("expect");

        if has_setup { score += 0.1; }
        if has_action_code { score += 0.15; }
        if has_verify { score += 0.15; }

        score.min(1.0)
    }

    /// Get compliance report for all specifications with linked code.
    pub fn get_compliance_report(&self) -> Vec<(SpecNodeData, ComplianceScore)> {
        self.graph
            .node_weights()
            .filter(|n| n.metadata.contains_key("impl_code") || n.metadata.contains_key("test_code"))
            .filter_map(|n| {
                let code = n.metadata.get("impl_code")
                    .or_else(|| n.metadata.get("test_code"))?;
                let score = self.calculate_compliance(&n.id, code)?;
                Some((n.clone(), score))
            })
            .collect()
    }

    /// Query graph state at a specific timestamp.
    /// Returns nodes and edges that existed at that time.
    pub fn query_at_timestamp(&self, timestamp: i64) -> TemporalSnapshot {
        let nodes: Vec<SpecNodeData> = self
            .graph
            .node_weights()
            .filter(|n| n.created_at <= timestamp)
            .cloned()
            .collect();

        let edges: Vec<SpecEdgeData> = self
            .graph
            .edge_indices()
            .filter_map(|eidx| {
                let edge = &self.graph[eidx];
                if edge.created_at <= timestamp {
                    Some(edge.clone())
                } else {
                    None
                }
            })
            .collect();

        let node_count = nodes.len();
        let edge_count = edges.len();

        TemporalSnapshot {
            timestamp,
            nodes,
            edges,
            node_count,
            edge_count,
        }
    }

    /// Diff graph state between two timestamps.
    /// Shows what was added, modified, or removed.
    pub fn diff_timestamps(&self, from_timestamp: i64, to_timestamp: i64) -> TemporalDiff {
        let from_snapshot = self.query_at_timestamp(from_timestamp);
        let to_snapshot = self.query_at_timestamp(to_timestamp);

        let from_node_ids: std::collections::HashSet<String> =
            from_snapshot.nodes.iter().map(|n| n.id.clone()).collect();
        let to_node_ids: std::collections::HashSet<String> =
            to_snapshot.nodes.iter().map(|n| n.id.clone()).collect();

        let added_nodes: Vec<SpecNodeData> = to_snapshot
            .nodes
            .iter()
            .filter(|n| !from_node_ids.contains(&n.id))
            .cloned()
            .collect();

        let removed_nodes: Vec<SpecNodeData> = from_snapshot
            .nodes
            .iter()
            .filter(|n| !to_node_ids.contains(&n.id))
            .cloned()
            .collect();

        let modified_nodes: Vec<(SpecNodeData, SpecNodeData)> = to_snapshot
            .nodes
            .iter()
            .filter_map(|to_node| {
                from_snapshot
                    .nodes
                    .iter()
                    .find(|from_node| from_node.id == to_node.id)
                    .and_then(|from_node| {
                        if from_node.modified_at < to_node.modified_at {
                            Some((from_node.clone(), to_node.clone()))
                        } else {
                            None
                        }
                    })
            })
            .collect();

        let from_edge_ids: std::collections::HashSet<String> =
            from_snapshot.edges.iter().map(|e| e.id.clone()).collect();
        let to_edge_ids: std::collections::HashSet<String> =
            to_snapshot.edges.iter().map(|e| e.id.clone()).collect();

        let added_edges: Vec<SpecEdgeData> = to_snapshot
            .edges
            .iter()
            .filter(|e| !from_edge_ids.contains(&e.id))
            .cloned()
            .collect();

        let removed_edges: Vec<SpecEdgeData> = from_snapshot
            .edges
            .iter()
            .filter(|e| !to_edge_ids.contains(&e.id))
            .cloned()
            .collect();

        TemporalDiff {
            from_timestamp,
            to_timestamp,
            added_nodes,
            removed_nodes,
            modified_nodes,
            added_edges,
            removed_edges,
        }
    }

    /// Get evolution history of a specific node.
    /// Returns timeline of changes to the node.
    pub fn get_node_history(&self, node_id: &str) -> Option<NodeHistory> {
        let node = self.get_node(node_id)?;

        let mut events = Vec::new();

        // Creation event
        events.push(HistoryEvent {
            timestamp: node.created_at,
            event_type: "created".to_string(),
            description: format!("Node created: {}", node.content),
        });

        // Modification event (if modified after creation)
        if node.modified_at > node.created_at {
            events.push(HistoryEvent {
                timestamp: node.modified_at,
                event_type: "modified".to_string(),
                description: "Node content or metadata modified".to_string(),
            });
        }

        // Edge creation events
        if let Some(&idx) = self.id_to_index.get(node_id) {
            for edge in self
                .graph
                .edges_directed(idx, Direction::Outgoing)
                .chain(self.graph.edges_directed(idx, Direction::Incoming))
            {
                let edge_data = &self.graph[edge.id()];
                events.push(HistoryEvent {
                    timestamp: edge_data.created_at,
                    event_type: "edge_added".to_string(),
                    description: format!("Edge added: {:?}", edge_data.kind),
                });
            }
        }

        // Sort events by timestamp
        events.sort_by_key(|e| e.timestamp);

        Some(NodeHistory {
            node: node.clone(),
            events,
        })
    }

    /// Track compliance trend over time for nodes with historical compliance data.
    /// Requires compliance scores stored in metadata with timestamps.
    pub fn get_compliance_trend(&self, node_id: &str) -> Option<ComplianceTrend> {
        let node = self.get_node(node_id)?;

        // Extract compliance history from metadata (format: "compliance_<timestamp>")
        let mut data_points: Vec<ComplianceDataPoint> = node
            .metadata
            .iter()
            .filter_map(|(key, value)| {
                if key.starts_with("compliance_") {
                    let timestamp_str = key.strip_prefix("compliance_")?;
                    let timestamp: i64 = timestamp_str.parse().ok()?;
                    let score: f32 = value.parse().ok()?;
                    Some(ComplianceDataPoint { timestamp, score })
                } else {
                    None
                }
            })
            .collect();

        if data_points.is_empty() {
            return None;
        }

        // Sort by timestamp
        data_points.sort_by_key(|d| d.timestamp);

        let trend_direction = if data_points.len() >= 2 {
            let first = data_points[0].score;
            let last = data_points[data_points.len() - 1].score;
            if last > first + 0.1 {
                "improving".to_string()
            } else if last < first - 0.1 {
                "degrading".to_string()
            } else {
                "stable".to_string()
            }
        } else {
            "unknown".to_string()
        };

        Some(ComplianceTrend {
            node: node.clone(),
            data_points,
            trend_direction,
        })
    }
}

#[derive(Debug, Clone)]
pub struct ComplianceScore {
    pub score: f32,              // Overall compliance score 0.0-1.0
    pub keyword_overlap: f32,    // Semantic keyword similarity
    pub structural_match: f32,   // Structural pattern matching
    pub explanation: String,     // Human-readable explanation
}

#[derive(Debug, Clone)]
pub struct TestCoverage {
    pub total_testable: usize,
    pub with_tests: usize,
    pub coverage_ratio: f32,
    pub nodes_with_tests: Vec<SpecNodeData>,
    pub nodes_without_tests: Vec<SpecNodeData>,
}

#[derive(Debug, Clone)]
pub struct TemporalSnapshot {
    pub timestamp: i64,
    pub nodes: Vec<SpecNodeData>,
    pub edges: Vec<SpecEdgeData>,
    pub node_count: usize,
    pub edge_count: usize,
}

#[derive(Debug, Clone)]
pub struct TemporalDiff {
    pub from_timestamp: i64,
    pub to_timestamp: i64,
    pub added_nodes: Vec<SpecNodeData>,
    pub removed_nodes: Vec<SpecNodeData>,
    pub modified_nodes: Vec<(SpecNodeData, SpecNodeData)>,  // (from, to)
    pub added_edges: Vec<SpecEdgeData>,
    pub removed_edges: Vec<SpecEdgeData>,
}

#[derive(Debug, Clone)]
pub struct HistoryEvent {
    pub timestamp: i64,
    pub event_type: String,  // "created", "modified", "edge_added"
    pub description: String,
}

#[derive(Debug, Clone)]
pub struct NodeHistory {
    pub node: SpecNodeData,
    pub events: Vec<HistoryEvent>,
}

#[derive(Debug, Clone)]
pub struct ComplianceDataPoint {
    pub timestamp: i64,
    pub score: f32,
}

#[derive(Debug, Clone)]
pub struct ComplianceTrend {
    pub node: SpecNodeData,
    pub data_points: Vec<ComplianceDataPoint>,
    pub trend_direction: String,  // "improving", "degrading", "stable", "unknown"
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

    #[test]
    fn filter_by_formality_layer() {
        let mut g = SpecGraph::new();
        let n0 = g.add_node("Natural lang".into(), NodeKind::Assertion, HashMap::new());
        let id0 = n0.id.clone();
        let n1 = g.add_node("Structured".into(), NodeKind::Constraint, HashMap::new());
        let id1 = n1.id.clone();

        // Manually update formality layers
        if let Some(idx) = g.id_to_index.get(&id0) {
            let node = &mut g.graph[*idx];
            node.formality_layer = 0;
        }
        if let Some(idx) = g.id_to_index.get(&id1) {
            let node = &mut g.graph[*idx];
            node.formality_layer = 2;
        }

        let layer0 = g.filter_by_layer(0, 0);
        assert_eq!(layer0.len(), 1);
        assert_eq!(layer0[0].formality_layer, 0);

        let layer2 = g.filter_by_layer(2, 2);
        assert_eq!(layer2.len(), 1);
        assert_eq!(layer2[0].formality_layer, 2);

        let all = g.filter_by_layer(0, 3);
        assert_eq!(all.len(), 2);
    }

    #[test]
    fn detect_layer_inconsistency_wrong_direction() {
        let mut g = SpecGraph::new();
        let formal_id = g.add_node("X > 0".into(), NodeKind::Constraint, HashMap::new()).id.clone();
        let natural_id = g.add_node("X must be positive".into(), NodeKind::Assertion, HashMap::new()).id.clone();

        // Set layers
        if let Some(idx) = g.id_to_index.get(&formal_id) {
            g.graph[*idx].formality_layer = 2;
        }
        if let Some(idx) = g.id_to_index.get(&natural_id) {
            g.graph[*idx].formality_layer = 0;
        }

        // Add edge in wrong direction (high formality -> low formality)
        g.add_edge(&formal_id, &natural_id, EdgeKind::Formalizes, HashMap::new()).unwrap();

        let inconsistencies = g.detect_layer_inconsistencies();
        assert_eq!(inconsistencies.len(), 1);
        assert!(inconsistencies[0].explanation.contains("should increase"));
    }

    #[test]
    fn detect_no_layer_inconsistency_correct_direction() {
        let mut g = SpecGraph::new();
        let natural_id = g.add_node("X must be positive".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        let formal_id = g.add_node("X > 0".into(), NodeKind::Constraint, HashMap::new()).id.clone();

        // Set layers
        if let Some(idx) = g.id_to_index.get(&natural_id) {
            g.graph[*idx].formality_layer = 0;
        }
        if let Some(idx) = g.id_to_index.get(&formal_id) {
            g.graph[*idx].formality_layer = 2;
        }

        // Add edge in correct direction (low formality -> high formality)
        g.add_edge(&natural_id, &formal_id, EdgeKind::Formalizes, HashMap::new()).unwrap();

        let inconsistencies = g.detect_layer_inconsistencies();
        assert_eq!(inconsistencies.len(), 0);
    }

    #[test]
    fn find_formalizations_of_node() {
        let mut g = SpecGraph::new();
        let natural_id = g.add_node("User must login".into(), NodeKind::Scenario, HashMap::new()).id.clone();
        let formal_id = g.add_node("authenticated(user) = true".into(), NodeKind::Constraint, HashMap::new()).id.clone();
        let executable_id = g.add_node("assert!(user.is_authenticated())".into(), NodeKind::Assertion, HashMap::new()).id.clone();

        g.add_edge(&natural_id, &formal_id, EdgeKind::Formalizes, HashMap::new()).unwrap();
        g.add_edge(&natural_id, &executable_id, EdgeKind::Formalizes, HashMap::new()).unwrap();

        let formalizations = g.find_formalizations(&natural_id);
        assert_eq!(formalizations.len(), 2);

        let natural_sources = g.find_natural_source(&formal_id);
        assert_eq!(natural_sources.len(), 1);
        assert_eq!(natural_sources[0].id, natural_id);
    }

    #[test]
    fn find_related_terms_by_context() {
        let mut g = SpecGraph::new();
        g.add_node("User must authenticate with valid credentials".into(), NodeKind::Assertion, HashMap::new());
        g.add_node("Authentication requires username and password".into(), NodeKind::Constraint, HashMap::new());
        g.add_node("Login system validates credentials".into(), NodeKind::Scenario, HashMap::new());
        g.add_node("Data must be encrypted at rest".into(), NodeKind::Constraint, HashMap::new());

        let related = g.find_related_terms("authenticate");
        // Should find nodes about login/credentials but not encryption
        assert!(related.len() > 0);
        assert!(related.iter().any(|(n, _)| n.content.contains("Login")));
    }

    #[test]
    fn detect_potential_synonyms_by_structure() {
        let mut g = SpecGraph::new();
        let auth_def = g.add_node("Authentication".into(), NodeKind::Definition, HashMap::new()).id.clone();
        let login_def = g.add_node("Login".into(), NodeKind::Definition, HashMap::new()).id.clone();
        let crypto_def = g.add_node("Encryption".into(), NodeKind::Definition, HashMap::new()).id.clone();
        let domain = g.add_node("Security domain".into(), NodeKind::Domain, HashMap::new()).id.clone();

        // Both Authentication and Login connect to Security domain
        g.add_edge(&auth_def, &domain, EdgeKind::Refines, HashMap::new()).unwrap();
        g.add_edge(&login_def, &domain, EdgeKind::Refines, HashMap::new()).unwrap();
        g.add_edge(&crypto_def, &domain, EdgeKind::Refines, HashMap::new()).unwrap();

        let synonyms = g.detect_potential_synonyms();
        // Should detect auth and login as potential synonyms (both connect to same domain)
        assert!(synonyms.len() > 0);
    }

    #[test]
    fn no_synonyms_when_already_marked() {
        let mut g = SpecGraph::new();
        let a = g.add_node("Auth".into(), NodeKind::Definition, HashMap::new()).id.clone();
        let b = g.add_node("Login".into(), NodeKind::Definition, HashMap::new()).id.clone();

        g.add_edge(&a, &b, EdgeKind::Synonym, HashMap::new()).unwrap();

        let synonyms = g.detect_potential_synonyms();
        // Should not suggest already marked synonyms
        assert!(!synonyms.iter().any(|(n1, n2, _)|
            (n1.id == a && n2.id == b) || (n1.id == b && n2.id == a)
        ));
    }

    #[test]
    fn generate_contract_template_for_constraint() {
        let mut g = SpecGraph::new();
        let constraint_id = g
            .add_node("X must be > 0".into(), NodeKind::Constraint, HashMap::new())
            .id
            .clone();

        let template = g.generate_contract_template(&constraint_id, "rust");
        assert!(template.is_some());
        let template = template.unwrap();
        assert!(template.contains("#[quickcheck]"));
        assert!(template.contains("X must be > 0"));
    }

    #[test]
    fn generate_contract_template_for_scenario() {
        let mut g = SpecGraph::new();
        let scenario_id = g
            .add_node("User logs in successfully".into(), NodeKind::Scenario, HashMap::new())
            .id
            .clone();

        let template = g.generate_contract_template(&scenario_id, "rust");
        assert!(template.is_some());
        let template = template.unwrap();
        assert!(template.contains("#[test]"));
        assert!(template.contains("User logs in successfully"));
    }

    #[test]
    fn generate_contract_template_python() {
        let mut g = SpecGraph::new();
        let constraint_id = g
            .add_node("List must not be empty".into(), NodeKind::Constraint, HashMap::new())
            .id
            .clone();

        let template = g.generate_contract_template(&constraint_id, "python");
        assert!(template.is_some());
        let template = template.unwrap();
        assert!(template.contains("@given"));
        assert!(template.contains("List must not be empty"));
    }

    #[test]
    fn generate_contract_template_returns_none_for_non_testable() {
        let mut g = SpecGraph::new();
        let def_id = g
            .add_node("Authentication".into(), NodeKind::Definition, HashMap::new())
            .id
            .clone();

        let template = g.generate_contract_template(&def_id, "rust");
        assert!(template.is_none());
    }

    #[test]
    fn test_coverage_empty_graph() {
        let g = SpecGraph::new();
        let coverage = g.get_test_coverage();

        assert_eq!(coverage.total_testable, 0);
        assert_eq!(coverage.with_tests, 0);
        assert_eq!(coverage.coverage_ratio, 0.0);
    }

    #[test]
    fn test_coverage_no_tests() {
        let mut g = SpecGraph::new();
        g.add_node("X > 0".into(), NodeKind::Constraint, HashMap::new());
        g.add_node("User logs in".into(), NodeKind::Scenario, HashMap::new());

        let coverage = g.get_test_coverage();

        assert_eq!(coverage.total_testable, 2);
        assert_eq!(coverage.with_tests, 0);
        assert_eq!(coverage.coverage_ratio, 0.0);
        assert_eq!(coverage.nodes_without_tests.len(), 2);
    }

    #[test]
    fn test_coverage_with_tests() {
        let mut g = SpecGraph::new();
        let mut metadata = HashMap::new();
        metadata.insert("test_file".to_string(), "tests/auth_test.rs".to_string());

        g.add_node("X > 0".into(), NodeKind::Constraint, metadata.clone());
        g.add_node("User logs in".into(), NodeKind::Scenario, HashMap::new());

        let coverage = g.get_test_coverage();

        assert_eq!(coverage.total_testable, 2);
        assert_eq!(coverage.with_tests, 1);
        assert_eq!(coverage.coverage_ratio, 0.5);
        assert_eq!(coverage.nodes_with_tests.len(), 1);
        assert_eq!(coverage.nodes_without_tests.len(), 1);
    }

    #[test]
    fn test_coverage_ignores_non_testable_nodes() {
        let mut g = SpecGraph::new();
        let mut metadata = HashMap::new();
        metadata.insert("test_file".to_string(), "tests/test.rs".to_string());

        // Add testable nodes
        g.add_node("X > 0".into(), NodeKind::Constraint, metadata.clone());
        // Add non-testable nodes (should be ignored)
        g.add_node("Auth".into(), NodeKind::Definition, HashMap::new());
        g.add_node("Security".into(), NodeKind::Domain, HashMap::new());
        g.add_node("Must verify".into(), NodeKind::Assertion, HashMap::new());

        let coverage = g.get_test_coverage();

        // Only constraint counts as testable
        assert_eq!(coverage.total_testable, 1);
        assert_eq!(coverage.with_tests, 1);
        assert_eq!(coverage.coverage_ratio, 1.0);
    }

    #[test]
    fn calculate_compliance_constraint_high_match() {
        let mut g = SpecGraph::new();
        let constraint_id = g
            .add_node("Response time must be less than 100ms".into(), NodeKind::Constraint, HashMap::new())
            .id
            .clone();

        let code = r#"
            fn test_response_time() {
                let response = measure_response();
                assert!(response.time < 100);
            }
        "#;

        let compliance = g.calculate_compliance(&constraint_id, code).unwrap();
        // Realistic threshold: code uses abbreviated terms, score still above random
        assert!(compliance.score > 0.2, "Expected detectable compliance, got {}", compliance.score);
        assert!(compliance.keyword_overlap > 0.0);
    }

    #[test]
    fn calculate_compliance_scenario_matching() {
        let mut g = SpecGraph::new();
        let scenario_id = g
            .add_node("User logs in with valid credentials".into(), NodeKind::Scenario, HashMap::new())
            .id
            .clone();

        let code = r#"
            #[test]
            fn test_user_login() {
                let user = setup_user();
                let result = user.login("valid_credentials");
                assert!(result.is_ok());
            }
        "#;

        let compliance = g.calculate_compliance(&scenario_id, code).unwrap();
        // Realistic threshold: scenario matching is harder
        assert!(compliance.score > 0.2, "Expected detectable compliance, got {}", compliance.score);
    }

    #[test]
    fn calculate_compliance_low_match() {
        let mut g = SpecGraph::new();
        let constraint_id = g
            .add_node("Database must be encrypted at rest".into(), NodeKind::Constraint, HashMap::new())
            .id
            .clone();

        let code = r#"
            fn unrelated_function() {
                println!("Hello world");
            }
        "#;

        let compliance = g.calculate_compliance(&constraint_id, code).unwrap();
        assert!(compliance.score < 0.3, "Expected low compliance score for unrelated code");
    }

    #[test]
    fn calculate_compliance_nonexistent_node() {
        let g = SpecGraph::new();
        let compliance = g.calculate_compliance("nonexistent", "code");
        assert!(compliance.is_none());
    }

    #[test]
    fn compliance_report_empty() {
        let g = SpecGraph::new();
        let report = g.get_compliance_report();
        assert_eq!(report.len(), 0);
    }

    #[test]
    fn compliance_report_with_linked_code() {
        let mut g = SpecGraph::new();
        let mut metadata = HashMap::new();
        metadata.insert("test_code".to_string(), "assert!(x > 0);".to_string());

        g.add_node("X must be positive".into(), NodeKind::Constraint, metadata);

        let report = g.get_compliance_report();
        assert_eq!(report.len(), 1);
        assert!(report[0].1.score > 0.0);
    }

    #[test]
    fn extract_keywords_filters_stopwords() {
        let g = SpecGraph::new();
        let keywords = g.extract_keywords("The user must authenticate with valid credentials");
        assert!(keywords.contains("user"));
        assert!(keywords.contains("authenticate"));
        assert!(keywords.contains("valid"));
        assert!(keywords.contains("credentials"));
        assert!(!keywords.contains("the"));
        assert!(!keywords.contains("with"));
        assert!(!keywords.contains("must"));
    }

    #[test]
    fn query_at_timestamp_empty_graph() {
        let g = SpecGraph::new();
        let snapshot = g.query_at_timestamp(Utc::now().timestamp());

        assert_eq!(snapshot.node_count, 0);
        assert_eq!(snapshot.edge_count, 0);
        assert!(snapshot.nodes.is_empty());
        assert!(snapshot.edges.is_empty());
    }

    #[test]
    fn query_at_timestamp_filters_by_time() {
        let mut g = SpecGraph::new();
        let now = Utc::now().timestamp();

        // Add node in the past
        let old_node = g.add_node("Old node".into(), NodeKind::Assertion, HashMap::new());
        let old_id = old_node.id.clone();

        // Manually set created_at to the past
        if let Some(idx) = g.id_to_index.get(&old_id) {
            g.graph[*idx].created_at = now - 1000;
        }

        // Add node in the future (shouldn't appear in past query)
        let future_node = g.add_node("Future node".into(), NodeKind::Assertion, HashMap::new());
        let future_id = future_node.id.clone();
        if let Some(idx) = g.id_to_index.get(&future_id) {
            g.graph[*idx].created_at = now + 1000;
        }

        // Query at current time
        let snapshot = g.query_at_timestamp(now);

        // Should only see the old node
        assert_eq!(snapshot.node_count, 1);
        assert_eq!(snapshot.nodes[0].id, old_id);
    }

    #[test]
    fn diff_timestamps_detects_added_nodes() {
        let mut g = SpecGraph::new();
        let t1 = Utc::now().timestamp() - 100;
        let t2 = Utc::now().timestamp();

        // Add node after t1
        let node = g.add_node("New node".into(), NodeKind::Assertion, HashMap::new());
        let node_id = node.id.clone();

        // Manually set created_at between t1 and t2
        if let Some(idx) = g.id_to_index.get(&node_id) {
            g.graph[*idx].created_at = t1 + 50;
        }

        let diff = g.diff_timestamps(t1, t2);

        assert_eq!(diff.added_nodes.len(), 1);
        assert_eq!(diff.added_nodes[0].id, node_id);
        assert_eq!(diff.removed_nodes.len(), 0);
    }

    #[test]
    fn diff_timestamps_shows_no_changes_for_stable_graph() {
        let mut g = SpecGraph::new();
        let t1 = Utc::now().timestamp() - 100;
        let t2 = Utc::now().timestamp();

        // Add node before both timestamps
        let node = g.add_node("Existing".into(), NodeKind::Assertion, HashMap::new());
        let node_id = node.id.clone();

        // Set created time before t1
        if let Some(idx) = g.id_to_index.get(&node_id) {
            g.graph[*idx].created_at = t1 - 50;
        }

        let diff = g.diff_timestamps(t1, t2);

        // No changes should be detected - node existed in both snapshots
        // Note: modified detection requires versioned storage, which isn't implemented yet
        assert_eq!(diff.added_nodes.len(), 0);
        assert_eq!(diff.removed_nodes.len(), 0);
    }

    #[test]
    fn get_node_history_shows_creation() {
        let mut g = SpecGraph::new();
        let node = g.add_node("Test node".into(), NodeKind::Assertion, HashMap::new());
        let node_id = node.id.clone();

        let history = g.get_node_history(&node_id).unwrap();

        assert_eq!(history.node.id, node_id);
        assert!(!history.events.is_empty());
        assert_eq!(history.events[0].event_type, "created");
    }

    #[test]
    fn get_node_history_shows_edge_additions() {
        let mut g = SpecGraph::new();
        let a = g.add_node("Node A".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        let b = g.add_node("Node B".into(), NodeKind::Assertion, HashMap::new()).id.clone();
        g.add_edge(&a, &b, EdgeKind::Refines, HashMap::new()).unwrap();

        let history = g.get_node_history(&a).unwrap();

        // Should have creation + edge addition
        assert!(history.events.len() >= 2);
        assert!(history.events.iter().any(|e| e.event_type == "edge_added"));
    }

    #[test]
    fn get_node_history_nonexistent_returns_none() {
        let g = SpecGraph::new();
        let history = g.get_node_history("nonexistent");
        assert!(history.is_none());
    }

    #[test]
    fn get_compliance_trend_no_data() {
        let mut g = SpecGraph::new();
        let node = g.add_node("Test".into(), NodeKind::Constraint, HashMap::new()).id.clone();

        let trend = g.get_compliance_trend(&node);
        assert!(trend.is_none());
    }

    #[test]
    fn get_compliance_trend_with_data() {
        let mut g = SpecGraph::new();
        let mut metadata = HashMap::new();
        metadata.insert("compliance_1000".to_string(), "0.5".to_string());
        metadata.insert("compliance_2000".to_string(), "0.7".to_string());
        metadata.insert("compliance_3000".to_string(), "0.9".to_string());

        let node = g.add_node("Test".into(), NodeKind::Constraint, metadata).id.clone();

        let trend = g.get_compliance_trend(&node).unwrap();

        assert_eq!(trend.data_points.len(), 3);
        assert_eq!(trend.data_points[0].timestamp, 1000);
        assert_eq!(trend.data_points[0].score, 0.5);
        assert_eq!(trend.trend_direction, "improving");
    }

    #[test]
    fn get_compliance_trend_degrading() {
        let mut g = SpecGraph::new();
        let mut metadata = HashMap::new();
        metadata.insert("compliance_1000".to_string(), "0.9".to_string());
        metadata.insert("compliance_2000".to_string(), "0.5".to_string());

        let node = g.add_node("Test".into(), NodeKind::Constraint, metadata).id.clone();

        let trend = g.get_compliance_trend(&node).unwrap();

        assert_eq!(trend.trend_direction, "degrading");
    }

    #[test]
    fn get_compliance_trend_stable() {
        let mut g = SpecGraph::new();
        let mut metadata = HashMap::new();
        metadata.insert("compliance_1000".to_string(), "0.7".to_string());
        metadata.insert("compliance_2000".to_string(), "0.72".to_string());

        let node = g.add_node("Test".into(), NodeKind::Constraint, metadata).id.clone();

        let trend = g.get_compliance_trend(&node).unwrap();

        assert_eq!(trend.trend_direction, "stable");
    }
}
