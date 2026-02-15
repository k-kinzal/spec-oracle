/// SpecRepository: Pure data persistence layer for specification graph
///
/// This module contains ALL pure data operations:
/// - CRUD on nodes and edges
/// - Graph traversal and queries
/// - Search and filtering
/// - Test coverage and compliance calculation
/// - Temporal queries (versioning, history, diff)
/// - Serialization (JSON, DOT)
///
/// ARCHITECTURAL CONSTRAINT:
/// NO imports from crate::formal:: module allowed here.
/// This is pure data layer - formal verification belongs in UDAFModel.
use chrono::Utc;
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

use super::*; // Import data module types

/// Pure data repository for specification graph
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecRepository {
    graph: DiGraph<SpecNodeData, SpecEdgeData>,
    #[serde(skip)]
    id_to_index: HashMap<String, NodeIndex>,
    #[serde(skip)]
    edge_id_to_index: HashMap<String, EdgeIndex>,
}

impl Default for SpecRepository {
    fn default() -> Self {
        Self::new()
    }
}

impl SpecRepository {
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

    // ========================================================================
    // Node operations
    // ========================================================================

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
            formality_layer: 0, // Default to natural language
        };
        let idx = self.graph.add_node(data);
        self.id_to_index.insert(id, idx);
        &self.graph[idx]
    }

    /// Add a node from loaded data (preserves existing ID and timestamps)
    pub fn add_node_from_loaded(&mut self, node: SpecNodeData) -> String {
        let id = node.id.clone();
        let idx = self.graph.add_node(node);
        self.id_to_index.insert(id.clone(), idx);
        id
    }

    pub fn get_node(&self, id: &str) -> Option<&SpecNodeData> {
        self.id_to_index.get(id).map(|&idx| &self.graph[idx])
    }

    /// Find a node by content and kind (for deduplication)
    pub fn find_node_by_content(&self, content: &str, kind: NodeKind) -> Option<&SpecNodeData> {
        self.graph
            .node_weights()
            .find(|n| n.content == content && n.kind == kind)
    }

    pub fn update_node_formality(&mut self, id: &str, formality_layer: u8) -> bool {
        if let Some(&idx) = self.id_to_index.get(id)
            && let Some(node) = self.graph.node_weight_mut(idx) {
                node.formality_layer = formality_layer;
                node.modified_at = Utc::now().timestamp();
                return true;
            }
        false
    }

    pub fn update_node_metadata(
        &mut self,
        id: &str,
        key: String,
        value: String,
    ) -> Option<SpecNodeData> {
        if let Some(&idx) = self.id_to_index.get(id)
            && let Some(node) = self.graph.node_weight_mut(idx) {
                node.metadata.insert(key, value);
                node.modified_at = Utc::now().timestamp();
                return Some(node.clone());
            }
        None
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

    // ========================================================================
    // Edge operations
    // ========================================================================

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

    /// Add an edge from loaded data (preserves existing ID and timestamps)
    pub fn add_edge_from_loaded(&mut self, edge: Edge) -> Result<String, GraphError> {
        let &src_idx = self
            .id_to_index
            .get(&edge.source)
            .ok_or_else(|| GraphError::NodeNotFound(edge.source.clone()))?;
        let &tgt_idx = self
            .id_to_index
            .get(&edge.target)
            .ok_or_else(|| GraphError::NodeNotFound(edge.target.clone()))?;

        let id = edge.data.id.clone();
        let eidx = self.graph.add_edge(src_idx, tgt_idx, edge.data);
        self.edge_id_to_index.insert(id.clone(), eidx);
        Ok(id)
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
                if let Some(nid) = node_id
                    && src_data.id != nid && tgt_data.id != nid {
                        return None;
                    }
                Some((edge_data, src_data.id.as_str(), tgt_data.id.as_str()))
            })
            .collect()
    }

    pub fn find_edge(
        &self,
        source_id: &str,
        target_id: &str,
        kind: Option<EdgeKind>,
    ) -> Option<&SpecEdgeData> {
        let src_idx = self.id_to_index.get(source_id)?;
        let tgt_idx = self.id_to_index.get(target_id)?;

        self.graph
            .edges_connecting(*src_idx, *tgt_idx)
            .find(|e| kind.is_none() || Some(self.graph[e.id()].kind) == kind)
            .map(|e| &self.graph[e.id()])
    }

    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// Iterator over all nodes (for serialization)
    pub fn nodes(&self) -> impl Iterator<Item = &SpecNodeData> {
        self.graph.node_weights()
    }

    /// Iterator over all edges with source/target IDs (for serialization)
    pub fn edges(&self) -> impl Iterator<Item = Edge> + '_ {
        self.graph.edge_indices().filter_map(move |eidx| {
            let (src_idx, tgt_idx) = self.graph.edge_endpoints(eidx)?;
            let edge_data = self.graph[eidx].clone();
            let source = self.graph[src_idx].id.clone();
            let target = self.graph[tgt_idx].id.clone();
            Some(Edge {
                source,
                target,
                data: edge_data,
            })
        })
    }

    // ========================================================================
    // Search and filtering
    // ========================================================================

    /// Search nodes by content substring (case-insensitive).
    pub fn search(&self, query: &str) -> Vec<&SpecNodeData> {
        let q = query.to_lowercase();
        self.graph
            .node_weights()
            .filter(|n| n.content.to_lowercase().contains(&q))
            .collect()
    }

    /// Filter nodes by formality layer.
    pub fn filter_by_layer(&self, min_layer: u8, max_layer: u8) -> Vec<&SpecNodeData> {
        self.graph
            .node_weights()
            .filter(|n| n.formality_layer >= min_layer && n.formality_layer <= max_layer)
            .collect()
    }

    // ========================================================================
    // Relationship traversal
    // ========================================================================

    /// Trace all relationships for a node, returning a hierarchical structure.
    /// Returns tuples of (node, edge_kind, direction) where direction is "outgoing" or "incoming".
    pub fn trace_relationships(
        &self,
        node_id: &str,
        max_depth: usize,
    ) -> Vec<(SpecNodeData, EdgeKind, String, usize)> {
        let mut result = Vec::new();
        let mut visited = std::collections::HashSet::new();

        if let Some(&start_idx) = self.id_to_index.get(node_id) {
            visited.insert(start_idx);
            self.trace_recursive(start_idx, max_depth, 0, &mut visited, &mut result);
        }

        result
    }

    fn trace_recursive(
        &self,
        idx: NodeIndex,
        max_depth: usize,
        current_depth: usize,
        visited: &mut std::collections::HashSet<NodeIndex>,
        result: &mut Vec<(SpecNodeData, EdgeKind, String, usize)>,
    ) {
        if max_depth > 0 && current_depth >= max_depth {
            return;
        }

        // Traverse outgoing edges
        for edge in self.graph.edges_directed(idx, Direction::Outgoing) {
            let target_idx = edge.target();
            let edge_data = &self.graph[edge.id()];
            let target_node = &self.graph[target_idx];

            result.push((
                target_node.clone(),
                edge_data.kind,
                "outgoing".to_string(),
                current_depth + 1,
            ));

            if !visited.contains(&target_idx) {
                visited.insert(target_idx);
                self.trace_recursive(target_idx, max_depth, current_depth + 1, visited, result);
            }
        }

        // Traverse incoming edges
        for edge in self.graph.edges_directed(idx, Direction::Incoming) {
            let source_idx = edge.source();
            let edge_data = &self.graph[edge.id()];
            let source_node = &self.graph[source_idx];

            result.push((
                source_node.clone(),
                edge_data.kind,
                "incoming".to_string(),
                current_depth + 1,
            ));

            if !visited.contains(&source_idx) {
                visited.insert(source_idx);
                self.trace_recursive(source_idx, max_depth, current_depth + 1, visited, result);
            }
        }
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

    // ========================================================================
    // Terminology and synonym detection
    // ========================================================================

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
        let stop_words = [
            "the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for",
        ];
        let mut term_context: std::collections::HashSet<String> =
            std::collections::HashSet::new();

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
                let neighbors_a: std::collections::HashSet<NodeIndex> =
                    self.graph.neighbors_undirected(idx_a).collect();
                let neighbors_b: std::collections::HashSet<NodeIndex> =
                    self.graph.neighbors_undirected(idx_b).collect();

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

    // ========================================================================
    // Code generation
    // ========================================================================

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

    // ========================================================================
    // Test coverage and compliance
    // ========================================================================

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
            "the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for", "is", "are",
            "was", "were", "be", "been", "being", "have", "has", "had", "do", "does", "did",
            "will", "would", "should", "could", "may", "might", "must", "can", "of", "by",
            "with", "from", "as", "into", "through",
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
            && (code_lower.contains("assert")
                || code_lower.contains("require")
                || code_lower.contains("invariant"))
        {
            score += 0.3;
        }

        // Look for comparison operators
        if (spec_lower.contains('>')
            || spec_lower.contains('<')
            || spec_lower.contains("greater")
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
        let action_words = [
            "login", "create", "update", "delete", "send", "receive", "verify",
        ];
        let has_action = action_words
            .iter()
            .any(|&w| spec_lower.contains(w) && code_lower.contains(w));
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
        let has_verify = code_lower.contains("assert")
            || code_lower.contains("verify")
            || code_lower.contains("expect");

        if has_setup {
            score += 0.1;
        }
        if has_action_code {
            score += 0.15;
        }
        if has_verify {
            score += 0.15;
        }

        score.min(1.0)
    }

    /// Get compliance report for all specifications with linked code.
    pub fn get_compliance_report(&self) -> Vec<(SpecNodeData, ComplianceScore)> {
        self.graph
            .node_weights()
            .filter(|n| n.metadata.contains_key("impl_code") || n.metadata.contains_key("test_code"))
            .filter_map(|n| {
                let code = n
                    .metadata
                    .get("impl_code")
                    .or_else(|| n.metadata.get("test_code"))?;
                let score = self.calculate_compliance(&n.id, code)?;
                Some((n.clone(), score))
            })
            .collect()
    }

    // ========================================================================
    // Temporal operations
    // ========================================================================

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
    pub fn get_compliance_trends(&self, node_id: &str) -> Option<ComplianceTrend> {
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

    // ========================================================================
    // Serialization
    // ========================================================================

    /// Export the specification graph in DOT format (Graphviz).
    /// Nodes are colored by formality layer (U0=blue, U1=green, U2=yellow, U3=red).
    /// Edges are styled by kind (Refines, Formalizes, etc.).
    pub fn export_dot(&self) -> String {
        let mut dot = String::from("digraph spec_oracle {\n");
        dot.push_str("    rankdir=LR;\n");
        dot.push_str("    node [shape=box, style=filled];\n");
        dot.push_str("    edge [fontsize=10];\n\n");

        // Helper function to escape DOT strings
        fn escape_dot(s: &str) -> String {
            s.replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
        }

        // Helper function to truncate content
        fn truncate(s: &str, max_len: usize) -> String {
            if s.len() > max_len {
                format!("{}...", &s[..max_len])
            } else {
                s.to_string()
            }
        }

        // Helper function to get layer color
        fn layer_color(layer: u8) -> &'static str {
            match layer {
                0 => "lightblue",   // U0: natural language
                1 => "lightgreen",  // U1: structured/formal
                2 => "lightyellow", // U2: interface/API
                3 => "lightcoral",  // U3: implementation
                _ => "white",
            }
        }

        // Helper function to get layer label
        fn layer_label(layer: u8) -> &'static str {
            match layer {
                0 => "U0",
                1 => "U1",
                2 => "U2",
                3 => "U3",
                _ => "U?",
            }
        }

        // Helper function to get kind abbreviation
        fn kind_abbr(kind: NodeKind) -> &'static str {
            match kind {
                NodeKind::Assertion => "A",
                NodeKind::Constraint => "C",
                NodeKind::Scenario => "S",
                NodeKind::Definition => "D",
                NodeKind::Domain => "Dom",
            }
        }

        // Add nodes
        for node in self.graph.node_weights() {
            let layer = node.formality_layer;
            let color = layer_color(layer);
            let layer_lbl = layer_label(layer);
            let kind_lbl = kind_abbr(node.kind);
            let content_short = truncate(&node.content, 50);
            let label = format!("[{}] {} {}", layer_lbl, kind_lbl, content_short);

            dot.push_str(&format!(
                "    \"{}\" [label=\"{}\", fillcolor=\"{}\"];\n",
                escape_dot(&node.id),
                escape_dot(&label),
                color
            ));
        }

        dot.push('\n');

        // Add edges
        for edge_idx in self.graph.edge_indices() {
            if let Some((source_idx, target_idx)) = self.graph.edge_endpoints(edge_idx)
                && let Some(edge) = self.graph.edge_weight(edge_idx)
                    && let (Some(source_node), Some(target_node)) = (
                        self.graph.node_weight(source_idx),
                        self.graph.node_weight(target_idx),
                    ) {
                        let edge_style = match edge.kind {
                            EdgeKind::Refines => "solid",
                            EdgeKind::Formalizes => "bold",
                            EdgeKind::DerivesFrom => "dashed",
                            EdgeKind::Transform => "dotted",
                            EdgeKind::Contradicts => "bold, color=red",
                            EdgeKind::DependsOn => "dashed",
                            EdgeKind::Synonym => "dotted, color=gray",
                            EdgeKind::Composes => "solid",
                        };

                        let edge_label = format!("{:?}", edge.kind);

                        dot.push_str(&format!(
                            "    \"{}\" -> \"{}\" [label=\"{}\", style=\"{}\"];\n",
                            escape_dot(&source_node.id),
                            escape_dot(&target_node.id),
                            edge_label,
                            edge_style
                        ));
                    }
        }

        dot.push_str("}\n");
        dot
    }
}
