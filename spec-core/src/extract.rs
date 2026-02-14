use crate::{NodeKind, SpecGraph};
use std::collections::HashMap;
use std::path::Path;

/// Specification inferred from source code analysis
#[derive(Debug, Clone)]
pub struct InferredSpecification {
    pub content: String,
    pub kind: NodeKind,
    pub confidence: f32,      // 0.0-1.0
    pub source_file: String,
    pub source_line: usize,
    pub formality_layer: u8,  // 0=natural, 1=structured, 2=formal, 3=executable
    pub metadata: HashMap<String, String>,
}

/// Result of ingesting inferred specifications into graph
#[derive(Debug)]
pub struct IngestionReport {
    pub nodes_created: usize,
    pub nodes_skipped: usize,
    pub edges_created: usize,
    pub suggestions: Vec<EdgeSuggestion>,
    pub contradictions_found: Vec<String>,
}

/// Suggested edge that needs human review
#[derive(Debug)]
pub struct EdgeSuggestion {
    pub source_id: String,
    pub target_id: String,
    pub kind: crate::EdgeKind,
    pub confidence: f32,
    pub explanation: String,
}

impl SpecGraph {
    /// Check if inferred spec has sufficient semantic quality
    fn is_high_quality_spec(spec: &InferredSpecification) -> bool {
        let content = &spec.content;

        // Skip low-quality test assertions that are just code artifacts
        // Examples: "Invariant: g.node_count(), 1", "Invariant: fetched.kind, NodeKind::Assertion"
        if content.starts_with("Invariant: ") {
            // Reject if it contains Rust syntax (it's code, not a spec)
            let rust_syntax_markers = [
                ".iter()", ".any(", ".contains(", ".len()", ".get(",
                "!(", "||", "&&", ">", "<", "==", "!=",
                ".is_empty()", ".starts_with(", ".ends_with(",
                "assert!", "panic!", "unwrap(", "expect(",
                "{}", "[]", "\"{}\"", "format!", "println!"
            ];
            let has_rust_syntax = rust_syntax_markers.iter()
                .any(|marker| content.contains(marker));

            if has_rust_syntax {
                return false;  // Rust code, not a specification
            }

            // Also check for semantic keywords (original filter)
            let semantic_keywords = [
                "must", "should", "shall", "require", "ensure", "verify", "validate",
                "detect", "identify", "check", "test verifies", "system", "user",
                "specification", "requirement", "constraint"
            ];

            let has_semantic_meaning = semantic_keywords.iter()
                .any(|kw| content.to_lowercase().contains(kw));

            if !has_semantic_meaning {
                // Low-quality test assertion - skip it
                return false;
            }
        }

        // Skip trivial scenario names that provide no information
        // Examples: "scenario {}", "coverage empty graph", "coverage no tests"
        if content == "scenario {}" || content.trim().is_empty() {
            return false;
        }

        // Skip test function names that are too short or lack strong semantic value
        // Examples: "coverage empty graph", "empty graph", "no tests", "user login"
        if spec.kind == NodeKind::Scenario || spec.metadata.get("extractor") == Some(&"function_name".to_string()) {
            // Check minimum length (at least 25 characters for descriptive spec)
            if content.len() < 25 {
                return false;
            }

            // Must have strong semantic keywords (not just "user" or "test")
            let strong_keywords = [
                "must", "should", "shall", "ensure", "verify", "validate",
                "detect", "identify", "check for", "when", "if",
                "specification", "requirement", "constraint", "correctly", "properly",
                "without", "with", "given", "then", "returns", "accepts"
            ];
            let has_strong_semantic = strong_keywords.iter()
                .any(|kw| content.to_lowercase().contains(kw));

            // Reject if no strong semantics OR if it's just a test name pattern
            let is_trivial_test_name = content.to_lowercase().starts_with("scenario: ") &&
                !has_strong_semantic;

            if !has_strong_semantic || is_trivial_test_name {
                return false;
            }
        }

        true
    }

    /// Ingest inferred specifications into the graph
    pub fn ingest(&mut self, specs: Vec<InferredSpecification>) -> IngestionReport {
        let mut report = IngestionReport {
            nodes_created: 0,
            nodes_skipped: 0,
            edges_created: 0,
            suggestions: Vec::new(),
            contradictions_found: Vec::new(),
        };

        // Create nodes for high-confidence inferences (with deduplication)
        let mut created_ids = Vec::new();
        for spec in specs {
            // Apply both confidence threshold and quality filter
            if spec.confidence >= 0.7 && Self::is_high_quality_spec(&spec) {
                // Check for duplicate before creating node
                if let Some(existing) = self.find_node_by_content(&spec.content, spec.kind) {
                    // Duplicate found - skip creation, but track for edge inference
                    created_ids.push(existing.id.clone());
                    report.nodes_skipped += 1;
                } else {
                    // New node - create it
                    let mut metadata = spec.metadata.clone();
                    metadata.insert("source_file".to_string(), spec.source_file.clone());
                    metadata.insert("source_line".to_string(), spec.source_line.to_string());
                    metadata.insert("confidence".to_string(), spec.confidence.to_string());
                    metadata.insert("inferred".to_string(), "true".to_string());

                    let node = self.add_node_with_layer(
                        spec.content,
                        spec.kind,
                        spec.formality_layer,
                        metadata,
                    );
                    created_ids.push(node.id.clone());
                    report.nodes_created += 1;
                }
            } else {
                report.nodes_skipped += 1;
            }
        }

        // Infer relationships between newly created nodes and existing nodes
        for node_id in &created_ids {
            let suggestions = self.infer_relationships_for_node(node_id);

            for suggestion in suggestions {
                if suggestion.confidence >= 0.8 {
                    // High confidence: auto-create edge
                    match self.add_edge(
                        &suggestion.source_id,
                        &suggestion.target_id,
                        suggestion.kind,
                        HashMap::new(),
                    ) {
                        Ok(_) => report.edges_created += 1,
                        Err(_) => {} // Ignore errors (node might not exist)
                    }
                } else if suggestion.confidence >= 0.5 {
                    // Medium confidence: suggest for human review
                    report.suggestions.push(suggestion);
                }
            }
        }

        // Detect contradictions among newly created nodes
        let contras = self.detect_contradictions();
        for contra in contras {
            if created_ids.contains(&contra.node_a.id) || created_ids.contains(&contra.node_b.id) {
                report.contradictions_found.push(format!(
                    "Inferred contradiction: {} vs {}",
                    contra.node_a.content, contra.node_b.content
                ));
            }
        }

        report
    }

    /// Add node with explicit formality layer
    pub fn add_node_with_layer(
        &mut self,
        content: String,
        kind: NodeKind,
        formality_layer: u8,
        metadata: HashMap<String, String>,
    ) -> crate::SpecNodeData {
        // Use existing add_node infrastructure
        let node = self.add_node(content, kind, metadata);
        let node_id = node.id.clone();

        // Update formality layer
        self.update_node_formality(&node_id, formality_layer);

        // Return updated node
        self.get_node(&node_id).unwrap().clone()
    }

    /// Infer relationships for all nodes in the graph
    pub fn infer_all_relationships(&mut self) -> IngestionReport {
        let mut report = IngestionReport {
            nodes_created: 0,
            nodes_skipped: 0,
            edges_created: 0,
            suggestions: Vec::new(),
            contradictions_found: Vec::new(),
        };

        // Get all node IDs
        let all_ids: Vec<String> = self.list_nodes(None).iter().map(|n| n.id.clone()).collect();

        // Infer relationships for each node
        for node_id in &all_ids {
            let suggestions = self.infer_relationships_for_node(node_id);

            for suggestion in suggestions {
                if suggestion.confidence >= 0.8 {
                    // High confidence: auto-create edge
                    match self.add_edge(
                        &suggestion.source_id,
                        &suggestion.target_id,
                        suggestion.kind,
                        HashMap::new(),
                    ) {
                        Ok(_) => report.edges_created += 1,
                        Err(_) => {} // Ignore errors (edge might already exist)
                    }
                } else if suggestion.confidence >= 0.5 {
                    // Medium confidence: suggest for human review
                    report.suggestions.push(suggestion);
                }
            }
        }

        report
    }

    /// Automatically infer and create relationships for a single newly-added node
    /// This enables automatic re-integration when specs are added manually
    pub fn auto_connect_node(&mut self, node_id: &str) -> IngestionReport {
        let mut report = IngestionReport {
            nodes_created: 0,
            nodes_skipped: 0,
            edges_created: 0,
            suggestions: Vec::new(),
            contradictions_found: Vec::new(),
        };

        // Infer relationships for the specified node
        let suggestions = self.infer_relationships_for_node(node_id);

        for suggestion in suggestions {
            if suggestion.confidence >= 0.8 {
                // High confidence: auto-create edge
                match self.add_edge(
                    &suggestion.source_id,
                    &suggestion.target_id,
                    suggestion.kind,
                    HashMap::new(),
                ) {
                    Ok(_) => report.edges_created += 1,
                    Err(_) => {} // Ignore errors (edge might already exist)
                }
            } else if suggestion.confidence >= 0.5 {
                // Medium confidence: suggest for human review
                report.suggestions.push(suggestion);
            }
        }

        report
    }

    /// Infer relationships with AI enhancement for cross-layer semantic matching (optimized)
    /// Only compares nodes across different formality layers to create Formalizes edges
    pub fn infer_cross_layer_relationships_with_ai(&mut self, min_confidence: f32) -> IngestionReport {
        let mut report = IngestionReport {
            nodes_created: 0,
            nodes_skipped: 0,
            edges_created: 0,
            suggestions: Vec::new(),
            contradictions_found: Vec::new(),
        };

        // Initialize AI engine
        let ai = crate::AISemantic::default();
        if !ai.is_available() {
            eprintln!("Warning: AI command not available");
            return report;
        }

        println!("Using AI-enhanced semantic matching for cross-layer relationships...");

        // Group nodes by formality layer
        let all_nodes = self.list_nodes(None);
        let mut layers: HashMap<u8, Vec<crate::SpecNodeData>> = HashMap::new();
        for node in all_nodes {
            layers.entry(node.formality_layer).or_default().push(node.clone());
        }

        let layer_keys: Vec<u8> = layers.keys().copied().collect();
        println!("  Found layers: {:?}", layer_keys);

        // Only compare across layers (source_layer < target_layer for Formalizes)
        let mut total_comparisons = 0;
        for source_layer in &layer_keys {
            for target_layer in &layer_keys {
                if source_layer >= target_layer {
                    continue; // Skip same-layer and reverse comparisons
                }

                let source_nodes = layers.get(source_layer).unwrap();
                let target_nodes = layers.get(target_layer).unwrap();
                let comparisons = source_nodes.len() * target_nodes.len();
                total_comparisons += comparisons;

                println!("  Comparing layer {} -> {} ({} × {} = {} pairs)",
                    source_layer, target_layer,
                    source_nodes.len(), target_nodes.len(), comparisons);

                for (i, source_node) in source_nodes.iter().enumerate() {
                    if i % 10 == 0 && i > 0 {
                        println!("    Progress: {}/{} layer {} nodes", i, source_nodes.len(), source_layer);
                    }

                    for target_node in target_nodes {
                        let similarity = self.calculate_semantic_similarity_with_ai(
                            &source_node.content,
                            source_node.formality_layer,
                            &target_node.content,
                            target_node.formality_layer,
                            &ai,
                        );

                        if similarity < 0.5 {
                            continue; // Not similar enough for Formalizes
                        }

                        // Create Formalizes edge suggestion
                        let confidence = similarity * 0.9;
                        let suggestion = EdgeSuggestion {
                            source_id: source_node.id.clone(),
                            target_id: target_node.id.clone(),
                            kind: crate::EdgeKind::Formalizes,
                            confidence,
                            explanation: format!(
                                "Same concept at different formality levels ({} -> {})",
                                source_layer, target_layer
                            ),
                        };

                        if confidence >= min_confidence {
                            match self.add_edge(
                                &suggestion.source_id,
                                &suggestion.target_id,
                                suggestion.kind,
                                HashMap::new(),
                            ) {
                                Ok(_) => report.edges_created += 1,
                                Err(_) => {} // Edge might already exist
                            }
                        } else if confidence >= 0.5 {
                            report.suggestions.push(suggestion);
                        }
                    }
                }
            }
        }

        let (cache_size, _) = ai.cache_stats();
        println!("  Total comparisons: {}", total_comparisons);
        println!("  AI cache size: {} entries", cache_size);
        println!("  Formalizes edges created: {}", report.edges_created);

        report
    }

    /// Infer relationships with AI enhancement for cross-layer semantic matching
    pub fn infer_all_relationships_with_ai(&mut self, min_confidence: f32) -> IngestionReport {
        let mut report = IngestionReport {
            nodes_created: 0,
            nodes_skipped: 0,
            edges_created: 0,
            suggestions: Vec::new(),
            contradictions_found: Vec::new(),
        };

        // Get all node IDs
        let all_ids: Vec<String> = self.list_nodes(None).iter().map(|n| n.id.clone()).collect();

        // Initialize AI engine
        let ai = crate::AISemantic::default();
        if !ai.is_available() {
            eprintln!("Warning: AI command not available, falling back to simple inference");
            return self.infer_all_relationships();
        }

        println!("Using AI-enhanced semantic matching for cross-layer relationships...");

        // Infer relationships for each node
        for (i, node_id) in all_ids.iter().enumerate() {
            if i % 50 == 0 {
                println!("  Progress: {}/{} nodes processed", i, all_ids.len());
            }

            let suggestions = self.infer_relationships_for_node_with_ai(node_id, &ai);

            for suggestion in suggestions {
                if suggestion.confidence >= min_confidence {
                    // High confidence: auto-create edge
                    match self.add_edge(
                        &suggestion.source_id,
                        &suggestion.target_id,
                        suggestion.kind,
                        HashMap::new(),
                    ) {
                        Ok(_) => report.edges_created += 1,
                        Err(_) => {} // Ignore errors (edge might already exist)
                    }
                } else if suggestion.confidence >= 0.5 {
                    // Medium confidence: suggest for human review
                    report.suggestions.push(suggestion);
                }
            }
        }

        let (cache_size, _) = ai.cache_stats();
        println!("  AI cache size: {} entries", cache_size);

        report
    }

    /// Infer relationships for a specific node with AI enhancement
    fn infer_relationships_for_node_with_ai(&self, node_id: &str, ai: &crate::AISemantic) -> Vec<EdgeSuggestion> {
        let mut suggestions = Vec::new();

        let source_node = match self.get_node(node_id) {
            Some(n) => n,
            None => return suggestions,
        };

        // Get all other nodes
        let all_nodes = self.list_nodes(None);

        for target_node in all_nodes {
            if target_node.id == node_id {
                continue; // Skip self
            }

            // Calculate AI-enhanced semantic similarity
            let similarity = self.calculate_semantic_similarity_with_ai(
                &source_node.content,
                source_node.formality_layer,
                &target_node.content,
                target_node.formality_layer,
                ai,
            );

            // Layer-aware threshold: cross-layer connections need lower threshold
            let threshold = if source_node.formality_layer != target_node.formality_layer {
                0.15  // Cross-layer: proto↔requirement, test↔requirement
            } else {
                0.3   // Same-layer: more strict to avoid noise
            };

            if similarity < threshold {
                continue; // Too dissimilar
            }

            // Infer edge kind and confidence based on multiple factors
            if let Some((edge_kind, confidence, explanation)) =
                self.infer_edge_kind(source_node, target_node, similarity)
            {
                suggestions.push(EdgeSuggestion {
                    source_id: node_id.to_string(),
                    target_id: target_node.id.clone(),
                    kind: edge_kind,
                    confidence,
                    explanation,
                });
            }
        }

        suggestions
    }

    /// Infer relationships for a specific node
    fn infer_relationships_for_node(&self, node_id: &str) -> Vec<EdgeSuggestion> {
        let mut suggestions = Vec::new();

        let source_node = match self.get_node(node_id) {
            Some(n) => n,
            None => return suggestions,
        };

        // Get all other nodes
        let all_nodes = self.list_nodes(None);

        for target_node in all_nodes {
            if target_node.id == node_id {
                continue; // Skip self
            }

            // Calculate semantic similarity
            let similarity = self.calculate_semantic_similarity(
                &source_node.content,
                &target_node.content,
            );

            // Layer-aware threshold: cross-layer connections need lower threshold
            // because proto/test specs are concise while requirements are detailed
            let threshold = if source_node.formality_layer != target_node.formality_layer {
                0.15  // Cross-layer: proto↔requirement, test↔requirement
            } else {
                0.3   // Same-layer: more strict to avoid noise
            };

            if similarity < threshold {
                continue; // Too dissimilar
            }

            // Infer edge kind and confidence based on multiple factors
            if let Some((edge_kind, confidence, explanation)) =
                self.infer_edge_kind(source_node, target_node, similarity)
            {
                suggestions.push(EdgeSuggestion {
                    source_id: node_id.to_string(),
                    target_id: target_node.id.clone(),
                    kind: edge_kind,
                    confidence,
                    explanation,
                });
            }
        }

        suggestions
    }

    /// Calculate semantic similarity between two texts (optionally AI-enhanced)
    fn calculate_semantic_similarity(&self, text1: &str, text2: &str) -> f32 {
        // Start with simple keyword-based similarity
        let lower1 = text1.to_lowercase();
        let lower2 = text2.to_lowercase();

        let words1: std::collections::HashSet<String> =
            lower1.split_whitespace().map(|s| s.to_string()).collect();
        let words2: std::collections::HashSet<String> =
            lower2.split_whitespace().map(|s| s.to_string()).collect();

        if words1.is_empty() || words2.is_empty() {
            return 0.0;
        }

        let intersection = words1.intersection(&words2).count();
        let union = words1.union(&words2).count();

        intersection as f32 / union as f32
    }

    /// Calculate semantic similarity with AI enhancement for cross-layer comparisons
    fn calculate_semantic_similarity_with_ai(
        &self,
        text1: &str,
        layer1: u8,
        text2: &str,
        layer2: u8,
        ai: &crate::AISemantic,
    ) -> f32 {
        // First try simple similarity
        let simple_sim = self.calculate_semantic_similarity(text1, text2);

        // For cross-layer comparisons, ALWAYS use AI if available
        // Keyword overlap is meaningless across layers (U0 uses natural language, U2/U3 use technical terms)
        // Example: U0 "system must detect contradictions" ↔ U2 "RPC: DetectContradictions" (overlap ~0.1, semantic ~0.9)
        if layer1 != layer2 {
            if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
                // Trust AI heavily for cross-layer matching
                // Keyword overlap is noise, semantic equivalence is signal
                return simple_sim * 0.2 + ai_sim * 0.8;
            }
            // AI unavailable: fall back to simple similarity (will miss many connections)
            return simple_sim;
        }

        // Same-layer comparisons: use original conservative logic
        // If similarity is very high (>0.8), trust keyword matching
        if simple_sim > 0.8 {
            return simple_sim;
        }

        // For moderate similarity (0.4-0.8), use AI to disambiguate
        // This catches same-layer duplicates that keyword matching misses
        if simple_sim >= 0.4 {
            if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
                // Blend simple and AI similarity (weighted average)
                // Give more weight to AI for disambiguation
                return simple_sim * 0.3 + ai_sim * 0.7;
            }
        }

        // For very low similarity (<0.4) in same layer, skip AI (too expensive, low probability)
        simple_sim
    }

    /// Infer edge kind between two nodes
    fn infer_edge_kind(
        &self,
        source: &crate::SpecNodeData,
        target: &crate::SpecNodeData,
        similarity: f32,
    ) -> Option<(crate::EdgeKind, f32, String)> {
        // Rule 1: Synonym - very high similarity, same kind
        // Check this FIRST because it's most specific (highest threshold)
        if similarity > 0.8 && source.kind == target.kind {
            return Some((
                crate::EdgeKind::Synonym,
                similarity * 0.95,
                "Nearly identical content".to_string(),
            ));
        }

        // Rule 2: Formalizes - same concept, different formality levels
        if similarity > 0.5 && source.formality_layer < target.formality_layer {
            return Some((
                crate::EdgeKind::Formalizes,
                similarity * 0.9,
                format!(
                    "Same concept at different formality levels ({} -> {})",
                    source.formality_layer, target.formality_layer
                ),
            ));
        }

        // Rule 3: DerivesFrom - assertion derives from constraint
        if similarity > 0.5
            && source.kind == NodeKind::Assertion
            && target.kind == NodeKind::Constraint
        {
            return Some((
                crate::EdgeKind::DerivesFrom,
                similarity * 0.8,
                "Assertion derives from constraint".to_string(),
            ));
        }

        // Rule 4: Refines - scenario refines constraint, or same kind with high similarity
        if similarity > 0.6 {
            if source.kind == NodeKind::Scenario && target.kind == NodeKind::Constraint {
                return Some((
                    crate::EdgeKind::Refines,
                    similarity * 0.85,
                    "Scenario refines constraint".to_string(),
                ));
            }
            if source.kind == target.kind {
                return Some((
                    crate::EdgeKind::Refines,
                    similarity * 0.9,
                    "Similar specifications (potential refinement)".to_string(),
                ));
            }
        }

        // Rule 5: Same source file suggests relationship
        if let (Some(src_file), Some(tgt_file)) = (
            source.metadata.get("source_file"),
            target.metadata.get("source_file"),
        ) {
            if src_file == tgt_file && similarity > 0.4 {
                return Some((
                    crate::EdgeKind::Refines,
                    similarity * 0.7,
                    "Same source file".to_string(),
                ));
            }
        }

        None
    }
}

/// Extract specifications from Rust source code
pub struct RustExtractor;

impl RustExtractor {
    /// Extract specifications from Rust file
    pub fn extract(file_path: &Path) -> Result<Vec<InferredSpecification>, String> {
        let content = std::fs::read_to_string(file_path)
            .map_err(|e| format!("Failed to read file: {}", e))?;

        let mut specs = Vec::new();

        // Extract from function names (conventions like validate_*, check_*, require_*)
        specs.extend(Self::extract_from_function_names(&content, file_path)?);

        // Extract from assertions (assert!, assert_eq!, debug_assert!)
        specs.extend(Self::extract_from_assertions(&content, file_path)?);

        // Extract from test functions
        specs.extend(Self::extract_from_tests(&content, file_path)?);

        // Extract from doc comments
        specs.extend(Self::extract_from_docs(&content, file_path)?);

        // Extract from panic messages
        specs.extend(Self::extract_from_panics(&content, file_path)?);

        Ok(specs)
    }

    fn extract_from_function_names(
        content: &str,
        file_path: &Path,
    ) -> Result<Vec<InferredSpecification>, String> {
        let mut specs = Vec::new();
        let file_name = file_path.to_string_lossy().to_string();

        for (line_num, line) in content.lines().enumerate() {
            // Match function definitions
            if let Some(fn_name) = Self::extract_fn_name(line) {
                // Convention-based inference
                let (kind, confidence, description) = if fn_name.starts_with("validate_") {
                    (NodeKind::Constraint, 0.8, format!("Must {}", fn_name.strip_prefix("validate_").unwrap().replace('_', " ")))
                } else if fn_name.starts_with("check_") {
                    (NodeKind::Constraint, 0.75, format!("Must {}", fn_name.strip_prefix("check_").unwrap().replace('_', " ")))
                } else if fn_name.starts_with("require_") {
                    (NodeKind::Constraint, 0.85, format!("Requires {}", fn_name.strip_prefix("require_").unwrap().replace('_', " ")))
                } else if fn_name.starts_with("test_") {
                    (NodeKind::Scenario, 0.9, fn_name.strip_prefix("test_").unwrap().replace('_', " "))
                } else {
                    continue;
                };

                specs.push(InferredSpecification {
                    content: description,
                    kind,
                    confidence,
                    source_file: file_name.clone(),
                    source_line: line_num + 1,
                    formality_layer: 1, // Structured (from naming convention)
                    metadata: HashMap::from([
                        ("function".to_string(), fn_name.to_string()),
                        ("extractor".to_string(), "function_name".to_string()),
                    ]),
                });
            }
        }

        Ok(specs)
    }

    fn extract_from_assertions(
        content: &str,
        file_path: &Path,
    ) -> Result<Vec<InferredSpecification>, String> {
        let mut specs = Vec::new();
        let file_name = file_path.to_string_lossy().to_string();

        for (line_num, line) in content.lines().enumerate() {
            // Match assert!, assert_eq!, debug_assert!, etc.
            if let Some(assertion) = Self::extract_assertion(line) {
                specs.push(InferredSpecification {
                    content: format!("Invariant: {}", assertion),
                    kind: NodeKind::Constraint,
                    confidence: 0.95, // Assertions are high-confidence constraints
                    source_file: file_name.clone(),
                    source_line: line_num + 1,
                    formality_layer: 3, // Executable (actual code)
                    metadata: HashMap::from([
                        ("assertion".to_string(), assertion.clone()),
                        ("extractor".to_string(), "assertion".to_string()),
                    ]),
                });
            }
        }

        Ok(specs)
    }

    fn extract_from_tests(
        content: &str,
        file_path: &Path,
    ) -> Result<Vec<InferredSpecification>, String> {
        let mut specs = Vec::new();
        let file_name = file_path.to_string_lossy().to_string();

        let mut in_test = false;
        let mut test_name = String::new();
        let mut test_body = String::new();
        let mut test_start_line = 0;

        for (line_num, line) in content.lines().enumerate() {
            let trimmed = line.trim();

            // Detect #[test] or #[cfg(test)]
            if trimmed.starts_with("#[test]") || trimmed.contains("#[test]") {
                in_test = true;
                test_start_line = line_num + 1;
                test_body.clear();
            } else if in_test && trimmed.starts_with("fn ") {
                if let Some(name) = Self::extract_fn_name(trimmed) {
                    test_name = name.to_string();
                }
            } else if in_test && !test_name.is_empty() {
                // Collect test body for AI analysis
                test_body.push_str(line);
                test_body.push('\n');

                if trimmed == "}" {
                    // End of test function

                    // Extract U3 test scenario (the test itself)
                    let scenario_name = test_name.strip_prefix("test_").unwrap_or(&test_name).replace('_', " ");
                    specs.push(InferredSpecification {
                        content: format!("Scenario: {}", scenario_name),
                        kind: NodeKind::Scenario,
                        confidence: 0.9,
                        source_file: file_name.clone(),
                        source_line: test_start_line,
                        formality_layer: 3, // U3 - Executable test
                        metadata: HashMap::from([
                            ("test_function".to_string(), test_name.clone()),
                            ("extractor".to_string(), "test".to_string()),
                        ]),
                    });

                    // Extract U0 requirement via AI (reverse mapping f₀₃⁻¹: U3 → U0)
                    if let Some(u0_spec) = Self::extract_intent_from_test_with_ai(&test_name, &test_body) {
                        specs.push(InferredSpecification {
                            content: u0_spec,
                            kind: NodeKind::Constraint, // Root requirements are constraints
                            confidence: 0.95, // AI-extracted intent is high confidence
                            source_file: file_name.clone(),
                            source_line: test_start_line,
                            formality_layer: 0, // U0 - root specification inferred from U3
                            metadata: HashMap::from([
                                ("test_function".to_string(), test_name.clone()),
                                ("extractor".to_string(), "ai_intent".to_string()),
                                ("reverse_mapping".to_string(), "f_03_inverse".to_string()),
                                ("derived_from_u3".to_string(), "true".to_string()),
                            ]),
                        });
                    }

                    in_test = false;
                    test_name.clear();
                    test_body.clear();
                }
            }
        }

        Ok(specs)
    }

    /// Extract the INTENT behind a test using AI (reverse mapping f₀₃⁻¹: U3 → U0)
    ///
    /// This is the core of the reverse mapping engine. Instead of just pattern-matching
    /// test names, we use AI to understand what requirement the test is verifying.
    fn extract_intent_from_test_with_ai(test_name: &str, test_body: &str) -> Option<String> {
        use std::process::{Command, Stdio};

        // Check if claude CLI is available
        let available = Command::new("claude")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok();

        if !available {
            // Fallback to simple name-based extraction if AI unavailable
            return None;
        }

        let prompt = format!(
            r#"You are analyzing a test function to extract the root specification (U0) it verifies.

Test name: {}
Test code:
{}

Task: Extract the fundamental REQUIREMENT or CONSTRAINT that this test is verifying.
Output ONLY a single sentence specification in natural language, starting with "The system must..." or "System must..." or similar.

Focus on:
- What requirement is being tested? (not how it's tested)
- What constraint must the system satisfy?
- What capability must the system provide?

Output format: Single sentence, no explanation, no code, just the requirement.
Example output: "The system must detect contradictions when password length requirements conflict"
"#,
            test_name, test_body
        );

        let output = Command::new("claude")
            .arg("-p")
            .arg(&prompt)
            .output()
            .ok()?;

        if !output.status.success() {
            return None;
        }

        let response = String::from_utf8(output.stdout).ok()?;
        let spec = response.trim();

        // Validate that we got a reasonable specification
        if spec.is_empty() || spec.len() < 20 || spec.len() > 500 {
            return None;
        }

        // Check that it's a specification (contains requirement keywords)
        let requirement_keywords = ["must", "shall", "should", "system", "require"];
        let has_requirement = requirement_keywords.iter()
            .any(|kw| spec.to_lowercase().contains(kw));

        if !has_requirement {
            return None;
        }

        Some(spec.to_string())
    }

    fn extract_from_docs(
        content: &str,
        file_path: &Path,
    ) -> Result<Vec<InferredSpecification>, String> {
        let mut specs = Vec::new();
        let file_name = file_path.to_string_lossy().to_string();

        for (line_num, line) in content.lines().enumerate() {
            let trimmed = line.trim();

            // Match /// or //! doc comments
            if let Some(doc) = trimmed.strip_prefix("///").or_else(|| trimmed.strip_prefix("//!")) {
                let doc_text = doc.trim();

                // Look for specification keywords
                let (kind, confidence) = if doc_text.contains("must") || doc_text.contains("shall") || doc_text.contains("required") {
                    (NodeKind::Constraint, 0.8)
                } else if doc_text.contains("should") || doc_text.contains("expected") {
                    (NodeKind::Assertion, 0.7)
                } else if doc_text.contains("example") || doc_text.contains("scenario") {
                    (NodeKind::Scenario, 0.6)
                } else {
                    continue; // Not a specification
                };

                if !doc_text.is_empty() {
                    specs.push(InferredSpecification {
                        content: doc_text.to_string(),
                        kind,
                        confidence,
                        source_file: file_name.clone(),
                        source_line: line_num + 1,
                        formality_layer: 0, // Natural language
                        metadata: HashMap::from([
                            ("doc_comment".to_string(), "true".to_string()),
                            ("extractor".to_string(), "doc".to_string()),
                        ]),
                    });
                }
            }
        }

        Ok(specs)
    }

    fn extract_from_panics(
        content: &str,
        file_path: &Path,
    ) -> Result<Vec<InferredSpecification>, String> {
        let mut specs = Vec::new();
        let file_name = file_path.to_string_lossy().to_string();

        for (line_num, line) in content.lines().enumerate() {
            // Match panic! with message
            if let Some(panic_msg) = Self::extract_panic_message(line) {
                specs.push(InferredSpecification {
                    content: format!("Violation: {}", panic_msg),
                    kind: NodeKind::Constraint,
                    confidence: 0.85,
                    source_file: file_name.clone(),
                    source_line: line_num + 1,
                    formality_layer: 3, // Executable
                    metadata: HashMap::from([
                        ("panic".to_string(), panic_msg.clone()),
                        ("extractor".to_string(), "panic".to_string()),
                    ]),
                });
            }
        }

        Ok(specs)
    }

    // Helper parsers

    fn extract_fn_name(line: &str) -> Option<String> {
        let trimmed = line.trim();
        if trimmed.starts_with("fn ") || trimmed.starts_with("pub fn ") {
            let after_fn = trimmed.split("fn ").nth(1)?;
            let name = after_fn.split('(').next()?.trim();
            Some(name.to_string())
        } else {
            None
        }
    }

    fn extract_assertion(line: &str) -> Option<String> {
        let trimmed = line.trim();

        // Match assert!(...), assert_eq!(...), etc.
        for macro_name in &["assert!", "assert_eq!", "assert_ne!", "debug_assert!"] {
            if let Some(idx) = trimmed.find(macro_name) {
                let after_macro = &trimmed[idx + macro_name.len()..];
                if let Some(start) = after_macro.find('(') {
                    if let Some(end) = after_macro.rfind(')') {
                        let assertion = &after_macro[start + 1..end];
                        return Some(assertion.trim().to_string());
                    }
                }
            }
        }

        None
    }

    fn extract_panic_message(line: &str) -> Option<String> {
        let trimmed = line.trim();

        if let Some(idx) = trimmed.find("panic!(") {
            let after_panic = &trimmed[idx + 7..];
            if let Some(start) = after_panic.find('"') {
                if let Some(end) = after_panic[start + 1..].find('"') {
                    let message = &after_panic[start + 1..start + 1 + end];
                    return Some(message.to_string());
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn extract_from_rust_file() {
        let temp = TempDir::new().unwrap();
        let file_path = temp.path().join("test.rs");

        fs::write(
            &file_path,
            r#"
/// User must be authenticated
fn validate_user_authentication(user: &User) -> bool {
    assert!(user.is_authenticated());
    user.auth_token.is_some()
}

#[test]
fn test_authentication_required() {
    let user = User::new();
    assert!(!validate_user_authentication(&user));
}

fn process_payment(amount: u64) {
    if amount == 0 {
        panic!("Amount must be greater than zero");
    }
}
"#,
        )
        .unwrap();

        let specs = RustExtractor::extract(&file_path).unwrap();

        assert!(specs.len() >= 4, "Should extract multiple specifications");

        // Check for function name extraction
        assert!(
            specs.iter().any(|s| s.content.contains("user authentication")),
            "Should extract from function name"
        );

        // Check for assertion extraction
        assert!(
            specs.iter().any(|s| s.content.contains("Invariant")),
            "Should extract assertions"
        );

        // Check for test extraction
        assert!(
            specs.iter().any(|s| s.kind == NodeKind::Scenario),
            "Should extract test scenarios"
        );

        // Check for panic extraction
        assert!(
            specs.iter().any(|s| s.content.contains("greater than zero")),
            "Should extract panic messages"
        );

        // Check formality layers
        let executable = specs.iter().filter(|s| s.formality_layer == 3).count();
        assert!(executable > 0, "Should have executable specifications");

        let natural = specs.iter().filter(|s| s.formality_layer == 0).count();
        assert!(natural > 0, "Should have natural language specifications");
    }

    #[test]
    fn ingest_inferred_specs() {
        let mut graph = SpecGraph::new();

        let specs = vec![
            InferredSpecification {
                content: "User must be authenticated".to_string(),
                kind: NodeKind::Constraint,
                confidence: 0.9,
                source_file: "auth.rs".to_string(),
                source_line: 42,
                formality_layer: 0,
                metadata: HashMap::new(),
            },
            InferredSpecification {
                content: "Password length >= 8".to_string(),
                kind: NodeKind::Constraint,
                confidence: 0.95,
                source_file: "auth.rs".to_string(),
                source_line: 55,
                formality_layer: 3,
                metadata: HashMap::new(),
            },
            InferredSpecification {
                content: "Low confidence spec".to_string(),
                kind: NodeKind::Assertion,
                confidence: 0.5, // Below threshold
                source_file: "test.rs".to_string(),
                source_line: 10,
                formality_layer: 0,
                metadata: HashMap::new(),
            },
        ];

        let report = graph.ingest(specs);

        assert_eq!(report.nodes_created, 2, "Should create 2 high-confidence nodes");
        assert_eq!(report.nodes_skipped, 1, "Should skip 1 low-confidence node");

        let nodes = graph.list_nodes(None);
        assert_eq!(nodes.len(), 2);

        // Verify metadata is preserved
        let auth_node = nodes.iter().find(|n| n.content.contains("authenticated")).unwrap();
        assert_eq!(auth_node.metadata.get("source_file").unwrap(), "auth.rs");
        assert_eq!(auth_node.metadata.get("inferred").unwrap(), "true");
    }
}

/// Extract U2 specifications from Protocol Buffer (.proto) files
pub struct ProtoExtractor;

impl ProtoExtractor {
    /// Extract RPC interface specifications from proto file
    pub fn extract(file_path: &Path) -> Result<Vec<InferredSpecification>, String> {
        let content = std::fs::read_to_string(file_path)
            .map_err(|e| format!("Failed to read file: {}", e))?;

        let mut specs = Vec::new();
        let file_name = file_path.to_string_lossy().to_string();

        // Extract RPC definitions
        let mut current_comment = String::new();
        for (line_num, line) in content.lines().enumerate() {
            let trimmed = line.trim();

            // Capture comment lines
            if trimmed.starts_with("//") {
                let comment = trimmed.trim_start_matches("//").trim();
                if !comment.is_empty() {
                    current_comment = comment.to_string();
                }
                continue;
            }

            // Match RPC definitions: "rpc MethodName(RequestType) returns (ResponseType);"
            if trimmed.starts_with("rpc ") {
                if let Some(rpc_name) = Self::extract_rpc_name(trimmed) {
                    let description = if !current_comment.is_empty() {
                        current_comment.clone()
                    } else {
                        // Generate description from RPC name
                        Self::rpc_name_to_description(&rpc_name)
                    };

                    specs.push(InferredSpecification {
                        content: description,
                        kind: NodeKind::Assertion, // RPC interface is an assertion about behavior
                        confidence: 0.95, // High confidence - explicitly defined interface
                        source_file: file_name.clone(),
                        source_line: line_num + 1,
                        formality_layer: 2, // U2: Interface/API specification
                        metadata: HashMap::from([
                            ("rpc_name".to_string(), rpc_name.clone()),
                            ("extractor".to_string(), "proto_rpc".to_string()),
                        ]),
                    });

                    current_comment.clear();
                }
            }
        }

        Ok(specs)
    }

    fn extract_rpc_name(line: &str) -> Option<String> {
        // Parse "rpc MethodName(Request) returns (Response);"
        let after_rpc = line.strip_prefix("rpc ")?.trim();
        let name = after_rpc.split('(').next()?.trim();
        Some(name.to_string())
    }

    fn rpc_name_to_description(rpc_name: &str) -> String {
        // Convert camelCase/PascalCase to sentence
        // AddNode -> "RPC: Add node"
        // DetectContradictions -> "RPC: Detect contradictions"
        let mut result = String::new();
        let mut prev_was_lower = false;

        for (i, ch) in rpc_name.chars().enumerate() {
            if ch.is_uppercase() && prev_was_lower {
                result.push(' ');
                result.push(ch.to_lowercase().next().unwrap());
            } else if i == 0 {
                // First character stays as-is
                result.push(ch);
            } else {
                result.push(ch.to_lowercase().next().unwrap());
            }
            prev_was_lower = ch.is_lowercase();
        }

        format!("RPC: {}", result)
    }
}

#[cfg(test)]
mod proto_extractor_tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_extract_rpc_definitions() {
        let proto_content = r#"
syntax = "proto3";

service TestService {
  // Add a new node to the graph
  rpc AddNode(AddNodeRequest) returns (AddNodeResponse);

  rpc GetNode(GetNodeRequest) returns (GetNodeResponse);

  // Detect contradictions between specifications
  rpc DetectContradictions(DetectContradictionsRequest) returns (DetectContradictionsResponse);
}
"#;

        let mut temp_file = NamedTempFile::new().unwrap();
        temp_file.write_all(proto_content.as_bytes()).unwrap();

        let specs = ProtoExtractor::extract(temp_file.path()).unwrap();

        assert_eq!(specs.len(), 3, "Should extract 3 RPC definitions");

        // Check first RPC with comment
        let add_node = &specs[0];
        assert_eq!(add_node.content, "Add a new node to the graph");
        assert_eq!(add_node.kind, NodeKind::Assertion);
        assert_eq!(add_node.formality_layer, 2);
        assert_eq!(add_node.metadata.get("rpc_name").unwrap(), "AddNode");
        assert_eq!(add_node.confidence, 0.95);

        // Check RPC without comment (generated description)
        let get_node = &specs[1];
        assert_eq!(get_node.content, "RPC: Get node");
        assert_eq!(get_node.metadata.get("rpc_name").unwrap(), "GetNode");

        // Check camelCase conversion
        let detect = &specs[2];
        assert_eq!(detect.content, "Detect contradictions between specifications");
        assert_eq!(detect.metadata.get("rpc_name").unwrap(), "DetectContradictions");
    }
}
