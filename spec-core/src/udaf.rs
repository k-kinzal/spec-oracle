/// U/D/A/f Model: Explicit implementation of the theoretical foundation of specORACLE
///
/// Based on conversation.md and motivation.md:
/// - U (Universe): The space in which specifications are defined
/// - D (Domain): The region that specifications actually cover
/// - A (Admissible set): The set of allowed implementations
/// - f (Transform function): Mappings between universes
///
/// Critical insight: U0 is NOT directly written by users.
/// U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ ... ∪ f₀ₙ⁻¹(UN)
///
/// Users write U1-UN (various specifications), and specORACLE constructs U0
/// from the inverse mappings of all layers.

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

/// Universe: The space in which specifications are defined
///
/// A universe represents a complete space of possible specifications at a
/// particular level of formality or abstraction.
///
/// - U0: Root specification (constructed from inverse mappings, not written directly)
/// - U1-UN: Projection universes (written by users, e.g., natural language, TLA+, code)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Universe {
    /// Unique identifier for this universe
    pub id: String,

    /// Layer index (0 for U0, 1-N for projection universes)
    pub layer: u8,

    /// Human-readable name (e.g., "Natural Language Requirements", "TLA+ Formal Spec", "Rust Implementation")
    pub name: String,

    /// Description of what this universe represents
    pub description: String,

    /// Specifications that belong to this universe
    pub specifications: HashSet<String>,  // Node IDs

    /// Metadata for extensibility
    pub metadata: HashMap<String, String>,
}

impl Universe {
    /// Create U0 (root universe) - constructed from inverse mappings
    pub fn root() -> Self {
        Self {
            id: "U0".to_string(),
            layer: 0,
            name: "Root Specification".to_string(),
            description: "The foundational universe constructed from inverse mappings of all projection universes. This represents the 'rough projection of the undefinable root specification'.".to_string(),
            specifications: HashSet::new(),
            metadata: HashMap::new(),
        }
    }

    /// Create a projection universe (U1-UN)
    pub fn projection(layer: u8, name: String, description: String) -> Self {
        assert!(layer > 0, "U0 is reserved for root universe");
        Self {
            id: format!("U{}", layer),
            layer,
            name,
            description,
            specifications: HashSet::new(),
            metadata: HashMap::new(),
        }
    }
}

/// Domain: The region that a specification actually covers
///
/// D represents "what this specification is about" - the subset of the universe
/// that the specification intends to govern.
///
/// Gap detection: D \ D_S (intended domain minus actually specified domain)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Domain {
    /// Unique identifier for this domain
    pub id: String,

    /// Human-readable name
    pub name: String,

    /// What this domain covers (natural language description)
    pub description: String,

    /// The universe this domain belongs to
    pub universe_id: String,

    /// Specifications that cover this domain
    pub covered_by: HashSet<String>,  // Node IDs

    /// Sub-domains (hierarchical structure)
    pub subdomains: Vec<String>,  // Domain IDs

    /// Metadata for extensibility
    pub metadata: HashMap<String, String>,
}

impl Domain {
    pub fn new(id: String, name: String, description: String, universe_id: String) -> Self {
        Self {
            id,
            name,
            description,
            universe_id,
            covered_by: HashSet::new(),
            subdomains: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    /// Check if this domain has any coverage gaps
    pub fn has_gaps(&self) -> bool {
        self.covered_by.is_empty()
    }
}

/// Admissible Set: The set of implementations allowed by a specification
///
/// A represents "what is correct" - all implementations that satisfy the specification.
/// Contradiction detection: A1 ∩ A2 = ∅ (disjoint admissible sets)
///
/// Note: This is a symbolic representation. The actual admissible set is infinite
/// and cannot be enumerated. Instead, we represent it through constraints.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdmissibleSet {
    /// The specification that defines this admissible set
    pub spec_id: String,

    /// The universe this admissible set belongs to
    pub universe_id: String,

    /// Constraints that define membership in this set
    /// (e.g., "password.len() >= 8", "response_time < 1s")
    pub constraints: Vec<Constraint>,

    /// Known contradictions with other admissible sets
    pub contradicts: HashSet<String>,  // Other AdmissibleSet IDs

    /// Metadata for extensibility
    pub metadata: HashMap<String, String>,
}

impl AdmissibleSet {
    pub fn new(spec_id: String, universe_id: String) -> Self {
        Self {
            spec_id,
            universe_id,
            constraints: Vec::new(),
            contradicts: HashSet::new(),
            metadata: HashMap::new(),
        }
    }

    /// Add a constraint to this admissible set
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Mark this admissible set as contradicting another
    pub fn mark_contradiction(&mut self, other_id: String) {
        self.contradicts.insert(other_id);
    }

    /// Check if this admissible set is likely empty (unsatisfiable constraints)
    pub fn is_likely_empty(&self) -> bool {
        // Heuristic: check for obvious contradictions in constraints
        // e.g., "x >= 10" and "x <= 5"
        // TODO: Implement SMT solver integration for precise satisfiability check
        false  // Placeholder
    }
}

/// Constraint: A symbolic representation of a membership condition
///
/// Represents a condition that an implementation must satisfy to be in the admissible set.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Constraint {
    /// Natural language description of the constraint
    pub description: String,

    /// Formal representation (e.g., SMT-LIB, propositional logic)
    /// None if not yet formalized
    pub formal: Option<String>,

    /// Type of constraint (universal ∀, existential ∃, etc.)
    pub kind: ConstraintKind,

    /// Metadata for extensibility
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstraintKind {
    /// Universal constraint (∀): Must hold for all cases
    Universal,

    /// Existential constraint (∃): Must hold for at least one case
    Existential,

    /// Implication (→): If condition then consequence
    Implication,

    /// Equivalence (↔): Bidirectional implication
    Equivalence,
}

/// Transform Function: Mappings between universes
///
/// f: Ui → Uj represents a transformation from one universe to another.
/// The most critical transforms are inverse mappings: f₀ᵢ⁻¹: Ui → U0
///
/// These are NOT just edge markers - they contain actual transformation logic.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransformFunction {
    /// Unique identifier for this transform
    pub id: String,

    /// Source universe
    pub source_universe: String,

    /// Target universe
    pub target_universe: String,

    /// Human-readable description of this transformation
    pub description: String,

    /// The type of transformation
    pub kind: TransformKind,

    /// The actual transformation logic (strategy pattern)
    /// This is where we'll plug in different transformation implementations
    pub strategy: TransformStrategy,

    /// Metadata for extensibility
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransformKind {
    /// Forward mapping: Ui → Uj (i < j, more concrete)
    Forward,

    /// Inverse mapping: Ui → U0 (critical for constructing root universe)
    Inverse,

    /// Parallel mapping: Ui → Uj (i, j > 0, different aspects)
    Parallel,
}

/// Strategy for performing transformations
///
/// Different transformation strategies based on the nature of the universes.
/// This is where the actual "how to transform" logic lives.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TransformStrategy {
    /// Abstract syntax tree analysis (for code → spec)
    ASTAnalysis {
        language: String,
        extractor_config: HashMap<String, String>,
    },

    /// Natural language inference (for docs → spec)
    NLPInference {
        model: String,
        prompt_template: String,
    },

    /// Formal verification (for TLA+/Alloy → spec)
    FormalVerification {
        tool: String,
        verification_config: HashMap<String, String>,
    },

    /// Type system analysis (for type definitions → spec)
    TypeAnalysis {
        type_system: String,
    },

    /// Manual mapping (user-defined transformation)
    Manual {
        description: String,
    },

    /// Composed transformation (chain multiple strategies)
    Composed {
        strategies: Vec<Box<TransformStrategy>>,
    },
}

impl TransformFunction {
    /// Create an inverse mapping: Ui → U0
    pub fn inverse(
        source_universe: String,
        description: String,
        strategy: TransformStrategy,
    ) -> Self {
        Self {
            id: format!("f_{}_to_U0", source_universe),
            source_universe: source_universe.clone(),
            target_universe: "U0".to_string(),
            description,
            kind: TransformKind::Inverse,
            strategy,
            metadata: HashMap::new(),
        }
    }

    /// Create a forward mapping: Ui → Uj
    pub fn forward(
        source_universe: String,
        target_universe: String,
        description: String,
        strategy: TransformStrategy,
    ) -> Self {
        Self {
            id: format!("f_{}_{}", source_universe, target_universe),
            source_universe,
            target_universe,
            description,
            kind: TransformKind::Forward,
            strategy,
            metadata: HashMap::new(),
        }
    }
}

/// UDAF Model: The complete multi-universe specification model
///
/// This is the core data structure that implements the theoretical foundation
/// of specORACLE as described in conversation.md and motivation.md.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UDAFModel {
    /// All universes in the model
    pub universes: HashMap<String, Universe>,

    /// All domains across all universes
    pub domains: HashMap<String, Domain>,

    /// All admissible sets (one per specification)
    pub admissible_sets: HashMap<String, AdmissibleSet>,

    /// All transform functions between universes
    pub transforms: HashMap<String, TransformFunction>,

    /// Metadata for extensibility
    pub metadata: HashMap<String, String>,
}

impl UDAFModel {
    pub fn new() -> Self {
        let mut model = Self {
            universes: HashMap::new(),
            domains: HashMap::new(),
            admissible_sets: HashMap::new(),
            transforms: HashMap::new(),
            metadata: HashMap::new(),
        };

        // Always create U0 (root universe)
        model.universes.insert("U0".to_string(), Universe::root());

        model
    }

    /// Add a projection universe (U1, U2, etc.)
    pub fn add_universe(&mut self, layer: u8, name: String, description: String) -> String {
        let universe = Universe::projection(layer, name, description);
        let id = universe.id.clone();
        self.universes.insert(id.clone(), universe);
        id
    }

    /// Add a domain to a universe
    pub fn add_domain(&mut self, domain: Domain) -> String {
        let id = domain.id.clone();
        self.domains.insert(id.clone(), domain);
        id
    }

    /// Add an admissible set for a specification
    pub fn add_admissible_set(&mut self, admissible_set: AdmissibleSet) -> String {
        let id = admissible_set.spec_id.clone();
        self.admissible_sets.insert(id.clone(), admissible_set);
        id
    }

    /// Add a transform function
    pub fn add_transform(&mut self, transform: TransformFunction) -> String {
        let id = transform.id.clone();
        self.transforms.insert(id.clone(), transform);
        id
    }

    /// Construct U0 from all projection universes via inverse mappings
    ///
    /// U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ ... ∪ f₀ₙ⁻¹(UN)
    ///
    /// This is the core operation that realizes the theoretical model.
    /// Returns the newly extracted InferredSpecification objects that should be ingested into the graph.
    pub fn construct_u0(&mut self, graph: &crate::SpecGraph) -> Result<Vec<crate::InferredSpecification>, String> {
        // Collect all newly extracted specifications from projection universes
        let mut newly_created_specs = Vec::new();

        // For each projection universe (U1, U2, U3...)
        for (universe_id, universe) in &self.universes {
            if universe.layer == 0 {
                continue;  // Skip U0 itself
            }

            // Find the inverse transform for this universe
            let inverse_transform_id = format!("f_{}_to_U0", universe_id);

            if let Some(transform) = self.transforms.get(&inverse_transform_id) {
                // Execute the transform strategy to extract/map specifications
                let extracted_specs = self.execute_transform(transform, graph)?;
                newly_created_specs.extend(extracted_specs);
            }
        }

        Ok(newly_created_specs)
    }

    /// Execute a transform strategy to extract specifications
    fn execute_transform(
        &self,
        transform: &TransformFunction,
        graph: &crate::SpecGraph,
    ) -> Result<Vec<crate::InferredSpecification>, String> {
        match &transform.strategy {
            TransformStrategy::ASTAnalysis { language, extractor_config } => {
                // Execute AST analysis for the specified language
                if language == "rust" {
                    self.execute_rust_ast_analysis(extractor_config, graph)
                } else {
                    Err(format!("Unsupported language: {}", language))
                }
            }
            TransformStrategy::Manual { description: _ } => {
                // Manual transforms don't auto-execute
                Ok(Vec::new())
            }
            _ => {
                // Other strategies not yet implemented
                Ok(Vec::new())
            }
        }
    }

    /// Execute Rust AST analysis to extract specifications from code
    fn execute_rust_ast_analysis(
        &self,
        config: &HashMap<String, String>,
        graph: &crate::SpecGraph,
    ) -> Result<Vec<crate::InferredSpecification>, String> {
        use crate::RustExtractor;
        use std::path::Path;

        // Get source files from config or find them in graph metadata
        let source_files = self.find_rust_source_files(config, graph)?;

        let mut extracted_specs = Vec::new();

        for file_path in source_files {
            let path = Path::new(&file_path);

            // Extract specifications using RustExtractor
            match RustExtractor::extract(path) {
                Ok(inferred_specs) => {
                    // Filter by confidence threshold from config
                    let min_confidence = config
                        .get("min_confidence")
                        .and_then(|s| s.parse::<f32>().ok())
                        .unwrap_or(0.7);

                    for spec in inferred_specs {
                        if spec.confidence >= min_confidence {
                            // Return the actual InferredSpecification objects
                            // These will be ingested into the graph
                            extracted_specs.push(spec);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Warning: Failed to extract from {}: {}", file_path, e);
                }
            }
        }

        Ok(extracted_specs)
    }

    /// Find Rust source files to analyze from config or graph metadata
    fn find_rust_source_files(
        &self,
        config: &HashMap<String, String>,
        graph: &crate::SpecGraph,
    ) -> Result<Vec<String>, String> {
        // If source_files specified in config, use those
        if let Some(files_str) = config.get("source_files") {
            return Ok(files_str.split(',').map(|s| s.trim().to_string()).collect());
        }

        // Otherwise, find source files from graph nodes with source_file metadata
        let mut source_files = HashSet::new();
        for node in graph.list_nodes(None) {
            if let Some(source_file) = node.metadata.get("source_file") {
                if source_file.ends_with(".rs") {
                    source_files.insert(source_file.clone());
                }
            }
        }

        if source_files.is_empty() {
            Err("No source files found in config or graph metadata".to_string())
        } else {
            Ok(source_files.into_iter().collect())
        }
    }

    /// Detect contradictions: A1 ∩ A2 = ∅
    ///
    /// Returns pairs of admissible sets that are mutually exclusive
    pub fn detect_contradictions(&self) -> Vec<(String, String, String)> {
        let mut contradictions = Vec::new();

        let admissible_ids: Vec<_> = self.admissible_sets.keys().cloned().collect();

        for i in 0..admissible_ids.len() {
            for j in (i+1)..admissible_ids.len() {
                let id_a = &admissible_ids[i];
                let id_b = &admissible_ids[j];

                if let (Some(a), Some(b)) = (
                    self.admissible_sets.get(id_a),
                    self.admissible_sets.get(id_b),
                ) {
                    // Check if they're marked as contradicting
                    if a.contradicts.contains(id_b) || b.contradicts.contains(id_a) {
                        contradictions.push((
                            id_a.clone(),
                            id_b.clone(),
                            "Marked as contradicting".to_string(),
                        ));
                    }

                    // TODO: Implement SMT-based satisfiability check
                    // Check if ∃x. (x ∈ A1 ∧ x ∈ A2) is unsatisfiable
                }
            }
        }

        contradictions
    }

    /// Detect omissions: Domains without coverage
    ///
    /// Returns domains where D \ D_S ≠ ∅ (intended domain minus specified domain)
    pub fn detect_omissions(&self) -> Vec<String> {
        self.domains
            .values()
            .filter(|domain| domain.has_gaps())
            .map(|domain| domain.id.clone())
            .collect()
    }

    /// Extract constraints from natural language text
    ///
    /// Parses specification text to identify implicit constraints like:
    /// - "at least N" → minimum constraint
    /// - "at most N" → maximum constraint
    /// - "must be" / "must not be" → boolean constraints
    /// - "between X and Y" → range constraints
    ///
    /// Returns a vector of extracted constraints.
    fn extract_constraints_from_text(&self, text: &str) -> Vec<Constraint> {
        let mut constraints = Vec::new();
        let lower_text = text.to_lowercase();

        // Pattern 1: "at least N"
        if let Some(min_value) = self.extract_numeric_value(&lower_text, "at least") {
            constraints.push(Constraint {
                description: format!("Minimum value: {}", min_value),
                formal: Some(format!(">= {}", min_value)),
                kind: ConstraintKind::Universal,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("pattern".to_string(), "at_least".to_string());
                    m.insert("value".to_string(), min_value.to_string());
                    m.insert("source".to_string(), text.to_string());
                    m
                },
            });
        }

        // Pattern 2: "at most N"
        if let Some(max_value) = self.extract_numeric_value(&lower_text, "at most") {
            constraints.push(Constraint {
                description: format!("Maximum value: {}", max_value),
                formal: Some(format!("<= {}", max_value)),
                kind: ConstraintKind::Universal,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("pattern".to_string(), "at_most".to_string());
                    m.insert("value".to_string(), max_value.to_string());
                    m.insert("source".to_string(), text.to_string());
                    m
                },
            });
        }

        // Pattern 3: "minimum N" / "minimum of N"
        if let Some(min_value) = self.extract_numeric_value(&lower_text, "minimum") {
            constraints.push(Constraint {
                description: format!("Minimum value: {}", min_value),
                formal: Some(format!(">= {}", min_value)),
                kind: ConstraintKind::Universal,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("pattern".to_string(), "minimum".to_string());
                    m.insert("value".to_string(), min_value.to_string());
                    m.insert("source".to_string(), text.to_string());
                    m
                },
            });
        }

        // Pattern 4: "maximum N" / "maximum of N"
        if let Some(max_value) = self.extract_numeric_value(&lower_text, "maximum") {
            constraints.push(Constraint {
                description: format!("Maximum value: {}", max_value),
                formal: Some(format!("<= {}", max_value)),
                kind: ConstraintKind::Universal,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("pattern".to_string(), "maximum".to_string());
                    m.insert("value".to_string(), max_value.to_string());
                    m.insert("source".to_string(), text.to_string());
                    m
                },
            });
        }

        // Pattern 5: "exactly N"
        if let Some(exact_value) = self.extract_numeric_value(&lower_text, "exactly") {
            constraints.push(Constraint {
                description: format!("Exact value: {}", exact_value),
                formal: Some(format!("== {}", exact_value)),
                kind: ConstraintKind::Universal,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("pattern".to_string(), "exactly".to_string());
                    m.insert("value".to_string(), exact_value.to_string());
                    m.insert("source".to_string(), text.to_string());
                    m
                },
            });
        }

        // Pattern 6: "between X and Y"
        if let Some((min, max)) = self.extract_range(&lower_text) {
            constraints.push(Constraint {
                description: format!("Range: {} to {}", min, max),
                formal: Some(format!(">= {} && <= {}", min, max)),
                kind: ConstraintKind::Universal,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("pattern".to_string(), "range".to_string());
                    m.insert("min".to_string(), min.to_string());
                    m.insert("max".to_string(), max.to_string());
                    m.insert("source".to_string(), text.to_string());
                    m
                },
            });
        }

        // Pattern 7: "must be" (boolean requirement)
        if lower_text.contains("must be") && !lower_text.contains("at least") && !lower_text.contains("at most") {
            // Extract what must be
            if let Some(pos) = lower_text.find("must be") {
                let after = &text[pos + 7..].trim();
                if !after.is_empty() {
                    constraints.push(Constraint {
                        description: format!("Required: {}", after),
                        formal: Some(format!("== {}", after)),
                        kind: ConstraintKind::Universal,
                        metadata: {
                            let mut m = HashMap::new();
                            m.insert("pattern".to_string(), "must_be".to_string());
                            m.insert("value".to_string(), after.to_string());
                            m.insert("source".to_string(), text.to_string());
                            m
                        },
                    });
                }
            }
        }

        // Pattern 8: "must not be" / "cannot be" (boolean prohibition)
        if lower_text.contains("must not") || lower_text.contains("cannot be") {
            let pattern = if lower_text.contains("must not") { "must not" } else { "cannot be" };
            if let Some(pos) = lower_text.find(pattern) {
                let after = &text[pos + pattern.len()..].trim();
                if !after.is_empty() {
                    constraints.push(Constraint {
                        description: format!("Forbidden: {}", after),
                        formal: Some(format!("!= {}", after)),
                        kind: ConstraintKind::Universal,
                        metadata: {
                            let mut m = HashMap::new();
                            m.insert("pattern".to_string(), "must_not_be".to_string());
                            m.insert("value".to_string(), after.to_string());
                            m.insert("source".to_string(), text.to_string());
                            m
                        },
                    });
                }
            }
        }

        constraints
    }

    /// Extract numeric value after a keyword
    fn extract_numeric_value(&self, text: &str, keyword: &str) -> Option<i64> {
        if let Some(pos) = text.find(keyword) {
            let after = &text[pos + keyword.len()..];
            for word in after.split_whitespace() {
                if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric()).parse::<i64>() {
                    return Some(n);
                }
            }
        }
        None
    }

    /// Extract range from "between X and Y" pattern
    fn extract_range(&self, text: &str) -> Option<(i64, i64)> {
        if let Some(pos) = text.find("between") {
            let after = &text[pos + 7..];
            let parts: Vec<&str> = after.split("and").collect();
            if parts.len() >= 2 {
                let min = self.extract_first_number(parts[0])?;
                let max = self.extract_first_number(parts[1])?;
                return Some((min, max));
            }
        }
        None
    }

    /// Extract first number from string
    fn extract_first_number(&self, s: &str) -> Option<i64> {
        for word in s.split_whitespace() {
            if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric()).parse::<i64>() {
                return Some(n);
            }
        }
        None
    }

    /// Populate UDAFModel from a SpecGraph
    ///
    /// This synchronizes the theoretical model with the practical graph representation.
    pub fn populate_from_graph(&mut self, graph: &crate::SpecGraph) {
        // Clear existing data
        self.universes.clear();
        self.domains.clear();
        self.admissible_sets.clear();
        self.transforms.clear();

        // Always create U0
        self.universes.insert("U0".to_string(), Universe::root());

        // Analyze nodes and populate universes
        for node in graph.list_nodes(None) {
            let layer = node.formality_layer;
            let universe_id = format!("U{}", layer);

            // Create universe if it doesn't exist
            if !self.universes.contains_key(&universe_id) && layer > 0 {
                let (name, description) = match layer {
                    1 => ("Formal Specifications".to_string(), "Structured formal specifications".to_string()),
                    2 => ("Interface Definitions".to_string(), "Interface contracts and protocols".to_string()),
                    3 => ("Executable Implementations".to_string(), "Actual code implementations".to_string()),
                    _ => (format!("Layer {}", layer), format!("Layer {} specifications", layer)),
                };
                self.add_universe(layer, name, description);
            }

            // Add spec to universe
            if let Some(universe) = self.universes.get_mut(&universe_id) {
                universe.specifications.insert(node.id.clone());
            }

            // Create admissible set for this specification
            let mut admissible_set = AdmissibleSet::new(node.id.clone(), universe_id.clone());

            // Extract constraints from content
            if node.kind == crate::NodeKind::Constraint {
                admissible_set.add_constraint(Constraint {
                    description: node.content.clone(),
                    formal: None,
                    kind: ConstraintKind::Universal,
                    metadata: node.metadata.clone(),
                });
            } else {
                // For non-Constraint nodes, extract implicit constraints from natural language
                let extracted = self.extract_constraints_from_text(&node.content);
                for constraint in extracted {
                    admissible_set.add_constraint(constraint);
                }
            }

            self.admissible_sets.insert(node.id.clone(), admissible_set);

            // Create domain if this is a Domain node
            if node.kind == crate::NodeKind::Domain {
                let domain = Domain::new(
                    node.id.clone(),
                    node.content.clone(),
                    "Domain boundary definition".to_string(),
                    universe_id,
                );
                self.domains.insert(node.id.clone(), domain);
            }
        }

        // Analyze edges to create transform functions
        for (edge, source_id, target_id) in graph.list_edges(None) {
            if edge.kind == crate::EdgeKind::Formalizes {
                // Create a transform function for this formalization
                let source_node = graph.get_node(source_id);
                let target_node = graph.get_node(target_id);

                if let (Some(source), Some(target)) = (source_node, target_node) {
                    let source_universe = format!("U{}", source.formality_layer);
                    let target_universe = format!("U{}", target.formality_layer);

                    // Create forward transform
                    let transform = TransformFunction::forward(
                        source_universe.clone(),
                        target_universe.clone(),
                        format!("Formalizes: {} -> {}", source.content.chars().take(30).collect::<String>(), target.content.chars().take(30).collect::<String>()),
                        TransformStrategy::Manual {
                            description: "Manual formalization via Formalizes edge".to_string(),
                        },
                    );
                    self.transforms.insert(transform.id.clone(), transform);
                }
            }
        }

        // Create inverse transforms for each projection universe to U0
        for (universe_id, _universe) in &self.universes {
            if universe_id == "U0" {
                continue;
            }

            let layer_num = universe_id.strip_prefix('U')
                .and_then(|s| s.parse::<u8>().ok())
                .unwrap_or(0);

            // Create inverse transform based on layer
            let strategy = match layer_num {
                3 => TransformStrategy::ASTAnalysis {
                    language: "rust".to_string(),
                    extractor_config: HashMap::from([
                        ("min_confidence".to_string(), "0.7".to_string()),
                    ]),
                },
                2 => TransformStrategy::TypeAnalysis {
                    type_system: "rust".to_string(),
                },
                1 => TransformStrategy::FormalVerification {
                    tool: "manual".to_string(),
                    verification_config: HashMap::new(),
                },
                _ => TransformStrategy::Manual {
                    description: format!("Inverse mapping from {}", universe_id),
                },
            };

            let transform = TransformFunction::inverse(
                universe_id.clone(),
                format!("Inverse mapping from {} to U0", universe_id),
                strategy,
            );
            self.transforms.insert(transform.id.clone(), transform);
        }
    }
}

impl Default for UDAFModel {
    fn default() -> Self {
        Self::new()
    }
}
