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

mod ids;
mod metadata;
mod refs;

// Re-export type-safe ID types
pub use ids::{UniverseId, DomainId, SpecId, TransformId, IdError};
// Re-export metadata types
pub use metadata::{MetadataKey, Metadata, UniverseMetadata, DomainMetadata, ConstraintMetadata, TransformMetadata};
// Re-export reference set types
pub use refs::{SpecSet, DomainSet};

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
    /// Unique identifier for this universe (e.g., "U0", "U1", "U2")
    pub id: UniverseId,

    /// Human-readable name (e.g., "Natural Language Requirements", "TLA+ Formal Spec", "Rust Implementation")
    pub name: String,

    /// Description of what this universe represents
    pub description: String,

    /// Specifications that belong to this universe
    pub specifications: SpecSet,

    /// Metadata for extensibility
    pub metadata: UniverseMetadata,
}

impl Universe {
    /// Create U0 (root universe) - constructed from inverse mappings
    pub fn root() -> Self {
        Self {
            id: UniverseId::root(),
            name: "Root Specification".to_string(),
            description: "The foundational universe constructed from inverse mappings of all projection universes. This represents the 'rough projection of the undefinable root specification'.".to_string(),
            specifications: SpecSet::new(),
            metadata: UniverseMetadata::new(),
        }
    }

    /// Create a projection universe (U1-UN)
    ///
    /// Returns Err if layer is 0 (use root() instead)
    pub fn projection(layer: u8, name: String, description: String) -> Result<Self, IdError> {
        let id = UniverseId::projection(layer)?;
        Ok(Self {
            id,
            name,
            description,
            specifications: SpecSet::new(),
            metadata: UniverseMetadata::new(),
        })
    }

    /// Get the layer number from the universe ID
    pub fn layer(&self) -> u8 {
        self.id.layer()
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
    pub id: DomainId,

    /// Human-readable name
    pub name: String,

    /// What this domain covers (natural language description)
    pub description: String,

    /// The universe this domain belongs to
    pub universe_id: UniverseId,

    /// Specifications that cover this domain
    pub covered_by: SpecSet,

    /// Sub-domains (hierarchical structure)
    pub subdomains: DomainSet,

    /// Metadata for extensibility
    pub metadata: DomainMetadata,
}

impl Domain {
    /// Create a new domain with generated ID
    pub fn new(name: String, description: String, universe_id: UniverseId) -> Self {
        Self {
            id: DomainId::new(),
            name,
            description,
            universe_id,
            covered_by: SpecSet::new(),
            subdomains: DomainSet::new(),
            metadata: DomainMetadata::new(),
        }
    }

    /// Create a domain with specific ID (for loading from storage)
    pub fn with_id(id: DomainId, name: String, description: String, universe_id: UniverseId) -> Self {
        Self {
            id,
            name,
            description,
            universe_id,
            covered_by: SpecSet::new(),
            subdomains: DomainSet::new(),
            metadata: DomainMetadata::new(),
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
    pub spec_id: SpecId,

    /// The universe this admissible set belongs to
    pub universe_id: UniverseId,

    /// Constraints that define membership in this set
    /// (e.g., "password.len() >= 8", "response_time < 1s")
    pub constraints: Vec<Constraint>,

    /// Known contradictions with other admissible sets
    pub contradicts: SpecSet,

    /// Metadata for extensibility
    pub metadata: Metadata,
}

impl AdmissibleSet {
    pub fn new(spec_id: SpecId, universe_id: UniverseId) -> Self {
        Self {
            spec_id,
            universe_id,
            constraints: Vec::new(),
            contradicts: SpecSet::new(),
            metadata: Metadata::new(),
        }
    }

    /// Add a constraint to this admissible set
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Mark this admissible set as contradicting another
    pub fn mark_contradiction(&mut self, other_id: SpecId) {
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
    pub metadata: ConstraintMetadata,
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
    pub id: TransformId,

    /// Source universe
    pub source_universe: UniverseId,

    /// Target universe
    pub target_universe: UniverseId,

    /// Human-readable description of this transformation
    pub description: String,

    /// The type of transformation
    pub kind: TransformKind,

    /// The actual transformation logic (strategy pattern)
    /// This is where we'll plug in different transformation implementations
    pub strategy: TransformStrategy,

    /// Metadata for extensibility
    pub metadata: TransformMetadata,
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
        source_universe: UniverseId,
        description: String,
        strategy: TransformStrategy,
    ) -> Self {
        let id = TransformId::inverse(&source_universe);
        Self {
            id,
            source_universe,
            target_universe: UniverseId::root(),
            description,
            kind: TransformKind::Inverse,
            strategy,
            metadata: TransformMetadata::new(),
        }
    }

    /// Create a forward mapping: Ui → Uj
    pub fn forward(
        source_universe: UniverseId,
        target_universe: UniverseId,
        description: String,
        strategy: TransformStrategy,
    ) -> Self {
        let id = TransformId::forward(&source_universe, &target_universe);
        Self {
            id,
            source_universe,
            target_universe,
            description,
            kind: TransformKind::Forward,
            strategy,
            metadata: TransformMetadata::new(),
        }
    }
}

/// UDAF Model: The complete multi-universe specification model
///
/// This is the core data structure that implements the theoretical foundation
/// of specORACLE as described in conversation.md and motivation.md.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UDAFModel {
    /// All universes in the model (keyed by UniverseId)
    #[serde(with = "universe_map_serde")]
    pub universes: HashMap<UniverseId, Universe>,

    /// All domains across all universes (keyed by DomainId)
    #[serde(with = "domain_map_serde")]
    pub domains: HashMap<DomainId, Domain>,

    /// All admissible sets (one per specification, keyed by SpecId)
    #[serde(with = "admissible_map_serde")]
    pub admissible_sets: HashMap<SpecId, AdmissibleSet>,

    /// All transform functions between universes (keyed by TransformId)
    #[serde(with = "transform_map_serde")]
    pub transforms: HashMap<TransformId, TransformFunction>,

    /// Metadata for extensibility
    pub metadata: Metadata,
}

// Serde helpers for HashMap with typed IDs
mod universe_map_serde {
    use super::*;
    use serde::de::{Deserialize, Deserializer};
    use serde::ser::Serializer;

    pub fn serialize<S>(map: &HashMap<UniverseId, Universe>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, Universe> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<UniverseId, Universe>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, Universe>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                UniverseId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

mod domain_map_serde {
    use super::*;
    use serde::de::{Deserialize, Deserializer};
    use serde::ser::Serializer;

    pub fn serialize<S>(map: &HashMap<DomainId, Domain>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, Domain> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<DomainId, Domain>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, Domain>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                DomainId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

mod admissible_map_serde {
    use super::*;
    use serde::de::{Deserialize, Deserializer};
    use serde::ser::Serializer;

    pub fn serialize<S>(map: &HashMap<SpecId, AdmissibleSet>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, AdmissibleSet> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<SpecId, AdmissibleSet>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, AdmissibleSet>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                SpecId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

mod transform_map_serde {
    use super::*;
    use serde::de::{Deserialize, Deserializer};
    use serde::ser::Serializer;

    pub fn serialize<S>(map: &HashMap<TransformId, TransformFunction>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, TransformFunction> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<TransformId, TransformFunction>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, TransformFunction>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                TransformId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

impl UDAFModel {
    pub fn new() -> Self {
        let mut model = Self {
            universes: HashMap::new(),
            domains: HashMap::new(),
            admissible_sets: HashMap::new(),
            transforms: HashMap::new(),
            metadata: Metadata::new(),
        };

        // Always create U0 (root universe)
        let u0 = Universe::root();
        model.universes.insert(u0.id.clone(), u0);

        model
    }

    /// Add a projection universe (U1, U2, etc.)
    ///
    /// Returns the universe ID or an error if layer is invalid
    pub fn add_universe(&mut self, layer: u8, name: String, description: String) -> Result<UniverseId, IdError> {
        let universe = Universe::projection(layer, name, description)?;
        let id = universe.id.clone();
        self.universes.insert(id.clone(), universe);
        Ok(id)
    }

    /// Add a domain to a universe
    pub fn add_domain(&mut self, domain: Domain) -> DomainId {
        let id = domain.id.clone();
        self.domains.insert(id.clone(), domain);
        id
    }

    /// Add an admissible set for a specification
    pub fn add_admissible_set(&mut self, admissible_set: AdmissibleSet) -> SpecId {
        let id = admissible_set.spec_id.clone();
        self.admissible_sets.insert(id.clone(), admissible_set);
        id
    }

    /// Add a transform function
    pub fn add_transform(&mut self, transform: TransformFunction) -> TransformId {
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
        for (universe_id, _universe) in &self.universes {
            if universe_id.layer() == 0 {
                continue;  // Skip U0 itself
            }

            // Find the inverse transform for this universe
            let inverse_transform_id = TransformId::inverse(universe_id);

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
            // Note: graph nodes still use HashMap<String, String> for metadata
            // so we use the string key directly
            if let Some(source_file) = node.metadata.get(MetadataKey::SourceFile.as_str()) {
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
                            id_a.as_str().to_string(),
                            id_b.as_str().to_string(),
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
            .map(|domain| domain.id.as_str().to_string())
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
            let mut metadata = ConstraintMetadata::new();
            metadata.set_pattern("at_least".to_string());
            metadata.set_value(min_value.to_string());
            metadata.set_source(text.to_string());

            constraints.push(Constraint {
                description: format!("Minimum value: {}", min_value),
                formal: Some(format!(">= {}", min_value)),
                kind: ConstraintKind::Universal,
                metadata,
            });
        }

        // Pattern 2: "at most N"
        if let Some(max_value) = self.extract_numeric_value(&lower_text, "at most") {
            let mut metadata = ConstraintMetadata::new();
            metadata.set_pattern("at_most".to_string());
            metadata.set_value(max_value.to_string());
            metadata.set_source(text.to_string());

            constraints.push(Constraint {
                description: format!("Maximum value: {}", max_value),
                formal: Some(format!("<= {}", max_value)),
                kind: ConstraintKind::Universal,
                metadata,
            });
        }

        // Pattern 3: "minimum N" / "minimum of N"
        if let Some(min_value) = self.extract_numeric_value(&lower_text, "minimum") {
            let mut metadata = ConstraintMetadata::new();
            metadata.set_pattern("minimum".to_string());
            metadata.set_value(min_value.to_string());
            metadata.set_source(text.to_string());

            constraints.push(Constraint {
                description: format!("Minimum value: {}", min_value),
                formal: Some(format!(">= {}", min_value)),
                kind: ConstraintKind::Universal,
                metadata,
            });
        }

        // Pattern 4: "maximum N" / "maximum of N"
        if let Some(max_value) = self.extract_numeric_value(&lower_text, "maximum") {
            let mut metadata = ConstraintMetadata::new();
            metadata.set_pattern("maximum".to_string());
            metadata.set_value(max_value.to_string());
            metadata.set_source(text.to_string());

            constraints.push(Constraint {
                description: format!("Maximum value: {}", max_value),
                formal: Some(format!("<= {}", max_value)),
                kind: ConstraintKind::Universal,
                metadata,
            });
        }

        // Pattern 5: "exactly N"
        if let Some(exact_value) = self.extract_numeric_value(&lower_text, "exactly") {
            let mut metadata = ConstraintMetadata::new();
            metadata.set_pattern("exactly".to_string());
            metadata.set_value(exact_value.to_string());
            metadata.set_source(text.to_string());

            constraints.push(Constraint {
                description: format!("Exact value: {}", exact_value),
                formal: Some(format!("== {}", exact_value)),
                kind: ConstraintKind::Universal,
                metadata,
            });
        }

        // Pattern 6: "between X and Y"
        if let Some((min, max)) = self.extract_range(&lower_text) {
            let mut metadata = ConstraintMetadata::new();
            metadata.set_pattern("range".to_string());
            metadata.set_min(min.to_string());
            metadata.set_max(max.to_string());
            metadata.set_source(text.to_string());

            constraints.push(Constraint {
                description: format!("Range: {} to {}", min, max),
                formal: Some(format!(">= {} && <= {}", min, max)),
                kind: ConstraintKind::Universal,
                metadata,
            });
        }

        // Pattern 7: "must be" (boolean requirement)
        if lower_text.contains("must be") && !lower_text.contains("at least") && !lower_text.contains("at most") {
            // Extract what must be
            if let Some(pos) = lower_text.find("must be") {
                let after = &text[pos + 7..].trim();
                if !after.is_empty() {
                    let mut metadata = ConstraintMetadata::new();
                    metadata.set_pattern("must_be".to_string());
                    metadata.set_value(after.to_string());
                    metadata.set_source(text.to_string());

                    constraints.push(Constraint {
                        description: format!("Required: {}", after),
                        formal: Some(format!("== {}", after)),
                        kind: ConstraintKind::Universal,
                        metadata,
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
                    let mut metadata = ConstraintMetadata::new();
                    metadata.set_pattern("must_not_be".to_string());
                    metadata.set_value(after.to_string());
                    metadata.set_source(text.to_string());

                    constraints.push(Constraint {
                        description: format!("Forbidden: {}", after),
                        formal: Some(format!("!= {}", after)),
                        kind: ConstraintKind::Universal,
                        metadata,
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
        let u0 = Universe::root();
        self.universes.insert(u0.id.clone(), u0);

        // Analyze nodes and populate universes
        for node in graph.list_nodes(None) {
            let layer = node.formality_layer;

            // Parse universe ID - skip if invalid
            let universe_id = match UniverseId::parse(&format!("U{}", layer)) {
                Ok(id) => id,
                Err(_) => continue,
            };

            // Create universe if it doesn't exist
            if !self.universes.contains_key(&universe_id) && layer > 0 {
                let (name, description) = match layer {
                    1 => ("Formal Specifications".to_string(), "Structured formal specifications".to_string()),
                    2 => ("Interface Definitions".to_string(), "Interface contracts and protocols".to_string()),
                    3 => ("Executable Implementations".to_string(), "Actual code implementations".to_string()),
                    _ => (format!("Layer {}", layer), format!("Layer {} specifications", layer)),
                };
                // add_universe now returns Result, but we can ignore errors here since we validated layer
                let _ = self.add_universe(layer, name, description);
            }

            // Parse spec ID - skip if invalid
            let spec_id = match SpecId::parse(&node.id) {
                Ok(id) => id,
                Err(_) => continue,
            };

            // Add spec to universe
            if let Some(universe) = self.universes.get_mut(&universe_id) {
                universe.specifications.insert(spec_id.clone());
            }

            // Create admissible set for this specification
            let mut admissible_set = AdmissibleSet::new(spec_id.clone(), universe_id.clone());

            // Extract constraints from content
            if node.kind == crate::NodeKind::Constraint {
                // Convert graph metadata (HashMap<String, String>) to ConstraintMetadata
                let metadata = ConstraintMetadata::from(node.metadata.clone());

                admissible_set.add_constraint(Constraint {
                    description: node.content.clone(),
                    formal: None,
                    kind: ConstraintKind::Universal,
                    metadata,
                });
            } else {
                // For non-Constraint nodes, extract implicit constraints from natural language
                let extracted = self.extract_constraints_from_text(&node.content);
                for constraint in extracted {
                    admissible_set.add_constraint(constraint);
                }
            }

            self.admissible_sets.insert(spec_id.clone(), admissible_set);

            // Create domain if this is a Domain node
            if node.kind == crate::NodeKind::Domain {
                let domain = Domain::with_id(
                    DomainId::parse(&node.id).unwrap_or_else(|_| DomainId::new()),
                    node.content.clone(),
                    "Domain boundary definition".to_string(),
                    universe_id,
                );
                self.domains.insert(domain.id.clone(), domain);
            }
        }

        // Analyze edges to create transform functions
        for (edge, source_id, target_id) in graph.list_edges(None) {
            if edge.kind == crate::EdgeKind::Formalizes {
                // Create a transform function for this formalization
                let source_node = graph.get_node(source_id);
                let target_node = graph.get_node(target_id);

                if let (Some(source), Some(target)) = (source_node, target_node) {
                    // Parse universe IDs
                    let source_universe = match UniverseId::parse(&format!("U{}", source.formality_layer)) {
                        Ok(id) => id,
                        Err(_) => continue,
                    };
                    let target_universe = match UniverseId::parse(&format!("U{}", target.formality_layer)) {
                        Ok(id) => id,
                        Err(_) => continue,
                    };

                    // Create forward transform
                    let transform = TransformFunction::forward(
                        source_universe,
                        target_universe,
                        format!("Formalizes: {} -> {}",
                            source.content.chars().take(30).collect::<String>(),
                            target.content.chars().take(30).collect::<String>()),
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
            if universe_id.layer() == 0 {
                continue;  // Skip U0 itself
            }

            let layer_num = universe_id.layer();

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
                    description: format!("Inverse mapping from {}", universe_id.as_str()),
                },
            };

            let transform = TransformFunction::inverse(
                universe_id.clone(),
                format!("Inverse mapping from {} to U0", universe_id.as_str()),
                strategy,
            );
            self.transforms.insert(transform.id.clone(), transform);
        }
    }

    /// Validate all reference integrity across the model
    ///
    /// Checks:
    /// - Universe specifications reference valid SpecIds
    /// - Domain universe_id references valid UniverseIds
    /// - Domain covered_by references valid SpecIds
    /// - Domain subdomains references valid DomainIds
    /// - AdmissibleSet universe_id references valid UniverseIds
    /// - AdmissibleSet contradicts references valid SpecIds
    /// - Transform source/target universes reference valid UniverseIds
    ///
    /// Returns Ok(()) if all references are valid, or Err with details of invalid references
    pub fn validate(&self) -> Result<(), String> {
        let mut errors = Vec::new();

        // Collect all valid IDs for reference checking
        let valid_universe_ids: HashSet<String> = self.universes.keys()
            .map(|id| id.as_str().to_string())
            .collect();

        let valid_spec_ids: HashSet<String> = self.admissible_sets.keys()
            .map(|id| id.as_str().to_string())
            .collect();

        let valid_domain_ids: HashSet<String> = self.domains.keys()
            .map(|id| id.as_str().to_string())
            .collect();

        // Validate Universe references
        for (universe_id, universe) in &self.universes {
            // Check that all specifications in the universe exist
            let invalid_specs = universe.specifications.check_integrity(&valid_spec_ids);
            if !invalid_specs.is_empty() {
                errors.push(format!(
                    "Universe {} references non-existent specifications: {:?}",
                    universe_id.as_str(),
                    invalid_specs
                ));
            }
        }

        // Validate Domain references
        for (domain_id, domain) in &self.domains {
            // Check that universe_id exists
            if !valid_universe_ids.contains(domain.universe_id.as_str()) {
                errors.push(format!(
                    "Domain {} references non-existent universe: {}",
                    domain_id.as_str(),
                    domain.universe_id.as_str()
                ));
            }

            // Check that all covered_by specs exist
            let invalid_specs = domain.covered_by.check_integrity(&valid_spec_ids);
            if !invalid_specs.is_empty() {
                errors.push(format!(
                    "Domain {} references non-existent specifications in covered_by: {:?}",
                    domain_id.as_str(),
                    invalid_specs
                ));
            }

            // Check that all subdomains exist
            let invalid_domains = domain.subdomains.check_integrity(&valid_domain_ids);
            if !invalid_domains.is_empty() {
                errors.push(format!(
                    "Domain {} references non-existent subdomains: {:?}",
                    domain_id.as_str(),
                    invalid_domains
                ));
            }
        }

        // Validate AdmissibleSet references
        for (spec_id, admissible_set) in &self.admissible_sets {
            // Check that universe_id exists
            if !valid_universe_ids.contains(admissible_set.universe_id.as_str()) {
                errors.push(format!(
                    "AdmissibleSet {} references non-existent universe: {}",
                    spec_id.as_str(),
                    admissible_set.universe_id.as_str()
                ));
            }

            // Check that all contradicts references exist
            let invalid_contradicts = admissible_set.contradicts.check_integrity(&valid_spec_ids);
            if !invalid_contradicts.is_empty() {
                errors.push(format!(
                    "AdmissibleSet {} references non-existent specifications in contradicts: {:?}",
                    spec_id.as_str(),
                    invalid_contradicts
                ));
            }
        }

        // Validate Transform references
        for (transform_id, transform) in &self.transforms {
            // Check that source_universe exists
            if !valid_universe_ids.contains(transform.source_universe.as_str()) {
                errors.push(format!(
                    "Transform {} references non-existent source universe: {}",
                    transform_id.as_str(),
                    transform.source_universe.as_str()
                ));
            }

            // Check that target_universe exists
            if !valid_universe_ids.contains(transform.target_universe.as_str()) {
                errors.push(format!(
                    "Transform {} references non-existent target universe: {}",
                    transform_id.as_str(),
                    transform.target_universe.as_str()
                ));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.join("\n"))
        }
    }
}

impl Default for UDAFModel {
    fn default() -> Self {
        Self::new()
    }
}
