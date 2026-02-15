/// UDAF Model: The complete multi-universe specification model
///
/// This is the core data structure that implements the theoretical foundation
/// of specORACLE as described in conversation.md and motivation.md.

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use crate::formal::*;
use crate::{SpecGraph, InferredSpecification, RustExtractor};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UDAFModel {
    /// All universes in the model (keyed by UniverseId)
    #[serde(with = "super::serde_helpers::universe_map_serde")]
    pub universes: HashMap<UniverseId, Universe>,

    /// All domains across all universes (keyed by DomainId)
    #[serde(with = "super::serde_helpers::domain_map_serde")]
    pub domains: HashMap<DomainId, Domain>,

    /// All admissible sets (one per specification, keyed by SpecId)
    #[serde(with = "super::serde_helpers::admissible_map_serde")]
    pub admissible_sets: HashMap<SpecId, AdmissibleSet>,

    /// All transform functions between universes (keyed by TransformId)
    #[serde(with = "super::serde_helpers::transform_map_serde")]
    pub transforms: HashMap<TransformId, TransformFunction>,

    /// Metadata for extensibility
    pub metadata: Metadata,
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
    pub fn construct_u0(&mut self, graph: &SpecGraph) -> Result<Vec<InferredSpecification>, String> {
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
        graph: &SpecGraph,
    ) -> Result<Vec<InferredSpecification>, String> {
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
        graph: &SpecGraph,
    ) -> Result<Vec<InferredSpecification>, String> {
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
        graph: &SpecGraph,
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
                    // Try new field first, fall back to old field
                    let a_contradicts_b = if let Some(proof_data) = &a.proof_data {
                        proof_data.contradicts.contains(id_b)
                    } else if let Some(contradicts) = &a.contradicts {
                        contradicts.contains(id_b)
                    } else {
                        false
                    };

                    let b_contradicts_a = if let Some(proof_data) = &b.proof_data {
                        proof_data.contradicts.contains(id_a)
                    } else if let Some(contradicts) = &b.contradicts {
                        contradicts.contains(id_a)
                    } else {
                        false
                    };

                    if a_contradicts_b || b_contradicts_a {
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
    pub(crate) fn extract_constraints_from_text(&self, text: &str) -> Vec<Constraint> {
        let mut constraints = Vec::new();
        let lower_text = text.to_lowercase();

        // Pattern 1: "at least N"
        if let Some(min_value) = self.extract_numeric_value(&lower_text, "at least") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("at_least".to_string());
            meta.set_value(min_value.to_string());
            meta.set_source(text.to_string());

            let description_text = format!("Minimum value: {}", min_value);
            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            constraints.push(Constraint {
                // Layer 2: Proof data
                formal: Some(format!(">= {}", min_value)),
                kind: ConstraintKind::Universal,
                // OLD fields (for compatibility)
                description: Some(description_text),
                metadata: Some(meta),
                // NEW field (preferred)
                meta: Some(meta_with_desc),
            });
        }

        // Pattern 2: "at most N"
        if let Some(max_value) = self.extract_numeric_value(&lower_text, "at most") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("at_most".to_string());
            meta.set_value(max_value.to_string());
            meta.set_source(text.to_string());

            let description_text = format!("Maximum value: {}", max_value);
            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            constraints.push(Constraint {
                formal: Some(format!("<= {}", max_value)),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }

        // Pattern 3: "minimum N" / "minimum of N"
        if let Some(min_value) = self.extract_numeric_value(&lower_text, "minimum") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("minimum".to_string());
            meta.set_value(min_value.to_string());
            meta.set_source(text.to_string());

            let description_text = format!("Minimum value: {}", min_value);
            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            constraints.push(Constraint {
                formal: Some(format!(">= {}", min_value)),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }

        // Pattern 4: "maximum N" / "maximum of N"
        if let Some(max_value) = self.extract_numeric_value(&lower_text, "maximum") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("maximum".to_string());
            meta.set_value(max_value.to_string());
            meta.set_source(text.to_string());

            let description_text = format!("Maximum value: {}", max_value);
            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            constraints.push(Constraint {
                formal: Some(format!("<= {}", max_value)),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }

        // Pattern 5: "exactly N"
        if let Some(exact_value) = self.extract_numeric_value(&lower_text, "exactly") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("exactly".to_string());
            meta.set_value(exact_value.to_string());
            meta.set_source(text.to_string());

            let description_text = format!("Exact value: {}", exact_value);
            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            constraints.push(Constraint {
                formal: Some(format!("== {}", exact_value)),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }

        // Pattern 6: "between X and Y"
        if let Some((min, max)) = self.extract_range(&lower_text) {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("range".to_string());
            meta.set_min(min.to_string());
            meta.set_max(max.to_string());
            meta.set_source(text.to_string());

            let description_text = format!("Range: {} to {}", min, max);
            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            constraints.push(Constraint {
                formal: Some(format!(">= {} && <= {}", min, max)),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }

        // Pattern 7: "must be" (boolean requirement)
        if lower_text.contains("must be") && !lower_text.contains("at least") && !lower_text.contains("at most") {
            // Extract what must be
            if let Some(pos) = lower_text.find("must be") {
                let after = &text[pos + 7..].trim();
                if !after.is_empty() {
                    let mut meta = ConstraintMetadata::new();
                    meta.set_pattern("must_be".to_string());
                    meta.set_value(after.to_string());
                    meta.set_source(text.to_string());

                    let description_text = format!("Required: {}", after);
                    let mut meta_with_desc = meta.clone();
                    meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

                    constraints.push(Constraint {
                        formal: Some(format!("== {}", after)),
                        kind: ConstraintKind::Universal,
                        description: Some(description_text),
                        metadata: Some(meta),
                        meta: Some(meta_with_desc),
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
                    let mut meta = ConstraintMetadata::new();
                    meta.set_pattern("must_not_be".to_string());
                    meta.set_value(after.to_string());
                    meta.set_source(text.to_string());

                    let description_text = format!("Forbidden: {}", after);
                    let mut meta_with_desc = meta.clone();
                    meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

                    constraints.push(Constraint {
                        formal: Some(format!("!= {}", after)),
                        kind: ConstraintKind::Universal,
                        description: Some(description_text),
                        metadata: Some(meta),
                        meta: Some(meta_with_desc),
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
            // Check that universe_id exists (try meta first, fall back to old field)
            let universe_id_str = if let Some(meta) = &domain.meta {
                meta.get_str("universe_id").map(|s| s.as_str())
            } else {
                domain.universe_id.as_ref().map(|id| id.as_str())
            };

            if let Some(uid_str) = universe_id_str {
                if !valid_universe_ids.contains(uid_str) {
                    errors.push(format!(
                        "Domain {} references non-existent universe: {}",
                        domain_id.as_str(),
                        uid_str
                    ));
                }
            }

            // Check that all covered_by specs exist (try proof_data first, fall back to old field)
            let covered_by = if let Some(proof_data) = &domain.proof_data {
                Some(&proof_data.covered_by)
            } else {
                domain.covered_by.as_ref()
            };

            if let Some(covered_by_set) = covered_by {
                let invalid_specs = covered_by_set.check_integrity(&valid_spec_ids);
                if !invalid_specs.is_empty() {
                    errors.push(format!(
                        "Domain {} references non-existent specifications in covered_by: {:?}",
                        domain_id.as_str(),
                        invalid_specs
                    ));
                }
            }

            // Check that all subdomains exist (from meta)
            if let Some(meta) = &domain.meta {
                if let Some(_subdomains_str) = meta.get_str("subdomains") {
                    // Note: This is a simplified check; actual subdomain validation would need proper parsing
                    // For now, skip subdomain validation for new structure
                }
            } else if let Some(subdomains) = &domain.subdomains {
                let invalid_domains = subdomains.check_integrity(&valid_domain_ids);
                if !invalid_domains.is_empty() {
                    errors.push(format!(
                        "Domain {} references non-existent subdomains: {:?}",
                        domain_id.as_str(),
                        invalid_domains
                    ));
                }
            }
        }

        // Validate AdmissibleSet references
        for (spec_id, admissible_set) in &self.admissible_sets {
            // Check that universe_id exists (try meta first, fall back to old field)
            let universe_id_ref = if let Some(meta) = &admissible_set.meta {
                Some(&meta.universe_id)
            } else {
                admissible_set.universe_id.as_ref()
            };

            if let Some(uid) = universe_id_ref {
                if !valid_universe_ids.contains(uid.as_str()) {
                    errors.push(format!(
                        "AdmissibleSet {} references non-existent universe: {}",
                        spec_id.as_str(),
                        uid.as_str()
                    ));
                }
            }

            // Check that all contradicts references exist (try proof_data first, fall back to old field)
            let contradicts = if let Some(proof_data) = &admissible_set.proof_data {
                Some(&proof_data.contradicts)
            } else {
                admissible_set.contradicts.as_ref()
            };

            if let Some(contradicts_set) = contradicts {
                let invalid_contradicts = contradicts_set.check_integrity(&valid_spec_ids);
                if !invalid_contradicts.is_empty() {
                    errors.push(format!(
                        "AdmissibleSet {} references non-existent specifications in contradicts: {:?}",
                        spec_id.as_str(),
                        invalid_contradicts
                    ));
                }
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
