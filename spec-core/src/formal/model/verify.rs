/// Verification module: Formal verification methods for UDAFModel
///
/// This module implements contradiction detection, omission detection,
/// and consistency verification using the Prover.

use crate::formal::{
    AdmissibleSet, ProofStatus, SpecId, UniverseId,
};

#[cfg(feature = "z3-solver")]
use crate::formal::Prover;

use super::model::UDAFModel;

/// Contradiction: Two specifications that cannot both be satisfied
#[derive(Debug, Clone)]
pub struct Contradiction {
    pub spec_a: String,
    pub spec_b: String,
    pub explanation: String,
    pub proof_status: ProofStatus,
}

/// Omission: A domain with coverage gaps
#[derive(Debug, Clone)]
pub struct Omission {
    pub domain_id: String,
    pub explanation: String,
    pub missing_coverage: Option<String>,
}

/// Layer inconsistency: Specifications at different layers that contradict
#[derive(Debug, Clone)]
pub struct LayerInconsistency {
    pub layer_a: u8,
    pub layer_b: u8,
    pub spec_a: String,
    pub spec_b: String,
    pub explanation: String,
}

/// Inter-universe inconsistency: Contradictions across universe boundaries
#[derive(Debug, Clone)]
pub struct InterUniverseInconsistency {
    pub universe_a: String,
    pub universe_b: String,
    pub spec_a: String,
    pub spec_b: String,
    pub explanation: String,
}

#[cfg(feature = "z3-solver")]
impl UDAFModel {
    /// Detect contradictions using the Prover
    ///
    /// Returns pairs of admissible sets that are mutually exclusive: A1 ∩ A2 = ∅
    ///
    /// Strategy:
    /// 1. Check explicit contradiction markers
    /// 2. Use Prover to formally verify consistency via Z3
    /// 3. Fallback to heuristic detection if formal proof unavailable
    pub fn detect_contradictions_with_prover(&self, prover: &mut Prover) -> Vec<Contradiction> {
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
                    // Check explicit contradiction markers first
                    let a_contradicts_b = if let Some(proof_data) = &a.proof_data {
                        proof_data.contradicts.contains(id_b)
                    } else if let Some(contradicts) = &a.contradicts {
                        contradicts.contains(id_b)
                    } else {
                        false
                    };

                    if a_contradicts_b {
                        contradictions.push(Contradiction {
                            spec_a: id_a.as_str().to_string(),
                            spec_b: id_b.as_str().to_string(),
                            explanation: "Explicitly marked as contradicting".to_string(),
                            proof_status: ProofStatus::Refuted,
                        });
                        continue;
                    }

                    // Use Prover for formal verification
                    let proof = prover.prove_consistency(a, b);

                    match proof.status {
                        ProofStatus::Refuted => {
                            // Formally proven contradiction
                            let explanation = proof.steps
                                .iter()
                                .map(|step| step.description.clone())
                                .collect::<Vec<_>>()
                                .join("; ");

                            contradictions.push(Contradiction {
                                spec_a: id_a.as_str().to_string(),
                                spec_b: id_b.as_str().to_string(),
                                explanation: format!("Formally proven inconsistent: {}", explanation),
                                proof_status: ProofStatus::Refuted,
                            });
                        }
                        ProofStatus::Unknown => {
                            // Check if heuristics suggest contradiction
                            if let Some(heuristic_explanation) = self.detect_heuristic_contradiction(a, b) {
                                contradictions.push(Contradiction {
                                    spec_a: id_a.as_str().to_string(),
                                    spec_b: id_b.as_str().to_string(),
                                    explanation: format!("Heuristically detected: {}", heuristic_explanation),
                                    proof_status: ProofStatus::Unknown,
                                });
                            }
                        }
                        ProofStatus::Proven => {
                            // Formally proven consistent - no contradiction
                        }
                        ProofStatus::Pending => {
                            // Proof in progress - skip for now
                        }
                    }
                }
            }
        }

        contradictions
    }

    /// Detect omissions using the Prover
    ///
    /// Returns domains where D \ D_S ≠ ∅ (intended domain minus specified domain)
    ///
    /// Strategy:
    /// 1. Check for domains without any covering specifications
    /// 2. Use Prover to check completeness for formalized domains
    /// 3. Report gaps where domain is not fully covered
    pub fn detect_omissions_with_prover(&self, prover: &mut Prover) -> Vec<Omission> {
        let mut omissions = Vec::new();

        for (domain_id, domain) in &self.domains {
            // Check if domain has covering specifications
            let covered_by = if let Some(proof_data) = &domain.proof_data {
                &proof_data.covered_by
            } else if let Some(covered_by) = &domain.covered_by {
                covered_by
            } else {
                // No coverage info - report as omission
                omissions.push(Omission {
                    domain_id: domain_id.as_str().to_string(),
                    explanation: "Domain has no covering specifications".to_string(),
                    missing_coverage: None,
                });
                continue;
            };

            if covered_by.is_empty() {
                omissions.push(Omission {
                    domain_id: domain_id.as_str().to_string(),
                    explanation: "Domain is not covered by any specifications".to_string(),
                    missing_coverage: None,
                });
                continue;
            }

            // For formalized domains, use Prover to check completeness
            let domain_is_formalized = if let Some(proof_data) = &domain.proof_data {
                !proof_data.constraints.is_empty()
            } else {
                false
            };

            if domain_is_formalized {
                // Collect covering specs
                let mut covering_specs = Vec::new();
                for spec_id in covered_by.iter() {
                    if let Some(spec) = self.admissible_sets.get(&spec_id) {
                        covering_specs.push(spec);
                    }
                }

                if !covering_specs.is_empty() {
                    let proof = prover.prove_completeness(domain, &covering_specs);

                    match proof.status {
                        ProofStatus::Refuted => {
                            // Coverage gap formally proven
                            let explanation = proof.steps
                                .iter()
                                .map(|step| step.description.clone())
                                .collect::<Vec<_>>()
                                .join("; ");

                            omissions.push(Omission {
                                domain_id: domain_id.as_str().to_string(),
                                explanation: format!("Coverage gap formally proven: {}", explanation),
                                missing_coverage: Some(format!("{} specs do not fully cover domain", covering_specs.len())),
                            });
                        }
                        ProofStatus::Unknown => {
                            // Can't prove completeness - flag as potential gap
                            omissions.push(Omission {
                                domain_id: domain_id.as_str().to_string(),
                                explanation: "Cannot verify completeness (insufficient formalization)".to_string(),
                                missing_coverage: None,
                            });
                        }
                        ProofStatus::Proven => {
                            // Domain fully covered - no omission
                        }
                        ProofStatus::Pending => {
                            // Proof in progress - skip for now
                        }
                    }
                }
            } else {
                // Non-formalized domain - use heuristics
                if domain.has_gaps() {
                    omissions.push(Omission {
                        domain_id: domain_id.as_str().to_string(),
                        explanation: "Domain marked as having gaps (heuristic)".to_string(),
                        missing_coverage: None,
                    });
                }
            }
        }

        omissions
    }

    /// Detect layer inconsistencies
    ///
    /// Checks for contradictions between specifications at different formality layers
    /// (e.g., U0 natural language vs U3 implementation)
    pub fn detect_layer_inconsistencies(&self, prover: &mut Prover) -> Vec<LayerInconsistency> {
        let mut inconsistencies = Vec::new();

        // Group specs by universe layer
        let mut specs_by_layer: std::collections::HashMap<u8, Vec<(&SpecId, &AdmissibleSet)>> =
            std::collections::HashMap::new();

        for (spec_id, spec) in &self.admissible_sets {
            let universe_id = if let Some(meta) = &spec.meta {
                &meta.universe_id
            } else if let Some(uid) = &spec.universe_id {
                uid
            } else {
                continue;
            };

            if let Some(universe) = self.universes.get(universe_id) {
                specs_by_layer
                    .entry(universe.layer())
                    .or_insert_with(Vec::new)
                    .push((spec_id, spec));
            }
        }

        // Check cross-layer consistency
        let layers: Vec<u8> = specs_by_layer.keys().copied().collect();

        for i in 0..layers.len() {
            for j in (i+1)..layers.len() {
                let layer_a = layers[i];
                let layer_b = layers[j];

                if let (Some(specs_a), Some(specs_b)) = (
                    specs_by_layer.get(&layer_a),
                    specs_by_layer.get(&layer_b),
                ) {
                    for (id_a, spec_a) in specs_a {
                        for (id_b, spec_b) in specs_b {
                            // Check if specs are related (e.g., via refinement)
                            // For now, check all pairs
                            let proof = prover.prove_consistency(spec_a, spec_b);

                            if proof.status == ProofStatus::Refuted {
                                let explanation = proof.steps
                                    .iter()
                                    .map(|step| step.description.clone())
                                    .collect::<Vec<_>>()
                                    .join("; ");

                                inconsistencies.push(LayerInconsistency {
                                    layer_a,
                                    layer_b,
                                    spec_a: id_a.as_str().to_string(),
                                    spec_b: id_b.as_str().to_string(),
                                    explanation: format!("Cross-layer contradiction: {}", explanation),
                                });
                            }
                        }
                    }
                }
            }
        }

        inconsistencies
    }

    /// Detect inter-universe inconsistencies
    ///
    /// Checks for contradictions across universe boundaries (parallel universes)
    pub fn detect_inter_universe_inconsistencies(&self, prover: &mut Prover) -> Vec<InterUniverseInconsistency> {
        let mut inconsistencies = Vec::new();

        // Group specs by universe
        let mut specs_by_universe: std::collections::HashMap<UniverseId, Vec<(&SpecId, &AdmissibleSet)>> =
            std::collections::HashMap::new();

        for (spec_id, spec) in &self.admissible_sets {
            let universe_id = if let Some(meta) = &spec.meta {
                meta.universe_id.clone()
            } else if let Some(uid) = &spec.universe_id {
                uid.clone()
            } else {
                continue;
            };

            specs_by_universe
                .entry(universe_id)
                .or_insert_with(Vec::new)
                .push((spec_id, spec));
        }

        // Check cross-universe consistency for parallel universes (same layer)
        let universe_ids: Vec<UniverseId> = specs_by_universe.keys().cloned().collect();

        for i in 0..universe_ids.len() {
            for j in (i+1)..universe_ids.len() {
                let uid_a = &universe_ids[i];
                let uid_b = &universe_ids[j];

                // Only check parallel universes (same layer)
                if uid_a.layer() != uid_b.layer() {
                    continue;
                }

                if let (Some(specs_a), Some(specs_b)) = (
                    specs_by_universe.get(uid_a),
                    specs_by_universe.get(uid_b),
                ) {
                    for (id_a, spec_a) in specs_a {
                        for (id_b, spec_b) in specs_b {
                            let proof = prover.prove_consistency(spec_a, spec_b);

                            if proof.status == ProofStatus::Refuted {
                                let explanation = proof.steps
                                    .iter()
                                    .map(|step| step.description.clone())
                                    .collect::<Vec<_>>()
                                    .join("; ");

                                inconsistencies.push(InterUniverseInconsistency {
                                    universe_a: uid_a.as_str().to_string(),
                                    universe_b: uid_b.as_str().to_string(),
                                    spec_a: id_a.as_str().to_string(),
                                    spec_b: id_b.as_str().to_string(),
                                    explanation: format!("Cross-universe contradiction: {}", explanation),
                                });
                            }
                        }
                    }
                }
            }
        }

        inconsistencies
    }

    /// Heuristic contradiction detection (fallback when formal proof unavailable)
    fn detect_heuristic_contradiction(&self, spec_a: &AdmissibleSet, spec_b: &AdmissibleSet) -> Option<String> {
        // Get constraints
        let constraints_a = if let Some(proof_data) = &spec_a.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_a.constraints {
            constraints
        } else {
            return None;
        };

        let constraints_b = if let Some(proof_data) = &spec_b.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_b.constraints {
            constraints
        } else {
            return None;
        };

        // Check for numeric conflicts
        for c_a in constraints_a {
            for c_b in constraints_b {
                let desc_a = if let Some(meta) = &c_a.meta {
                    meta.get_str("description").map(|s| s.as_str()).unwrap_or("")
                } else {
                    c_a.description.as_deref().unwrap_or("")
                };

                let desc_b = if let Some(meta) = &c_b.meta {
                    meta.get_str("description").map(|s| s.as_str()).unwrap_or("")
                } else {
                    c_b.description.as_deref().unwrap_or("")
                };

                // Check for conflicting numeric constraints
                if let Some(conflict) = self.check_numeric_conflict(desc_a, desc_b) {
                    return Some(conflict);
                }
            }
        }

        None
    }

    /// Check for numeric conflicts in constraint descriptions
    fn check_numeric_conflict(&self, desc_a: &str, desc_b: &str) -> Option<String> {
        let a_lower = desc_a.to_lowercase();
        let b_lower = desc_b.to_lowercase();

        // "at least X" vs "at most Y" where X > Y
        if let (Some(min_a), Some(max_b)) = (
            self.extract_minimum_heuristic(&a_lower),
            self.extract_maximum_heuristic(&b_lower),
        ) {
            if min_a > max_b {
                return Some(format!(
                    "Numeric conflict: minimum {} vs maximum {}",
                    min_a, max_b
                ));
            }
        }

        None
    }

    /// Extract minimum value (heuristic)
    fn extract_minimum_heuristic(&self, text: &str) -> Option<i64> {
        if let Some(pos) = text.find("at least") {
            return self.extract_number_heuristic(&text[pos..]);
        }
        if let Some(pos) = text.find("minimum") {
            return self.extract_number_heuristic(&text[pos..]);
        }
        None
    }

    /// Extract maximum value (heuristic)
    fn extract_maximum_heuristic(&self, text: &str) -> Option<i64> {
        if let Some(pos) = text.find("at most") {
            return self.extract_number_heuristic(&text[pos..]);
        }
        if let Some(pos) = text.find("maximum") {
            return self.extract_number_heuristic(&text[pos..]);
        }
        None
    }

    /// Extract first number from string (heuristic)
    fn extract_number_heuristic(&self, s: &str) -> Option<i64> {
        for word in s.split_whitespace() {
            if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric() && c != '-').parse::<i64>() {
                return Some(n);
            }
        }
        None
    }
}
