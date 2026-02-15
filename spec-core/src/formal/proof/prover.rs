/// Prover implementation: The core verification engine
///
/// This module implements the Prover struct and its methods for formal verification.

use std::collections::{HashMap, HashSet};
use super::types::*;
use super::z3_backend::Z3Backend;

/// Prover: The core verification engine
#[derive(Debug, Clone)]
pub struct Prover {
    /// All proofs in the system
    proofs: HashMap<String, Proof>,

    /// Z3 SMT solver backend
    z3_backend: Z3Backend,
}

impl Prover {
    pub fn new() -> Self {
        Self {
            proofs: HashMap::new(),
            z3_backend: Z3Backend::new(),
        }
    }

    /// Prove consistency between two specifications
    ///
    /// Attempts to prove: ∃x. (x ∈ A1 ∧ x ∈ A2)
    /// (There exists an implementation that satisfies both specs)
    ///
    /// Strategy:
    /// 1. Try Z3 SMT solver (complete formal verification)
    /// 2. Fallback to heuristics if Z3 unavailable
    pub fn prove_consistency(
        &mut self,
        spec_a: &crate::formal::AdmissibleSet,
        spec_b: &crate::formal::AdmissibleSet,
    ) -> Proof {
        let property = Property::Consistency {
            spec_a: spec_a.spec_id.as_str().to_string(),
            spec_b: spec_b.spec_id.as_str().to_string(),
        };

        // Get constraints from new structure first, fall back to old structure
        let constraints_a = if let Some(proof_data) = &spec_a.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_a.constraints {
            constraints
        } else {
            &vec![]
        };

        let constraints_b = if let Some(proof_data) = &spec_b.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_b.constraints {
            constraints
        } else {
            &vec![]
        };

        // Try Z3 first (complete proof)
        let (status, steps) = self.z3_backend.check_consistency(
            constraints_a,
            constraints_b,
        );

        let method = if cfg!(feature = "z3-solver") {
            ProofMethod::SMTSolver {
                solver: "Z3".to_string(),
                formula: format!(
                    "Consistency check: {} constraints (A) ∧ {} constraints (B)",
                    constraints_a.len(),
                    constraints_b.len()
                ),
            }
        } else {
            ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: vec![
                    format!("A1: {} constraints", constraints_a.len()),
                    format!("A2: {} constraints", constraints_b.len()),
                ],
            }
        };

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method,
            status,
            steps,
            metadata: HashMap::new(),
        };

        self.proofs.insert(proof.id.clone(), proof.clone());
        proof
    }

    /// Prove implication: A1 ⊆ A2
    ///
    /// Attempts to prove that every implementation satisfying A1 also satisfies A2.
    /// Formula: UNSAT(A1 ∧ ¬A2)
    ///
    /// Returns Proven if implication holds, Refuted with counterexample if not.
    pub fn prove_implication(
        &mut self,
        antecedent: &crate::formal::AdmissibleSet,
        consequent: &crate::formal::AdmissibleSet,
    ) -> Proof {
        let property = Property::Implication {
            antecedent: antecedent.spec_id.as_str().to_string(),
            consequent: consequent.spec_id.as_str().to_string(),
        };

        // Get constraints from new structure first, fall back to old structure
        let constraints_a = if let Some(proof_data) = &antecedent.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &antecedent.constraints {
            constraints
        } else {
            &vec![]
        };

        let constraints_b = if let Some(proof_data) = &consequent.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &consequent.constraints {
            constraints
        } else {
            &vec![]
        };

        // Try Z3 first (complete proof)
        // Formula: UNSAT(A1 ∧ ¬A2)
        let (status, steps) = self.z3_backend.check_implication(
            constraints_a,
            constraints_b,
        );

        let method = if cfg!(feature = "z3-solver") {
            ProofMethod::SMTSolver {
                solver: "Z3".to_string(),
                formula: format!(
                    "Implication check: UNSAT({} constraints (A1) ∧ ¬({} constraints (A2)))",
                    constraints_a.len(),
                    constraints_b.len()
                ),
            }
        } else {
            ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: vec![
                    format!("A1: {} constraints", constraints_a.len()),
                    format!("A2: {} constraints", constraints_b.len()),
                ],
            }
        };

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method,
            status,
            steps,
            metadata: std::collections::HashMap::new(),
        };

        self.proofs.insert(proof.id.clone(), proof.clone());
        proof
    }

    /// Prove consistency within domain: A1 ∩ A2 ∩ D ≠ ∅
    ///
    /// Checks if two specifications are consistent within a specific domain.
    /// Formula: SAT(A1 ∧ A2 ∧ D)
    ///
    /// Gracefully degrades to prove_consistency if domain has no formal constraints.
    pub fn prove_consistency_within_domain(
        &mut self,
        spec_a: &crate::formal::AdmissibleSet,
        spec_b: &crate::formal::AdmissibleSet,
        domain: &crate::formal::Domain,
    ) -> Proof {
        // Check if domain is formalized
        let domain_is_formalized = if let Some(proof_data) = &domain.proof_data {
            !proof_data.constraints.is_empty()
        } else {
            false
        };

        if !domain_is_formalized {
            // Graceful degradation: fall back to A-only proof
            let mut proof = self.prove_consistency(spec_a, spec_b);
            proof.steps.push(ProofStep {
                description: "Note: Domain has no formal constraints; checked A-only consistency".to_string(),
                justification: "Graceful degradation".to_string(),
            });
            return proof;
        }

        let property = Property::Consistency {
            spec_a: spec_a.spec_id.as_str().to_string(),
            spec_b: spec_b.spec_id.as_str().to_string(),
        };

        // Get constraints
        let constraints_a = if let Some(proof_data) = &spec_a.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_a.constraints {
            constraints
        } else {
            &vec![]
        };

        let constraints_b = if let Some(proof_data) = &spec_b.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_b.constraints {
            constraints
        } else {
            &vec![]
        };

        let domain_constraints = if let Some(proof_data) = &domain.proof_data {
            &proof_data.constraints
        } else {
            &vec![]
        };

        // Try Z3: SAT(A1 ∧ A2 ∧ D)
        let (status, steps) = self.z3_backend.check_consistency_within_domain(
            constraints_a,
            constraints_b,
            domain_constraints,
        );

        let method = if cfg!(feature = "z3-solver") {
            ProofMethod::SMTSolver {
                solver: "Z3".to_string(),
                formula: format!(
                    "Consistency within domain: SAT({} constraints (A1) ∧ {} constraints (A2) ∧ {} constraints (D))",
                    constraints_a.len(),
                    constraints_b.len(),
                    domain_constraints.len()
                ),
            }
        } else {
            ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: vec![
                    format!("A1: {} constraints", constraints_a.len()),
                    format!("A2: {} constraints", constraints_b.len()),
                    format!("D: {} constraints", domain_constraints.len()),
                ],
            }
        };

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method,
            status,
            steps,
            metadata: std::collections::HashMap::new(),
        };

        self.proofs.insert(proof.id.clone(), proof.clone());
        proof
    }

    /// Prove completeness: D ⊆ D_S (domain fully covered by specifications)
    ///
    /// Attempts to prove that all elements in the domain are covered by at least one specification.
    /// Formula: UNSAT(D ∧ ¬(A1 ∨ A2 ∨ ... ∨ An))
    /// Simplified: UNSAT(D ∧ ¬A1 ∧ ¬A2 ∧ ... ∧ ¬An)
    ///
    /// Detects 漏れB（カバレッジ不足）
    /// Returns Proven if no gaps, Refuted with witness if coverage gap exists.
    pub fn prove_completeness(
        &mut self,
        domain: &crate::formal::Domain,
        covering_specs: &[&crate::formal::AdmissibleSet],
    ) -> Proof {
        // Check if domain is formalized
        let domain_is_formalized = if let Some(proof_data) = &domain.proof_data {
            !proof_data.constraints.is_empty()
        } else {
            false
        };

        if !domain_is_formalized {
            let property = Property::Completeness {
                spec: format!("{} specs", covering_specs.len()),
                domain: domain.id.as_str().to_string(),
            };

            let steps = vec![ProofStep {
                description: "Domain not formalized - cannot check completeness".to_string(),
                justification: "Domain must have formal constraints for completeness proof".to_string(),
            }];

            let proof = Proof {
                id: uuid::Uuid::new_v4().to_string(),
                property,
                method: ProofMethod::Manual {
                    justification: "Domain not formalized".to_string(),
                },
                status: ProofStatus::Unknown,
                steps,
                metadata: std::collections::HashMap::new(),
            };

            self.proofs.insert(proof.id.clone(), proof.clone());
            return proof;
        }

        let property = Property::Completeness {
            spec: format!("{} specs", covering_specs.len()),
            domain: domain.id.as_str().to_string(),
        };

        // Get domain constraints
        let domain_constraints = if let Some(proof_data) = &domain.proof_data {
            &proof_data.constraints
        } else {
            &vec![]
        };

        // Get all covering spec constraints
        let mut all_spec_constraints: Vec<&[crate::formal::Constraint]> = Vec::new();
        for spec in covering_specs {
            let constraints: &[crate::formal::Constraint] = if let Some(proof_data) = &spec.proof_data {
                &proof_data.constraints
            } else if let Some(constraints) = &spec.constraints {
                constraints
            } else {
                &[]
            };
            all_spec_constraints.push(constraints);
        }

        // Try Z3: UNSAT(D ∧ ¬A1 ∧ ¬A2 ∧ ... ∧ ¬An)
        let (status, steps) = self.z3_backend.check_completeness(
            domain_constraints,
            &all_spec_constraints,
        );

        let method = if cfg!(feature = "z3-solver") {
            ProofMethod::SMTSolver {
                solver: "Z3".to_string(),
                formula: format!(
                    "Completeness check: UNSAT({} domain constraints ∧ ¬({} specs))",
                    domain_constraints.len(),
                    covering_specs.len()
                ),
            }
        } else {
            ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: vec![
                    format!("D: {} constraints", domain_constraints.len()),
                    format!("{} covering specs", covering_specs.len()),
                ],
            }
        };

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method,
            status,
            steps,
            metadata: std::collections::HashMap::new(),
        };

        self.proofs.insert(proof.id.clone(), proof.clone());
        proof
    }

    /// Prove satisfiability of a specification
    ///
    /// Attempts to prove: ∃x. x ∈ A
    /// (There exists at least one implementation that satisfies the spec)
    ///
    /// Strategy:
    /// 1. Try Z3 SMT solver (complete formal verification)
    /// 2. Fallback to heuristics if Z3 unavailable
    pub fn prove_satisfiability(
        &mut self,
        spec: &crate::formal::AdmissibleSet,
    ) -> Proof {
        let property = Property::Satisfiability {
            spec: spec.spec_id.as_str().to_string(),
        };

        // Get constraints from new structure first, fall back to old structure
        let constraints = if let Some(proof_data) = &spec.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec.constraints {
            constraints
        } else {
            &vec![]
        };

        // Try Z3 first (complete proof)
        let (status, steps) = self.z3_backend.check_satisfiability(constraints);

        let method = if cfg!(feature = "z3-solver") {
            ProofMethod::SMTSolver {
                solver: "Z3".to_string(),
                formula: format!("Satisfiability check: {} constraints", constraints.len()),
            }
        } else {
            ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: constraints.iter().filter_map(|c| {
                    // Try new structure first, fall back to old
                    if let Some(meta) = &c.meta {
                        meta.get_str("description").map(|s| s.clone())
                    } else {
                        c.description.clone()
                    }
                }).collect(),
            }
        };

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method,
            status,
            steps,
            metadata: HashMap::new(),
        };

        self.proofs.insert(proof.id.clone(), proof.clone());
        proof
    }

    /// Check consistency via constraint analysis
    fn check_consistency_via_constraints(
        &self,
        spec_a: &crate::formal::AdmissibleSet,
        spec_b: &crate::formal::AdmissibleSet,
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        // Get constraints from new structure first, fall back to old structure
        let constraints_a = if let Some(proof_data) = &spec_a.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_a.constraints {
            constraints
        } else {
            &vec![]
        };

        let constraints_b = if let Some(proof_data) = &spec_b.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec_b.constraints {
            constraints
        } else {
            &vec![]
        };

        steps.push(ProofStep {
            description: format!("Analyzing {} constraints from spec A", constraints_a.len()),
            justification: "Constraint enumeration".to_string(),
        });

        steps.push(ProofStep {
            description: format!("Analyzing {} constraints from spec B", constraints_b.len()),
            justification: "Constraint enumeration".to_string(),
        });

        // Check if specs are explicitly marked as contradicting
        let a_contradicts_b = if let Some(proof_data) = &spec_a.proof_data {
            proof_data.contradicts.contains(&spec_b.spec_id)
        } else if let Some(contradicts) = &spec_a.contradicts {
            contradicts.contains(&spec_b.spec_id)
        } else {
            false
        };

        if a_contradicts_b {
            steps.push(ProofStep {
                description: "Specifications explicitly contradict each other".to_string(),
                justification: "Explicit contradiction marker".to_string(),
            });
            return (ProofStatus::Refuted, steps);
        }

        // Basic heuristic checks
        let contradictory = self.detect_obvious_contradiction(constraints_a, constraints_b);

        if contradictory {
            steps.push(ProofStep {
                description: "Detected obvious contradiction in constraints".to_string(),
                justification: "Constraint conflict analysis".to_string(),
            });
            (ProofStatus::Refuted, steps)
        } else {
            steps.push(ProofStep {
                description: "No obvious contradiction detected".to_string(),
                justification: "Heuristic constraint analysis".to_string(),
            });
            steps.push(ProofStep {
                description: "Note: This is not a complete proof. SMT solver integration needed for soundness.".to_string(),
                justification: "Limitation acknowledgment".to_string(),
            });
            (ProofStatus::Unknown, steps)
        }
    }

    /// Check satisfiability via constraint analysis
    fn check_satisfiability_via_constraints(
        &self,
        spec: &crate::formal::AdmissibleSet,
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        // Get constraints from new structure first, fall back to old structure
        let constraints = if let Some(proof_data) = &spec.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec.constraints {
            constraints
        } else {
            &vec![]
        };

        if constraints.is_empty() {
            steps.push(ProofStep {
                description: "No constraints - specification is trivially satisfiable".to_string(),
                justification: "Empty constraint set".to_string(),
            });
            return (ProofStatus::Proven, steps);
        }

        steps.push(ProofStep {
            description: format!("Analyzing {} constraints", constraints.len()),
            justification: "Constraint enumeration".to_string(),
        });

        // Basic satisfiability check
        let unsatisfiable = self.detect_obvious_unsatisfiability(constraints);

        if unsatisfiable {
            steps.push(ProofStep {
                description: "Detected obvious unsatisfiability".to_string(),
                justification: "Constraint conflict analysis".to_string(),
            });
            (ProofStatus::Refuted, steps)
        } else {
            steps.push(ProofStep {
                description: "No obvious unsatisfiability detected".to_string(),
                justification: "Heuristic constraint analysis".to_string(),
            });
            steps.push(ProofStep {
                description: "Note: This is not a complete proof. SMT solver integration needed for soundness.".to_string(),
                justification: "Limitation acknowledgment".to_string(),
            });
            (ProofStatus::Unknown, steps)
        }
    }

    /// Extract description from constraint (tries new structure first, falls back to old)
    fn get_constraint_description<'a>(&self, constraint: &'a crate::formal::Constraint) -> &'a str {
        if let Some(meta) = &constraint.meta {
            if let Some(desc) = meta.get_str("description") {
                return desc;
            }
        }
        if let Some(desc) = &constraint.description {
            return desc;
        }
        ""
    }

    /// Detect obvious contradictions between constraint sets
    fn detect_obvious_contradiction(
        &self,
        constraints_a: &[crate::formal::Constraint],
        constraints_b: &[crate::formal::Constraint],
    ) -> bool {
        // Check for explicit conflicts in numeric constraints
        // e.g., "x >= 10" vs "x <= 5"

        for a in constraints_a {
            for b in constraints_b {
                let desc_a = self.get_constraint_description(a);
                let desc_b = self.get_constraint_description(b);
                if self.constraints_conflict(desc_a, desc_b) {
                    return true;
                }
            }
        }

        false
    }

    /// Detect obvious unsatisfiability within a constraint set
    fn detect_obvious_unsatisfiability(
        &self,
        constraints: &[crate::formal::Constraint],
    ) -> bool {
        // Check for internal conflicts
        // e.g., "x >= 10" and "x <= 5" in the same spec

        for i in 0..constraints.len() {
            for j in (i+1)..constraints.len() {
                let desc_i = self.get_constraint_description(&constraints[i]);
                let desc_j = self.get_constraint_description(&constraints[j]);
                if self.constraints_conflict(desc_i, desc_j) {
                    return true;
                }
            }
        }

        false
    }

    /// Heuristic check if two constraints conflict
    fn constraints_conflict(&self, desc_a: &str, desc_b: &str) -> bool {
        let a_lower = desc_a.to_lowercase();
        let b_lower = desc_b.to_lowercase();

        // Numeric conflict patterns
        // "at least X" vs "at most Y" where X > Y
        if let (Some(min_a), Some(max_b)) = (
            self.extract_minimum(&a_lower),
            self.extract_maximum(&b_lower),
        ) {
            if min_a > max_b {
                return true;
            }
        }

        if let (Some(max_a), Some(min_b)) = (
            self.extract_maximum(&a_lower),
            self.extract_minimum(&b_lower),
        ) {
            if max_a < min_b {
                return true;
            }
        }

        // Boolean conflict patterns
        // "must be X" vs "must not be X" / "forbidden X"
        if (a_lower.contains("must be") || a_lower.contains("required"))
            && (b_lower.contains("must not") || b_lower.contains("forbidden") || b_lower.contains("prohibited"))
        {
            // Check if they're about the same thing
            let a_words: Vec<&str> = a_lower.split_whitespace().collect();
            let b_words: Vec<&str> = b_lower.split_whitespace().collect();
            let common_words: Vec<&str> = a_words.iter().filter(|w| b_words.contains(w)).copied().collect();

            if common_words.len() >= 2 {
                return true;
            }
        }

        false
    }

    /// Extract minimum value from constraint description
    fn extract_minimum(&self, desc: &str) -> Option<i64> {
        // "at least N", "minimum N", ">= N"
        if let Some(pos) = desc.find("at least") {
            return self.extract_number(&desc[pos..]);
        }
        if let Some(pos) = desc.find("minimum") {
            return self.extract_number(&desc[pos..]);
        }
        if let Some(pos) = desc.find(">=") {
            return self.extract_number(&desc[pos..]);
        }
        None
    }

    /// Extract maximum value from constraint description
    fn extract_maximum(&self, desc: &str) -> Option<i64> {
        // "at most N", "maximum N", "<= N"
        if let Some(pos) = desc.find("at most") {
            return self.extract_number(&desc[pos..]);
        }
        if let Some(pos) = desc.find("maximum") {
            return self.extract_number(&desc[pos..]);
        }
        if let Some(pos) = desc.find("<=") {
            return self.extract_number(&desc[pos..]);
        }
        None
    }

    /// Extract first number from string
    fn extract_number(&self, s: &str) -> Option<i64> {
        for word in s.split_whitespace() {
            if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric()).parse::<i64>() {
                return Some(n);
            }
        }
        None
    }

    /// Get all proofs
    pub fn list_proofs(&self) -> Vec<&Proof> {
        self.proofs.values().collect()
    }

    /// Get a specific proof
    pub fn get_proof(&self, id: &str) -> Option<&Proof> {
        self.proofs.get(id)
    }

    /// Get proofs for a specific specification
    pub fn get_proofs_for_spec(&self, spec_id: &str) -> Vec<&Proof> {
        self.proofs.values().filter(|p| {
            match &p.property {
                Property::Consistency { spec_a, spec_b } => {
                    spec_a == spec_id || spec_b == spec_id
                }
                Property::Satisfiability { spec } => spec == spec_id,
                Property::Implication { antecedent, consequent } => {
                    antecedent == spec_id || consequent == spec_id
                }
                Property::Completeness { spec, .. } => spec == spec_id,
                Property::TransformSoundness { source, target, .. } => {
                    source == spec_id || target == spec_id
                }
            }
        }).collect()
    }

    /// Heuristically detect underspecification (漏れA)
    ///
    /// Returns confidence-scored report, not a formal proof.
    /// Underspecification is a design choice, not an error, so it cannot be formally proven wrong.
    pub fn detect_underspecification(
        &self,
        spec: &crate::formal::AdmissibleSet,
        domain: &crate::formal::Domain,
        _universe: &crate::formal::Universe,
    ) -> UnderspecificationReport {
        let mut confidence = 0.0f32;
        let mut reasons = Vec::new();
        let mut suggestions = Vec::new();

        // Get constraints
        let spec_constraints = if let Some(proof_data) = &spec.proof_data {
            &proof_data.constraints
        } else if let Some(constraints) = &spec.constraints {
            constraints
        } else {
            &vec![]
        };

        let domain_constraints = if let Some(proof_data) = &domain.proof_data {
            &proof_data.constraints
        } else {
            &vec![]
        };

        // Heuristic 1: Constraint count
        // If spec has very few constraints relative to domain complexity
        if spec_constraints.is_empty() {
            confidence += 0.8;
            reasons.push("Specification has no constraints".to_string());
            suggestions.push("Add constraints to define the admissible set".to_string());
        } else if spec_constraints.len() < 3 && !domain_constraints.is_empty() && domain_constraints.len() > spec_constraints.len() * 2 {
            confidence += 0.4;
            reasons.push(format!(
                "Specification has only {} constraints, but domain has {} constraints",
                spec_constraints.len(),
                domain_constraints.len()
            ));
            suggestions.push("Consider adding more constraints to narrow the admissible set".to_string());
        }

        // Heuristic 2: Free variables
        // Extract variable names from domain and spec
        let domain_vars = self.extract_variable_names_from_constraints(domain_constraints);
        let spec_vars = self.extract_variable_names_from_constraints(spec_constraints);

        let unconstrained_vars: Vec<_> = domain_vars.iter()
            .filter(|v| !spec_vars.contains(*v))
            .collect();

        if !unconstrained_vars.is_empty() {
            confidence += 0.3 * (unconstrained_vars.len() as f32 / domain_vars.len().max(1) as f32);
            reasons.push(format!(
                "Domain mentions {} variable(s) not constrained in spec: {:?}",
                unconstrained_vars.len(),
                unconstrained_vars
            ));
            suggestions.push("Add constraints for unconstrained variables".to_string());
        }

        // Heuristic 3: Keyword matching
        // Check if domain description mentions aspects not addressed in spec
        let domain_desc = if let Some(meta) = &domain.meta {
            meta.get_str("description").map(|s| s.as_str()).unwrap_or("")
        } else if let Some(desc) = &domain.description {
            desc.as_str()
        } else {
            ""
        };

        let keywords = vec!["security", "performance", "reliability", "availability", "scalability"];
        let domain_lower = domain_desc.to_lowercase();
        let spec_text = spec_constraints.iter()
            .filter_map(|c| {
                if let Some(meta) = &c.meta {
                    meta.get_str("description").map(|s| s.to_lowercase())
                } else {
                    c.description.as_ref().map(|s| s.to_lowercase())
                }
            })
            .collect::<Vec<_>>()
            .join(" ");

        for keyword in keywords {
            if domain_lower.contains(keyword) && !spec_text.contains(keyword) {
                confidence += 0.1;
                reasons.push(format!(
                    "Domain mentions '{}' but specification does not address it",
                    keyword
                ));
                suggestions.push(format!("Add constraints related to {}", keyword));
            }
        }

        // Heuristic 4: Constraint tightness
        // Check if constraints are very loose (wide ranges, weak requirements)
        let loose_constraints = spec_constraints.iter().filter(|c| {
            let desc = if let Some(meta) = &c.meta {
                meta.get_str("description").map(|s| s.as_str()).unwrap_or("")
            } else {
                c.description.as_deref().unwrap_or("")
            };
            let lower = desc.to_lowercase();
            // Very loose patterns: "at least 1", "at most 1000000", etc.
            (lower.contains("at least 1") && !lower.contains("at least 10")) ||
            lower.contains("at most 1000") ||
            lower.contains("any") ||
            lower.contains("optional")
        }).count();

        if loose_constraints > 0 {
            confidence += 0.2 * (loose_constraints as f32 / spec_constraints.len().max(1) as f32);
            reasons.push(format!(
                "{} constraint(s) appear very loose or permissive",
                loose_constraints
            ));
            suggestions.push("Consider tightening loose constraints".to_string());
        }

        // Cap confidence at 1.0
        confidence = confidence.min(1.0);

        let is_likely_underspecified = confidence >= 0.5;

        UnderspecificationReport {
            spec_id: spec.spec_id.as_str().to_string(),
            domain_id: domain.id.as_str().to_string(),
            is_likely_underspecified,
            confidence,
            reasons,
            suggestions,
        }
    }

    /// Extract variable names from constraints
    fn extract_variable_names_from_constraints(&self, constraints: &[crate::formal::Constraint]) -> HashSet<String> {
        let mut vars = HashSet::new();
        for constraint in constraints {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str()).unwrap_or("")
            } else {
                constraint.description.as_deref().unwrap_or("")
            };

            // Extract variable name (heuristic: word before "must", "should", "is", etc.)
            let words: Vec<&str> = desc.split_whitespace().collect();
            for (i, &word) in words.iter().enumerate() {
                if word == "must" || word == "should" || word == "is" {
                    if i > 0 {
                        vars.insert(words[i-1].to_lowercase().trim_matches(|c: char| !c.is_alphanumeric()).to_string());
                    }
                }
            }
        }
        vars
    }
}

/// Underspecification detection report
///
/// This is a heuristic analysis, not a formal proof.
/// 漏れA（未規定）は設計上の選択であり、エラーではない。
#[derive(Debug, Clone)]
pub struct UnderspecificationReport {
    pub spec_id: String,
    pub domain_id: String,
    pub is_likely_underspecified: bool,
    pub confidence: f32,
    pub reasons: Vec<String>,
    pub suggestions: Vec<String>,
}

impl Default for Prover {
    fn default() -> Self {
        Self::new()
    }
}
