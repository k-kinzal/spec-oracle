/// Prover: Formal verification foundation for specORACLE
///
/// This module provides the "proven world" that is the essence of specORACLE.
/// Unlike heuristic verification, the prover provides mathematical guarantees
/// about specifications.
///
/// From motivation.md:
/// > specORACLEは、「証明された世界」を提供することが本質である
/// > "The essence of specORACLE is to provide a 'proven world'"
///
/// Current implementation: Lightweight constraint solver
/// Future: Integration with Lean4, Coq, Z3, etc.

use std::collections::HashMap;
use serde::{Deserialize, Serialize};

/// Proof: A formal verification that a property holds
///
/// This represents a mathematical proof that a specification property is true.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Proof {
    /// Unique identifier
    pub id: String,

    /// The property being proved
    pub property: Property,

    /// The proof method used
    pub method: ProofMethod,

    /// Proof status
    pub status: ProofStatus,

    /// Proof steps (for human readability)
    pub steps: Vec<ProofStep>,

    /// Metadata
    pub metadata: HashMap<String, String>,
}

/// Property: A statement about specifications that can be proven
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Property {
    /// No contradiction exists between two specifications
    /// Proves: ∃x. (x ∈ A1 ∧ x ∈ A2) (admissible sets have non-empty intersection)
    Consistency { spec_a: String, spec_b: String },

    /// A specification is satisfiable
    /// Proves: ∃x. x ∈ A (admissible set is non-empty)
    Satisfiability { spec: String },

    /// A specification implies another
    /// Proves: A1 ⊆ A2 (admissible set inclusion)
    Implication { antecedent: String, consequent: String },

    /// A specification is complete for a domain
    /// Proves: D ⊆ D_S (domain fully covered)
    Completeness { spec: String, domain: String },

    /// A layer transformation preserves semantics
    /// Proves: f(A_source) ⊆ A_target (transform is sound)
    TransformSoundness { source: String, target: String, transform: String },
}

/// ProofMethod: How a proof was obtained
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProofMethod {
    /// Constraint solving (lightweight built-in solver)
    ConstraintSolving {
        solver: String,
        constraints: Vec<String>,
    },

    /// SMT solver (Z3, CVC4, etc.)
    SMTSolver {
        solver: String,
        formula: String,
    },

    /// Theorem prover (Lean4, Coq, Isabelle)
    TheoremProver {
        prover: String,
        proof_script: String,
    },

    /// Property-based testing (QuickCheck-style)
    PropertyTesting {
        iterations: usize,
        counterexample: Option<String>,
    },

    /// Manual proof (user-provided)
    Manual {
        justification: String,
    },
}

/// ProofStatus: Result of proof attempt
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofStatus {
    /// Property is proven true
    Proven,

    /// Property is proven false (counterexample found)
    Refuted,

    /// Unable to prove or refute
    Unknown,

    /// Proof attempt in progress
    Pending,
}

/// ProofStep: One step in a proof derivation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStep {
    /// Step description
    pub description: String,

    /// Justification (rule, axiom, lemma)
    pub justification: String,
}

/// Prover: The core verification engine
pub struct Prover {
    /// All proofs in the system
    proofs: HashMap<String, Proof>,
}

impl Prover {
    pub fn new() -> Self {
        Self {
            proofs: HashMap::new(),
        }
    }

    /// Prove consistency between two specifications
    ///
    /// Attempts to prove: ∃x. (x ∈ A1 ∧ x ∈ A2)
    /// (There exists an implementation that satisfies both specs)
    pub fn prove_consistency(
        &mut self,
        spec_a: &crate::udaf::AdmissibleSet,
        spec_b: &crate::udaf::AdmissibleSet,
    ) -> Proof {
        let property = Property::Consistency {
            spec_a: spec_a.spec_id.clone(),
            spec_b: spec_b.spec_id.clone(),
        };

        // Use lightweight constraint solver
        let (status, steps) = self.check_consistency_via_constraints(spec_a, spec_b);

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method: ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: vec![
                    format!("A1: {:?}", spec_a.constraints),
                    format!("A2: {:?}", spec_b.constraints),
                ],
            },
            status,
            steps,
            metadata: HashMap::new(),
        };

        self.proofs.insert(proof.id.clone(), proof.clone());
        proof
    }

    /// Prove satisfiability of a specification
    ///
    /// Attempts to prove: ∃x. x ∈ A
    /// (There exists at least one implementation that satisfies the spec)
    pub fn prove_satisfiability(
        &mut self,
        spec: &crate::udaf::AdmissibleSet,
    ) -> Proof {
        let property = Property::Satisfiability {
            spec: spec.spec_id.clone(),
        };

        let (status, steps) = self.check_satisfiability_via_constraints(spec);

        let proof = Proof {
            id: uuid::Uuid::new_v4().to_string(),
            property,
            method: ProofMethod::ConstraintSolving {
                solver: "lightweight_builtin".to_string(),
                constraints: spec.constraints.iter().map(|c| c.description.clone()).collect(),
            },
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
        spec_a: &crate::udaf::AdmissibleSet,
        spec_b: &crate::udaf::AdmissibleSet,
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        steps.push(ProofStep {
            description: format!("Analyzing {} constraints from spec A", spec_a.constraints.len()),
            justification: "Constraint enumeration".to_string(),
        });

        steps.push(ProofStep {
            description: format!("Analyzing {} constraints from spec B", spec_b.constraints.len()),
            justification: "Constraint enumeration".to_string(),
        });

        // Check if specs are explicitly marked as contradicting
        if spec_a.contradicts.contains(&spec_b.spec_id) {
            steps.push(ProofStep {
                description: "Specifications explicitly contradict each other".to_string(),
                justification: "Explicit contradiction marker".to_string(),
            });
            return (ProofStatus::Refuted, steps);
        }

        // Basic heuristic checks
        let contradictory = self.detect_obvious_contradiction(&spec_a.constraints, &spec_b.constraints);

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
        spec: &crate::udaf::AdmissibleSet,
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        if spec.constraints.is_empty() {
            steps.push(ProofStep {
                description: "No constraints - specification is trivially satisfiable".to_string(),
                justification: "Empty constraint set".to_string(),
            });
            return (ProofStatus::Proven, steps);
        }

        steps.push(ProofStep {
            description: format!("Analyzing {} constraints", spec.constraints.len()),
            justification: "Constraint enumeration".to_string(),
        });

        // Basic satisfiability check
        let unsatisfiable = self.detect_obvious_unsatisfiability(&spec.constraints);

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

    /// Detect obvious contradictions between constraint sets
    fn detect_obvious_contradiction(
        &self,
        constraints_a: &[crate::udaf::Constraint],
        constraints_b: &[crate::udaf::Constraint],
    ) -> bool {
        // Check for explicit conflicts in numeric constraints
        // e.g., "x >= 10" vs "x <= 5"

        for a in constraints_a {
            for b in constraints_b {
                if self.constraints_conflict(&a.description, &b.description) {
                    return true;
                }
            }
        }

        false
    }

    /// Detect obvious unsatisfiability within a constraint set
    fn detect_obvious_unsatisfiability(
        &self,
        constraints: &[crate::udaf::Constraint],
    ) -> bool {
        // Check for internal conflicts
        // e.g., "x >= 10" and "x <= 5" in the same spec

        for i in 0..constraints.len() {
            for j in (i+1)..constraints.len() {
                if self.constraints_conflict(&constraints[i].description, &constraints[j].description) {
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
}

impl Default for Prover {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::udaf::{AdmissibleSet, Constraint, ConstraintKind};

    #[test]
    fn prove_satisfiability_empty_constraints() {
        let mut prover = Prover::new();
        let spec = AdmissibleSet::new("test-spec".to_string(), "U0".to_string());

        let proof = prover.prove_satisfiability(&spec);

        assert_eq!(proof.status, ProofStatus::Proven);
        assert!(proof.steps.iter().any(|s| s.description.contains("trivially satisfiable")));
    }

    #[test]
    fn prove_satisfiability_consistent_constraints() {
        let mut prover = Prover::new();
        let mut spec = AdmissibleSet::new("test-spec".to_string(), "U0".to_string());

        spec.add_constraint(Constraint {
            description: "x must be at least 5".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        spec.add_constraint(Constraint {
            description: "x must be at most 10".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        let proof = prover.prove_satisfiability(&spec);

        // Should be Unknown (not Refuted) because constraints are compatible
        assert_ne!(proof.status, ProofStatus::Refuted);
    }

    #[test]
    fn prove_satisfiability_conflicting_constraints() {
        let mut prover = Prover::new();
        let mut spec = AdmissibleSet::new("test-spec".to_string(), "U0".to_string());

        spec.add_constraint(Constraint {
            description: "x must be at least 10".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        spec.add_constraint(Constraint {
            description: "x must be at most 5".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        let proof = prover.prove_satisfiability(&spec);

        assert_eq!(proof.status, ProofStatus::Refuted);
        assert!(proof.steps.iter().any(|s| s.description.contains("unsatisfiability")));
    }

    #[test]
    fn prove_consistency_compatible_specs() {
        let mut prover = Prover::new();

        let mut spec_a = AdmissibleSet::new("spec-a".to_string(), "U0".to_string());
        spec_a.add_constraint(Constraint {
            description: "password must be at least 8 characters".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        let mut spec_b = AdmissibleSet::new("spec-b".to_string(), "U0".to_string());
        spec_b.add_constraint(Constraint {
            description: "password must be at most 20 characters".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        let proof = prover.prove_consistency(&spec_a, &spec_b);

        // Should be Unknown (not Refuted) because specs are compatible
        assert_ne!(proof.status, ProofStatus::Refuted);
    }

    #[test]
    fn prove_consistency_conflicting_specs() {
        let mut prover = Prover::new();

        let mut spec_a = AdmissibleSet::new("spec-a".to_string(), "U0".to_string());
        spec_a.add_constraint(Constraint {
            description: "password must be at least 10 characters".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        let mut spec_b = AdmissibleSet::new("spec-b".to_string(), "U0".to_string());
        spec_b.add_constraint(Constraint {
            description: "password must be at most 8 characters".to_string(),
            formal: None,
            kind: ConstraintKind::Universal,
            metadata: HashMap::new(),
        });

        let proof = prover.prove_consistency(&spec_a, &spec_b);

        assert_eq!(proof.status, ProofStatus::Refuted);
        assert!(proof.steps.iter().any(|s| s.description.contains("contradiction")));
    }

    #[test]
    fn list_proofs_for_spec() {
        let mut prover = Prover::new();
        let spec_a = AdmissibleSet::new("spec-a".to_string(), "U0".to_string());
        let spec_b = AdmissibleSet::new("spec-b".to_string(), "U0".to_string());
        let spec_c = AdmissibleSet::new("spec-c".to_string(), "U0".to_string());

        prover.prove_satisfiability(&spec_a);
        prover.prove_consistency(&spec_a, &spec_b);
        prover.prove_satisfiability(&spec_c);

        let proofs_for_a = prover.get_proofs_for_spec("spec-a");
        assert_eq!(proofs_for_a.len(), 2); // satisfiability + consistency

        let proofs_for_c = prover.get_proofs_for_spec("spec-c");
        assert_eq!(proofs_for_c.len(), 1); // only satisfiability
    }
}
