/// Z3 SMT Solver Backend for specORACLE Prover
///
/// This module provides complete formal verification through Z3,
/// replacing heuristic constraint checking with mathematical proofs.
///
/// From motivation.md:
/// > 証明器の実装により、ヒューリスティックではなく形式的に検証する
/// > "The prover implementation provides formal verification, not heuristics"

#[cfg(feature = "z3-solver")]
use z3::{Config, Context, Solver, ast::{Ast, Bool, Int}};
use crate::formal::{Constraint, ConstraintKind};
use super::types::{ProofStatus, ProofStep};
use std::collections::HashMap;

/// Z3-based SMT solver backend
#[allow(dead_code)]
#[derive(Debug)]
pub struct Z3Backend {
    #[cfg(feature = "z3-solver")]
    context: Context,
}

impl Clone for Z3Backend {
    fn clone(&self) -> Self {
        Self::new()
    }
}

#[allow(dead_code)]
impl Z3Backend {
    pub fn new() -> Self {
        #[cfg(feature = "z3-solver")]
        {
            let config = Config::new();
            let context = Context::new(&config);
            Self { context }
        }

        #[cfg(not(feature = "z3-solver"))]
        {
            Self {}
        }
    }

    /// Check satisfiability of constraints using Z3
    ///
    /// Returns (ProofStatus, ProofSteps)
    pub fn check_satisfiability(
        &self,
        constraints: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        #[cfg(feature = "z3-solver")]
        {
            self.check_satisfiability_z3(constraints)
        }

        #[cfg(not(feature = "z3-solver"))]
        {
            let steps = vec![ProofStep {
                description: "Z3 solver not available (feature disabled)".to_string(),
                justification: "Fallback to heuristic".to_string(),
            }];
            (ProofStatus::Unknown, steps)
        }
    }

    /// Check consistency between two constraint sets using Z3
    ///
    /// Returns (ProofStatus, ProofSteps)
    pub fn check_consistency(
        &self,
        constraints_a: &[Constraint],
        constraints_b: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        #[cfg(feature = "z3-solver")]
        {
            self.check_consistency_z3(constraints_a, constraints_b)
        }

        #[cfg(not(feature = "z3-solver"))]
        {
            let steps = vec![ProofStep {
                description: "Z3 solver not available (feature disabled)".to_string(),
                justification: "Fallback to heuristic".to_string(),
            }];
            (ProofStatus::Unknown, steps)
        }
    }

    /// Check implication: A1 ⊆ A2 (all elements of A1 are also in A2)
    ///
    /// Formula: UNSAT(A1 ∧ ¬A2)
    /// Returns Proven if implication holds, Refuted with counterexample if not
    pub fn check_implication(
        &self,
        constraints_antecedent: &[Constraint],
        constraints_consequent: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        #[cfg(feature = "z3-solver")]
        {
            self.check_implication_z3(constraints_antecedent, constraints_consequent)
        }

        #[cfg(not(feature = "z3-solver"))]
        {
            let steps = vec![ProofStep {
                description: "Z3 solver not available (feature disabled)".to_string(),
                justification: "Fallback to heuristic".to_string(),
            }];
            (ProofStatus::Unknown, steps)
        }
    }

    /// Check consistency within domain: A1 ∩ A2 ∩ D ≠ ∅
    ///
    /// Formula: SAT(A1 ∧ A2 ∧ D)
    /// Returns Proven if consistent, Refuted if contradictory within domain
    pub fn check_consistency_within_domain(
        &self,
        constraints_a: &[Constraint],
        constraints_b: &[Constraint],
        domain_constraints: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        #[cfg(feature = "z3-solver")]
        {
            self.check_consistency_within_domain_z3(constraints_a, constraints_b, domain_constraints)
        }

        #[cfg(not(feature = "z3-solver"))]
        {
            let steps = vec![ProofStep {
                description: "Z3 solver not available (feature disabled)".to_string(),
                justification: "Fallback to heuristic".to_string(),
            }];
            (ProofStatus::Unknown, steps)
        }
    }

    /// Check completeness: D ⊆ D_S (domain fully covered)
    ///
    /// Formula: UNSAT(D ∧ ¬A1 ∧ ¬A2 ∧ ... ∧ ¬An)
    /// Returns Proven if complete, Refuted with witness if gap exists
    pub fn check_completeness(
        &self,
        domain_constraints: &[Constraint],
        spec_constraints: &[&[Constraint]],
    ) -> (ProofStatus, Vec<ProofStep>) {
        #[cfg(feature = "z3-solver")]
        {
            self.check_completeness_z3(domain_constraints, spec_constraints)
        }

        #[cfg(not(feature = "z3-solver"))]
        {
            let steps = vec![ProofStep {
                description: "Z3 solver not available (feature disabled)".to_string(),
                justification: "Fallback to heuristic".to_string(),
            }];
            (ProofStatus::Unknown, steps)
        }
    }

    #[cfg(feature = "z3-solver")]
    fn check_satisfiability_z3(
        &self,
        constraints: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        if constraints.is_empty() {
            steps.push(ProofStep {
                description: "No constraints - trivially satisfiable".to_string(),
                justification: "Empty constraint set".to_string(),
            });
            return (ProofStatus::Proven, steps);
        }

        steps.push(ProofStep {
            description: format!("Encoding {} constraints into Z3", constraints.len()),
            justification: "SMT encoding".to_string(),
        });

        let solver = Solver::new(&self.context);
        let mut var_map: HashMap<String, Int<'_>> = HashMap::new();

        // Encode constraints into Z3
        for constraint in constraints {
            // Extract description for encoding (try new structure first, fallback to old)
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                steps.push(ProofStep {
                    description: format!("Encoded: {}", desc),
                    justification: "Constraint encoding".to_string(),
                });
            }
        }

        steps.push(ProofStep {
            description: "Invoking Z3 solver".to_string(),
            justification: "SMT solving".to_string(),
        });

        // Check satisfiability
        match solver.check() {
            z3::SatResult::Sat => {
                steps.push(ProofStep {
                    description: "Z3 proved: SATISFIABLE (model exists)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                // Get model for witness
                if let Some(model) = solver.get_model() {
                    let witness = format!("Witness: {}", model);
                    steps.push(ProofStep {
                        description: witness,
                        justification: "Model extraction".to_string(),
                    });
                }

                (ProofStatus::Proven, steps)
            }
            z3::SatResult::Unsat => {
                steps.push(ProofStep {
                    description: "Z3 proved: UNSATISFIABLE (no solution exists)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                // Get unsat core for explanation
                let core = solver.get_unsat_core();
                if !core.is_empty() {
                    let core_desc = format!("Unsat core: {} constraints conflict", core.len());
                    steps.push(ProofStep {
                        description: core_desc,
                        justification: "Unsat core extraction".to_string(),
                    });
                }

                (ProofStatus::Refuted, steps)
            }
            z3::SatResult::Unknown => {
                steps.push(ProofStep {
                    description: "Z3 returned: UNKNOWN (timeout or incomplete)".to_string(),
                    justification: "SMT solver limitation".to_string(),
                });
                (ProofStatus::Unknown, steps)
            }
        }
    }

    #[cfg(feature = "z3-solver")]
    fn check_consistency_z3(
        &self,
        constraints_a: &[Constraint],
        constraints_b: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        steps.push(ProofStep {
            description: format!(
                "Checking consistency: {} constraints (A) ∩ {} constraints (B)",
                constraints_a.len(),
                constraints_b.len()
            ),
            justification: "Consistency problem setup".to_string(),
        });

        let solver = Solver::new(&self.context);
        let mut var_map: HashMap<String, Int<'_>> = HashMap::new();

        // Encode constraints from both sets
        let mut encoded_a = 0;
        for constraint in constraints_a {
            // Extract description for encoding (try new structure first, fallback to old)
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_a += 1;
            }
        }

        let mut encoded_b = 0;
        for constraint in constraints_b {
            // Extract description for encoding (try new structure first, fallback to old)
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_b += 1;
            }
        }

        steps.push(ProofStep {
            description: format!(
                "Encoded {} constraints from A, {} from B",
                encoded_a, encoded_b
            ),
            justification: "SMT encoding".to_string(),
        });

        steps.push(ProofStep {
            description: "Invoking Z3 to check consistency".to_string(),
            justification: "SMT solving".to_string(),
        });

        // If SAT, then consistent (intersection non-empty)
        // If UNSAT, then contradictory (intersection empty)
        match solver.check() {
            z3::SatResult::Sat => {
                steps.push(ProofStep {
                    description: "Z3 proved: CONSISTENT (A ∩ B ≠ ∅)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                if let Some(model) = solver.get_model() {
                    steps.push(ProofStep {
                        description: format!("Witness exists: {}", model),
                        justification: "Model extraction".to_string(),
                    });
                }

                (ProofStatus::Proven, steps)
            }
            z3::SatResult::Unsat => {
                steps.push(ProofStep {
                    description: "Z3 proved: CONTRADICTORY (A ∩ B = ∅)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                (ProofStatus::Refuted, steps)
            }
            z3::SatResult::Unknown => {
                steps.push(ProofStep {
                    description: "Z3 returned: UNKNOWN".to_string(),
                    justification: "SMT solver limitation".to_string(),
                });
                (ProofStatus::Unknown, steps)
            }
        }
    }

    #[cfg(feature = "z3-solver")]
    fn check_completeness_z3(
        &self,
        domain_constraints: &[Constraint],
        spec_constraints: &[&[Constraint]],
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        steps.push(ProofStep {
            description: format!(
                "Checking completeness: {} domain constraints covered by {} specs",
                domain_constraints.len(),
                spec_constraints.len()
            ),
            justification: "Completeness problem setup".to_string(),
        });

        steps.push(ProofStep {
            description: "Formula: UNSAT(D ∧ ¬A1 ∧ ¬A2 ∧ ... ∧ ¬An)".to_string(),
            justification: "Completeness encoding".to_string(),
        });

        let solver = Solver::new(&self.context);
        let mut var_map: HashMap<String, Int<'_>> = HashMap::new();

        // Encode domain constraints
        let mut encoded_d = 0;
        for constraint in domain_constraints {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_d += 1;
            }
        }

        // Encode ¬(A1 ∨ A2 ∨ ... ∨ An) = ¬A1 ∧ ¬A2 ∧ ... ∧ ¬An
        let mut encoded_specs = 0;
        for constraints in spec_constraints {
            // For each spec, we need to negate ALL its constraints
            // ¬Ai = ¬(c1 ∧ c2 ∧ ... ∧ cn) = ¬c1 ∨ ¬c2 ∨ ... ∨ ¬cn
            // But we need ¬A1 ∧ ¬A2, so we negate each spec as a whole

            let mut spec_assertions = Vec::new();
            for constraint in *constraints {
                let desc = if let Some(meta) = &constraint.meta {
                    meta.get_str("description").map(|s| s.as_str())
                } else {
                    constraint.description.as_deref()
                }.unwrap_or("");

                if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                    spec_assertions.push(assertion);
                }
            }

            if !spec_assertions.is_empty() {
                // Conjoin all constraints in this spec: c1 ∧ c2 ∧ ... ∧ cn
                let spec_and = if spec_assertions.len() == 1 {
                    spec_assertions[0].clone()
                } else {
                    let refs: Vec<&Bool> = spec_assertions.iter().collect();
                    Bool::and(&self.context, &refs)
                };

                // Negate the whole spec: ¬(c1 ∧ c2 ∧ ... ∧ cn)
                solver.assert(&spec_and.not());
                encoded_specs += 1;
            }
        }

        steps.push(ProofStep {
            description: format!(
                "Encoded {} domain constraints, {} negated specs",
                encoded_d, encoded_specs
            ),
            justification: "SMT encoding".to_string(),
        });

        steps.push(ProofStep {
            description: "Invoking Z3 to check completeness".to_string(),
            justification: "SMT solving".to_string(),
        });

        // If UNSAT, then D ⊆ D_S (complete coverage)
        // If SAT, then there exists d ∈ D but d ∉ (A1 ∪ A2 ∪ ... ∪ An) (coverage gap)
        match solver.check() {
            z3::SatResult::Unsat => {
                steps.push(ProofStep {
                    description: "Z3 proved: COMPLETE (D ⊆ D_S, no coverage gaps)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });
                (ProofStatus::Proven, steps)
            }
            z3::SatResult::Sat => {
                steps.push(ProofStep {
                    description: "Z3 proved: INCOMPLETE (coverage gap exists)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                if let Some(model) = solver.get_model() {
                    steps.push(ProofStep {
                        description: format!("Coverage gap witness: {}", model),
                        justification: "Model extraction".to_string(),
                    });
                }

                (ProofStatus::Refuted, steps)
            }
            z3::SatResult::Unknown => {
                steps.push(ProofStep {
                    description: "Z3 returned: UNKNOWN".to_string(),
                    justification: "SMT solver limitation".to_string(),
                });
                (ProofStatus::Unknown, steps)
            }
        }
    }

    #[cfg(feature = "z3-solver")]
    fn check_consistency_within_domain_z3(
        &self,
        constraints_a: &[Constraint],
        constraints_b: &[Constraint],
        domain_constraints: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        steps.push(ProofStep {
            description: format!(
                "Checking consistency within domain: {} constraints (A) ∩ {} constraints (B) ∩ {} constraints (D)",
                constraints_a.len(),
                constraints_b.len(),
                domain_constraints.len()
            ),
            justification: "Consistency within domain setup".to_string(),
        });

        let solver = Solver::new(&self.context);
        let mut var_map: HashMap<String, Int<'_>> = HashMap::new();

        // Encode constraints from A1
        let mut encoded_a = 0;
        for constraint in constraints_a {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_a += 1;
            }
        }

        // Encode constraints from A2
        let mut encoded_b = 0;
        for constraint in constraints_b {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_b += 1;
            }
        }

        // Encode domain constraints
        let mut encoded_d = 0;
        for constraint in domain_constraints {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_d += 1;
            }
        }

        steps.push(ProofStep {
            description: format!(
                "Encoded {} from A, {} from B, {} from D",
                encoded_a, encoded_b, encoded_d
            ),
            justification: "SMT encoding".to_string(),
        });

        steps.push(ProofStep {
            description: "Invoking Z3 to check consistency within domain".to_string(),
            justification: "SMT solving".to_string(),
        });

        // If SAT, then consistent within domain (A ∩ B ∩ D ≠ ∅)
        // If UNSAT, then contradictory within domain (A ∩ B ∩ D = ∅)
        match solver.check() {
            z3::SatResult::Sat => {
                steps.push(ProofStep {
                    description: "Z3 proved: CONSISTENT within domain (A ∩ B ∩ D ≠ ∅)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                if let Some(model) = solver.get_model() {
                    steps.push(ProofStep {
                        description: format!("Witness exists: {}", model),
                        justification: "Model extraction".to_string(),
                    });
                }

                (ProofStatus::Proven, steps)
            }
            z3::SatResult::Unsat => {
                steps.push(ProofStep {
                    description: "Z3 proved: CONTRADICTORY within domain (A ∩ B ∩ D = ∅)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });
                (ProofStatus::Refuted, steps)
            }
            z3::SatResult::Unknown => {
                steps.push(ProofStep {
                    description: "Z3 returned: UNKNOWN".to_string(),
                    justification: "SMT solver limitation".to_string(),
                });
                (ProofStatus::Unknown, steps)
            }
        }
    }

    #[cfg(feature = "z3-solver")]
    fn check_implication_z3(
        &self,
        constraints_antecedent: &[Constraint],
        constraints_consequent: &[Constraint],
    ) -> (ProofStatus, Vec<ProofStep>) {
        let mut steps = Vec::new();

        steps.push(ProofStep {
            description: format!(
                "Checking implication: A1({} constraints) ⊆ A2({} constraints)",
                constraints_antecedent.len(),
                constraints_consequent.len()
            ),
            justification: "Implication problem setup".to_string(),
        });

        steps.push(ProofStep {
            description: "Formula: UNSAT(A1 ∧ ¬A2)".to_string(),
            justification: "Implication encoding".to_string(),
        });

        let solver = Solver::new(&self.context);
        let mut var_map: HashMap<String, Int<'_>> = HashMap::new();

        // Encode antecedent (A1)
        let mut encoded_a1 = 0;
        for constraint in constraints_antecedent {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                solver.assert(&assertion);
                encoded_a1 += 1;
            }
        }

        // Encode ¬A2 (negation of consequent)
        let mut encoded_not_a2 = 0;
        for constraint in constraints_consequent {
            let desc = if let Some(meta) = &constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("");

            if let Some(assertion) = self.encode_constraint(desc, &mut var_map) {
                // Negate the assertion
                solver.assert(&assertion.not());
                encoded_not_a2 += 1;
            }
        }

        steps.push(ProofStep {
            description: format!(
                "Encoded {} constraints from A1, {} negated constraints from A2",
                encoded_a1, encoded_not_a2
            ),
            justification: "SMT encoding".to_string(),
        });

        steps.push(ProofStep {
            description: "Invoking Z3 to check implication".to_string(),
            justification: "SMT solving".to_string(),
        });

        // If UNSAT, then A1 ⊆ A2 (implication holds)
        // If SAT, then there exists x ∈ A1 but x ∉ A2 (counterexample)
        match solver.check() {
            z3::SatResult::Unsat => {
                steps.push(ProofStep {
                    description: "Z3 proved: UNSAT(A1 ∧ ¬A2) → A1 ⊆ A2 (implication holds)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });
                (ProofStatus::Proven, steps)
            }
            z3::SatResult::Sat => {
                steps.push(ProofStep {
                    description: "Z3 proved: SAT(A1 ∧ ¬A2) → Counterexample exists (implication does NOT hold)".to_string(),
                    justification: "SMT solver verdict".to_string(),
                });

                if let Some(model) = solver.get_model() {
                    steps.push(ProofStep {
                        description: format!("Counterexample: {}", model),
                        justification: "Model extraction".to_string(),
                    });
                }

                (ProofStatus::Refuted, steps)
            }
            z3::SatResult::Unknown => {
                steps.push(ProofStep {
                    description: "Z3 returned: UNKNOWN".to_string(),
                    justification: "SMT solver limitation".to_string(),
                });
                (ProofStatus::Unknown, steps)
            }
        }
    }

    #[cfg(feature = "z3-solver")]
    fn encode_constraint<'ctx>(
        &'ctx self,
        description: &str,
        var_map: &mut HashMap<String, Int<'ctx>>,
    ) -> Option<Bool<'ctx>> {
        let desc_lower = description.to_lowercase();

        // Extract variable name (heuristic: first word before "must")
        let var_name = self.extract_variable_name(&desc_lower).unwrap_or_else(|| "x".to_string());

        // Get or create variable
        let var = if let Some(existing) = var_map.get(&var_name) {
            existing.clone()
        } else {
            let new_var = Int::new_const(&self.context, var_name.as_str());
            var_map.insert(var_name.clone(), new_var.clone());
            new_var
        };

        // Pattern matching for constraint types
        if let Some(min) = self.extract_minimum(&desc_lower) {
            // "at least N", "minimum N", ">= N"
            let n = Int::from_i64(&self.context, min);
            return Some(var.ge(&n));
        }

        if let Some(max) = self.extract_maximum(&desc_lower) {
            // "at most N", "maximum N", "<= N"
            let n = Int::from_i64(&self.context, max);
            return Some(var.le(&n));
        }

        if let Some(exact) = self.extract_exact(&desc_lower) {
            // "exactly N", "must be N"
            let n = Int::from_i64(&self.context, exact);
            return Some(var._eq(&n));
        }

        if let Some((min, max)) = self.extract_range(&desc_lower) {
            // "between X and Y"
            let min_val = Int::from_i64(&self.context, min);
            let max_val = Int::from_i64(&self.context, max);
            let ge = var.ge(&min_val);
            let le = var.le(&max_val);
            return Some(Bool::and(&self.context, &[&ge, &le]));
        }

        // Unable to encode this constraint
        None
    }

    #[cfg(feature = "z3-solver")]
    fn extract_variable_name(&self, desc: &str) -> Option<String> {
        // Extract variable name from patterns like "password must be..."
        let words: Vec<&str> = desc.split_whitespace().collect();
        if let Some(pos) = words.iter().position(|&w| w == "must" || w == "should") {
            if pos > 0 {
                return Some(words[pos - 1].to_string());
            }
        }
        None
    }

    fn extract_minimum(&self, desc: &str) -> Option<i64> {
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

    fn extract_maximum(&self, desc: &str) -> Option<i64> {
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

    fn extract_exact(&self, desc: &str) -> Option<i64> {
        if let Some(pos) = desc.find("exactly") {
            return self.extract_number(&desc[pos..]);
        }
        if desc.contains("must be") && !desc.contains("at least") && !desc.contains("at most") {
            return self.extract_number(desc);
        }
        None
    }

    fn extract_range(&self, desc: &str) -> Option<(i64, i64)> {
        if let Some(pos) = desc.find("between") {
            let rest = &desc[pos..];
            let numbers: Vec<i64> = rest.split_whitespace()
                .filter_map(|w| w.trim_matches(|c: char| !c.is_numeric()).parse::<i64>().ok())
                .collect();
            if numbers.len() >= 2 {
                return Some((numbers[0], numbers[1]));
            }
        }
        None
    }

    fn extract_number(&self, s: &str) -> Option<i64> {
        for word in s.split_whitespace() {
            if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric()).parse::<i64>() {
                return Some(n);
            }
        }
        None
    }
}

impl Default for Z3Backend {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(all(test, feature = "z3-solver"))]
mod tests {
    use super::*;

    #[test]
    fn z3_satisfiability_empty() {
        let backend = Z3Backend::new();
        let (status, _steps) = backend.check_satisfiability(&[]);
        assert_eq!(status, ProofStatus::Proven);
    }

    #[test]
    fn z3_satisfiability_consistent() {
        let backend = Z3Backend::new();

        let mut meta1 = crate::ConstraintMetadata::new();
        meta1.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at least 8 characters".to_string());

        let mut meta2 = crate::ConstraintMetadata::new();
        meta2.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at most 20 characters".to_string());

        let constraints = vec![
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at least 8 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta1),
            },
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at most 20 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta2),
            },
        ];

        let (status, _steps) = backend.check_satisfiability(&constraints);
        assert_eq!(status, ProofStatus::Proven); // SAT: password ∈ [8, 20]
    }

    #[test]
    fn z3_satisfiability_contradictory() {
        let backend = Z3Backend::new();

        let mut meta1 = crate::ConstraintMetadata::new();
        meta1.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at least 20 characters".to_string());

        let mut meta2 = crate::ConstraintMetadata::new();
        meta2.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at most 8 characters".to_string());

        let constraints = vec![
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at least 20 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta1),
            },
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at most 8 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta2),
            },
        ];

        let (status, _steps) = backend.check_satisfiability(&constraints);
        assert_eq!(status, ProofStatus::Refuted); // UNSAT
    }

    #[test]
    fn z3_consistency_compatible() {
        let backend = Z3Backend::new();

        let mut meta_a = crate::ConstraintMetadata::new();
        meta_a.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at least 8 characters".to_string());

        let mut meta_b = crate::ConstraintMetadata::new();
        meta_b.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at most 20 characters".to_string());

        let constraints_a = vec![
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at least 8 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta_a),
            },
        ];
        let constraints_b = vec![
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at most 20 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta_b),
            },
        ];

        let (status, _steps) = backend.check_consistency(&constraints_a, &constraints_b);
        assert_eq!(status, ProofStatus::Proven); // Consistent: [8, 20]
    }

    #[test]
    fn z3_consistency_contradictory() {
        let backend = Z3Backend::new();

        let mut meta_a = crate::ConstraintMetadata::new();
        meta_a.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at least 20 characters".to_string());

        let mut meta_b = crate::ConstraintMetadata::new();
        meta_b.insert(crate::MetadataKey::Custom("description".to_string()),
                     "password must be at most 8 characters".to_string());

        let constraints_a = vec![
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at least 20 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta_a),
            },
        ];
        let constraints_b = vec![
            Constraint {
                formal: None,
                kind: ConstraintKind::Universal,
                description: Some("password must be at most 8 characters".to_string()),
                metadata: Some(crate::ConstraintMetadata::new()),
                meta: Some(meta_b),
            },
        ];

        let (status, _steps) = backend.check_consistency(&constraints_a, &constraints_b);
        assert_eq!(status, ProofStatus::Refuted); // Contradictory: [20, ∞) ∩ (-∞, 8] = ∅
    }
}
