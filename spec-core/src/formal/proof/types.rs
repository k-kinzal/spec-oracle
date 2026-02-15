/// Proof types: Core types for formal verification
///
/// This module defines the fundamental types for representing proofs
/// and properties in the specORACLE verification system.
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
