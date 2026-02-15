/// Proof module: Formal verification mechanisms
///
/// This module provides the "proven world" that is the essence of specORACLE.
/// Unlike heuristic verification, the prover provides mathematical guarantees
/// about specifications.
///
/// From motivation.md:
/// > specORACLEは、「証明された世界」を提供することが本質である
/// > "The essence of specORACLE is to provide a 'proven world'"
///
/// Current implementation: Z3 SMT solver (complete formal verification)
/// Fallback: Lightweight constraint solver (when Z3 unavailable)
mod types;
mod z3_backend;

#[cfg(feature = "z3-solver")]
mod prover;

// Re-export all types
pub use types::{Proof, Property, ProofMethod, ProofStatus, ProofStep};

#[cfg(feature = "z3-solver")]
pub use prover::{Prover, UnderspecificationReport};
