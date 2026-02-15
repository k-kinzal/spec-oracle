//! Formal verification layer: The UDA/f space
//!
//! This module contains the formal specification model based on the UDA/f framework:
//! - U (Universe): The space in which specifications are defined
//! - D (Domain): The region that a specification actually covers
//! - A (Admissible Set): The set of implementations allowed by a specification
//! - f (Transform Functions): Mappings between universes

pub mod error;
pub mod universe;
pub mod domain;
pub mod admissible_set;
pub mod constraint;
pub mod transform;
pub mod metadata;
pub mod model;
pub mod proof;

// Re-export main types for convenience
pub use error::IdError;
pub use universe::{Universe, UniverseId, UniverseMetadata};
pub use domain::{Domain, DomainId, DomainMetadata, DomainSet, DomainProofData};
pub use admissible_set::{AdmissibleSet, AdmissibleSetProofData, AdmissibleSetMetadata, SpecId, SpecSet};
pub use constraint::{Constraint, ConstraintKind, ConstraintMetadata};
pub use transform::{TransformFunction, TransformId, TransformKind, TransformStrategy, TransformMetadata};
pub use metadata::{Metadata, MetadataKey};

// Re-export model and proof types
pub use model::UDAFModel;
pub use proof::{Proof, Property, ProofMethod, ProofStatus, ProofStep};
#[cfg(feature = "z3-solver")]
pub use proof::{Prover, UnderspecificationReport};
