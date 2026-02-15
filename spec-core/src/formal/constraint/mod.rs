//! Constraint module: Symbolic representations of membership conditions

mod constraint;
mod constraint_metadata;

pub use constraint::{Constraint, ConstraintKind};
pub use constraint_metadata::ConstraintMetadata;
