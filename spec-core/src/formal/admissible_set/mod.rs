//! AdmissibleSet module: The set of implementations allowed by a specification

mod admissible_set;
mod spec_id;
mod spec_set;
mod admissible_set_metadata;

pub use admissible_set::{AdmissibleSet, AdmissibleSetProofData, AdmissibleSetMetadata};
pub use spec_id::SpecId;
pub use spec_set::SpecSet;
