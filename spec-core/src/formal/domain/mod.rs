//! Domain module: The region that a specification actually covers

mod domain;
mod domain_id;
mod domain_metadata;
mod domain_set;

pub use domain::{Domain, DomainProofData};
pub use domain_id::DomainId;
pub use domain_metadata::DomainMetadata;
pub use domain_set::DomainSet;
