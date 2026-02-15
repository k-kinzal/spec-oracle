//! Domain module: The region that a specification actually covers

#[allow(clippy::module_inception)]
mod domain;
mod domain_id;
mod domain_metadata;
mod domain_set;

pub use domain::{Domain, DomainProofData};
pub use domain_id::DomainId;
pub use domain_metadata::DomainMetadata;
pub use domain_set::DomainSet;
