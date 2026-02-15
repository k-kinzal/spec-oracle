//! Metadata module: Shared metadata infrastructure

mod metadata_key;
#[allow(clippy::module_inception)]
mod metadata;

pub use metadata_key::MetadataKey;
pub use metadata::Metadata;
