//! Universe module: The space in which specifications are defined

#[allow(clippy::module_inception)]
mod universe;
mod universe_id;
mod universe_metadata;

pub use universe::Universe;
pub use universe_id::UniverseId;
pub use universe_metadata::UniverseMetadata;
