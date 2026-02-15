//! Transform module: Mappings between universes

#[allow(clippy::module_inception)]
mod transform;
mod transform_id;
mod transform_metadata;

#[allow(deprecated)]
pub use transform::{TransformFunction, TransformKind, TransformStrategy, ProjectionStrategy, ObserverKind};
pub use transform_id::TransformId;
pub use transform_metadata::TransformMetadata;
