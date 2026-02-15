//! Model module: The complete UDAF model orchestrator

#[allow(clippy::module_inception)]
mod model;
mod serde_helpers;
pub mod constraint;
pub mod sync;  // Replaced populate.rs

#[cfg(feature = "z3-solver")]
pub mod verify;

pub use model::UDAFModel;
pub use sync::ModelSync;

#[cfg(feature = "z3-solver")]
pub use verify::{Contradiction, Omission, LayerInconsistency, InterUniverseInconsistency};
