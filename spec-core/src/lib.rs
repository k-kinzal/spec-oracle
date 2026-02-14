pub mod graph;
pub mod store;

pub use graph::{NodeKind, EdgeKind, SpecGraph, SpecNodeData, SpecEdgeData};
pub use graph::{Contradiction, Omission, LayerInconsistency};
pub use store::FileStore;
