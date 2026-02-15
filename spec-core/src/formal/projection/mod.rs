//! Projection layer following paper §2.6
//!
//! This module implements the projection composition:
//!   proj_i = obs_i >> extract_i
//!
//! Where:
//! - obs_i: Ω → Option Γ_i (observer: root space to artifact space)
//! - extract_i: Γ_i → Option β_i (extractor: artifact space to IR)
//! - proj_i: the composition
//!
//! ## Types
//!
//! - **RootSpace (Ω)**: The foundational space from which projections are derived
//!   - RootSpaceKind::Trace: Behavioral trace observation
//!   - RootSpaceKind::ArtifactBundle: Static artifact bundle (PoC default)
//!
//! - **ArtifactSpace (Γ_i)**: Layer-specific artifact representation
//!   - ArtifactKind: RequirementsDoc, APISpec, SourceCode, TestCode, etc.
//!
//! - **Observer (obs_i)**: Transforms root space to artifact space
//!   - ArtifactBundleObserver: for artifact bundles
//!   - TraceObserver: for behavioral traces
//!   - FileSystemObserver: for direct file access
//!
//! - **Extractor (extract_i)**: Transforms artifact space to typed IR
//!   - Generic trait Extractor<T>
//!   - Implementations in extract.rs (RustExtractor, etc.)
//!
//! - **Projection**: Composes observer and extractor
//!   - Projection<O, E> where O: Observer, E: Extractor<T>

pub mod root_space;
pub mod artifact_space;
pub mod observer;
pub mod projection;

// Re-export key types for convenience
pub use root_space::{RootSpace, RootSpaceKind, RootSpaceId, RootSpaceMetadata, RootSpaceProofData};
pub use artifact_space::{ArtifactSpace, ArtifactKind, ArtifactSpaceId, ArtifactSpaceMetadata};
pub use observer::{Observer, ArtifactBundleObserver, TraceObserver, FileSystemObserver};
pub use projection::{Projection, Extractor};
