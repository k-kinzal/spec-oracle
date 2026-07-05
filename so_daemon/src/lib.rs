//! spec-oracle daemon: evidence capture, persistence, and the gRPC service.
//!
//! A node is a contract `(assumption ⇒ guarantee)` that is also a grounded
//! claim. The contract is projected mechanically from a constrained
//! natural-language `statement` (by the language crate); the grounding is
//! captured here as evidence. This crate owns everything that touches the
//! daemon's environment — parsing evidence values, snapshotting the locator's
//! content, discovering source provenance, and persisting to ArangoDB + a blob
//! store — and exposes it over the `spec_oracle.v1` contract via [`service`].
//!
//! The daemon owns the domain model. The wire contract lives separately in
//! `so-protocol` so clients can talk to the daemon without depending on this
//! crate. Edges (refinement, composition, conjunction), strength computation,
//! and classification are deliberately out of scope.

pub mod add;
pub mod arango;
pub mod convert;
pub mod domain;
pub mod evidence;
pub mod origin;
pub mod service;
pub mod snapshot;
pub mod store;

pub use convert::ConvertError;

/// Re-export of the [`inventory`] crate so a plugin can register an
/// [`origin::EnricherRegistration`] via `so_daemon::inventory::submit!`
/// without adding `inventory` to its own manifest. This guarantees the plugin
/// submits into the *same* registry this crate collects from: depending on
/// `inventory` directly at an incompatible version would be a compile error, not
/// a silent no-op, but re-exporting removes that hazard entirely.
pub use inventory;
