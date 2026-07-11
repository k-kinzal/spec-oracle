//! spec-oracle daemon: evidence capture, persistence, and the gRPC service.
//!
//! The daemon ingests a *specification* — one or more sentences of the
//! constrained specification language — and persists one node per sentence.
//! A node is a grounded sentence: the raw words (plus the language version
//! that accepted them) are the stored truth, and the `meta.evidence` captured
//! here grounds the claim. The assume-guarantee *contract* is a derived
//! reading of a sentence, not a stored fact: assumption and guarantee are
//! roles an assertion plays relative to a responsible subject, and pairing a
//! guarantee with a non-trivial assumption is a graph-level relationship
//! between sentences — out of scope here. This crate owns everything that
//! touches the daemon's environment — parsing evidence values, snapshotting
//! the locator's content, discovering source provenance, and persisting to
//! ArangoDB + a blob store — and exposes it over the `spec_oracle.v1` wire
//! contract via [`service`].
//!
//! The daemon owns the domain model. The wire contract lives separately in
//! `so-protocol` so clients can talk to the daemon without depending on this
//! crate. Edges (refinement, composition, conjunction), strength computation,
//! and classification are deliberately out of scope.

pub mod add;
pub mod add_mailbox;
pub mod arango;
pub mod convert;
pub mod domain;
pub mod evidence;
pub mod github;
pub mod jobs;
pub mod mailbox;
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
