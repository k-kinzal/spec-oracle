//! spec-oracle daemon: evidence capture, persistence, and the gRPC service.
//!
//! The daemon accepts exactly one constrained-NL sentence per Add and persists
//! exactly one Specification Node. The raw words (plus the language version
//! that accepted them) are the immediate stored truth. Raw Evidence requests
//! are retained on that Node and a post-acceptance Job later appends captured
//! `meta.evidence`. The assume-guarantee *contract* is a derived
//! reading of a sentence, not a stored fact: assumption and guarantee are
//! roles an assertion plays relative to a responsible subject, and pairing a
//! guarantee with a non-trivial assumption is a graph-level relationship
//! between sentences — out of scope here. This crate owns everything that
//! touches the daemon's environment — Job-side Evidence interpretation,
//! snapshotting the locator's content, discovering source provenance, and persisting to
//! ArangoDB + a blob store — and exposes it over the `spec_oracle.v1` wire
//! contract via [`service`].
//!
//! The daemon owns the domain model. The wire contract lives separately in
//! `so-protocol` so clients can talk to the daemon without depending on this
//! crate. Its graph generation persists exact term mentions and the first
//! graph-established semantic Edge family (refinement, equivalence, and
//! force-aware conflicts) from `so-reason`'s conservative assessment. Edge
//! families and endpoint roles keep those semantic relations distinct from
//! versioned selection judgments such as support, defeat, and supersession.
//! A/G pairing, composition, and the selection policy that could produce such
//! judgments remain out of scope.

pub mod add;
pub mod add_mailbox;
pub mod arango;
pub mod convert;
pub mod domain;
pub mod evidence;
pub mod evidence_capture;
pub mod github;
pub mod graph_generation;
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
