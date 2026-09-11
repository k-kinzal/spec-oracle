//! spec-oracle daemon: evidence capture, persistence, and the gRPC service.
//!
//! The daemon accepts exactly one constrained-NL sentence per Add and persists
//! exactly one Specification Node. The raw words (plus the language version
//! that accepted them) are the immediate stored truth. Raw Evidence requests
//! are retained on that Node and a post-acceptance Consumer later appends captured
//! `meta.evidence` and content-addressed Evidence vertices. The assume-guarantee
//! *contract* is a derived reading of a sentence: assumption and guarantee are
//! roles an assertion plays relative to a responsible subject, and pairing a
//! guarantee with a non-trivial assumption is a graph-level relationship
//! between sentences. This crate validates and persists those explicit
//! source/relied/target pairings and materializes their current aggregate
//! Assumption; the trivial ingest projection remains immutable Ledger history.
//! Ingest projections are persisted as shared Assumption and Guarantee vertices. This crate owns everything that
//! touches the daemon's environment — Consumer-side Evidence interpretation,
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
//! manually asserted Evidence affirmation and denial. The daemon accepts only
//! this narrowly typed manual Evidence path; it does not accept generic manual
//! Specification-to-Specification selection Edges. The current-set view follows
//! signed Evidence paths without rewriting semantic Edges. Proved
//! non-trivial A/G pairing is likewise append-only and never rewrites authored
//! words or the target Guarantee.

pub mod add;
pub mod arango;
pub mod command_bus;
pub mod consumer;
pub mod contract_algebra;
pub mod convert;
pub mod domain;
pub mod event_bus;
pub mod event_sink;
pub mod evidence;
pub mod evidence_capture;
pub mod evidence_graph;
pub mod github;
pub mod graph_generation;
pub mod graph_query;
pub mod identity;
pub mod origin;
pub mod pairing;
pub mod selection;
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
