//! The snapshot data type (provenance sense ②: our own observation).
//!
//! This module holds only the *shape* of a captured observation. The act of
//! capturing — reading a file's cited region, pinning the git commit, fetching a
//! URL — reads the local environment and is therefore daemon-side. The protocol
//! crate carries only the generated wire mirror.

use serde::{Deserialize, Serialize};

/// What the snapshot was pinned against.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Anchor {
    /// A file captured inside a git repository.
    Git {
        commit: String,
        /// The working tree had uncommitted changes to this path at capture time.
        dirty: bool,
    },
    /// A file not under version control.
    Worktree,
    /// A fetched web resource.
    Web {
        retrieved_at: String,
        status: u16,
        #[serde(skip_serializing_if = "Option::is_none")]
        content_type: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        last_modified: Option<String>,
    },
}

/// A captured, hashed observation of a locator's content.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Snapshot {
    /// The captured text (a file's cited region, or a URL body). Held in memory
    /// for the duration of an ingest, but **not persisted** and **not sent on the
    /// wire**: the bytes live in the content-addressed blob store keyed by
    /// `content_hash`, which is the authority. A node fetched back from storage
    /// (or received by a client) therefore has an empty `content` — read the blob
    /// to recover it.
    #[serde(skip)]
    pub content: String,
    /// SHA-256 (hex) of the raw captured bytes — the blob store key.
    pub content_hash: String,
    /// Length of the raw captured bytes.
    pub bytes: usize,
    /// When we captured it (RFC 3339, UTC).
    pub captured_at: String,
    pub anchor: Anchor,
}
