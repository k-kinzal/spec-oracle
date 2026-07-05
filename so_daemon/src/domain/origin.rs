//! The finalized source provenance (sense ①: the source artifact's own claim).
//!
//! Distinct from our snapshot (sense ②), origin is a claim *by the source* about
//! who authored it and when. Discovering it (git log, HTML meta tags, …) is
//! daemon-side capture behavior; the resolved [`Origin`] value that ends up on
//! the node is what lives here.

use serde::{Deserialize, Serialize};

/// The finalized source provenance stored on an evidence entry. Every field is
/// optional — a field nobody could supply stays `None`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Origin {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub author: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub created_at: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_at: Option<String>,
}

impl Origin {
    /// Whether every field is empty (used to omit origin from serialized nodes).
    pub fn is_empty(&self) -> bool {
        self.author.is_none() && self.created_at.is_none() && self.updated_at.is_none()
    }
}
