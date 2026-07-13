//! A written term form shared by specification sentences.
//!
//! A term-form node records lexical incidence, not referent identity. Two
//! specifications connected to `stop command` are known to use the same
//! normalized words; the node does not claim that both occurrences denote the
//! same runtime object. Definitions and future identity analysis may add that
//! stronger structure separately.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TermNode {
    pub id: String,
    /// Determiner-free, canonical, lower-cased noun phrase.
    pub form: String,
    pub head: String,
    pub lang_version: String,
    pub derivation_version: String,
}
