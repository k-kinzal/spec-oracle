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
    /// Normalized lexical atoms used only for relation-candidate discovery.
    ///
    /// These atoms do not assert referent identity and do not become graph
    /// vertices. Requiring multiple shared atoms lets discovery bridge surface
    /// variants such as `AddSpecification` and `Add Specification` without
    /// turning that heuristic into a semantic Edge.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub discovery_tokens: Vec<String>,
    pub lang_version: String,
    pub derivation_version: String,
}
