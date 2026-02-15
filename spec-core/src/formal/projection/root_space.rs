//! RootSpace (Ω): The root space from which projections originate
//!
//! Ω represents the collected evidence space - the set of artifacts, traces,
//! and observations from which U0 (root specification) is constructed via
//! inverse mappings.
//!
//! ## 3-Layer Structure
//! - Layer 1: Identifier (`id`) - RootSpaceId (UUID-based)
//! - Layer 2: Proof Data (`proof_data`) - snapshot integrity, trace provenance
//! - Layer 3: Metadata (`meta`) - kind, snapshot_time, version, human-readable info

use crate::formal::{IdError, MetadataKey};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
use std::fmt;
use uuid::Uuid;

// =============================================================================
// Layer 1: RootSpaceId
// =============================================================================

/// Unique identifier for a RootSpace (UUID-based)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RootSpaceId(String);

impl RootSpaceId {
    /// Create a new RootSpace ID (generates UUID)
    pub fn new() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    /// Parse from string (validates UUID format)
    pub fn parse(s: &str) -> Result<Self, IdError> {
        Uuid::parse_str(s)
            .map_err(|_| IdError::InvalidUuid(format!("Invalid UUID for RootSpaceId: {}", s)))?;
        Ok(Self(s.to_string()))
    }

    /// Get the string representation
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for RootSpaceId {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for RootSpaceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for RootSpaceId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for RootSpaceId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        RootSpaceId::parse(&s).map_err(serde::de::Error::custom)
    }
}

// =============================================================================
// Layer 2: RootSpaceProofData
// =============================================================================

/// Proof-essential data for RootSpace
///
/// Contains only the data needed for formal verification and proofs.
/// The Prover should only access this layer, never metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RootSpaceProofData {
    /// Number of artifacts/traces contained in this root space
    pub artifact_count: usize,

    /// Source universe IDs that contributed to this root space
    pub source_universes: Vec<String>,
}

impl RootSpaceProofData {
    pub fn new() -> Self {
        Self {
            artifact_count: 0,
            source_universes: Vec::new(),
        }
    }

    /// Record a source universe contribution
    pub fn add_source_universe(&mut self, universe_id: String) {
        if !self.source_universes.contains(&universe_id) {
            self.source_universes.push(universe_id);
        }
    }

    /// Check if this root space has any source evidence
    pub fn has_sources(&self) -> bool {
        !self.source_universes.is_empty()
    }
}

impl Default for RootSpaceProofData {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Layer 3: RootSpaceMetadata
// =============================================================================

/// Metadata for RootSpace with convenient accessors
///
/// Uses HashMap<String, String> internally for serialization compatibility,
/// with typed accessors for well-known keys (kind, snapshot_time, version).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RootSpaceMetadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl RootSpaceMetadata {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get the kind of this root space
    pub fn kind(&self) -> Option<RootSpaceKind> {
        self.inner.get("kind").and_then(|s| match s.as_str() {
            "artifact_bundle" => Some(RootSpaceKind::ArtifactBundle),
            "trace" => Some(RootSpaceKind::Trace),
            _ => None,
        })
    }

    /// Set the kind of this root space
    pub fn set_kind(&mut self, kind: RootSpaceKind) {
        self.inner
            .insert("kind".to_string(), kind.as_str().to_string());
    }

    /// Get the snapshot timestamp
    pub fn snapshot_time(&self) -> Option<&String> {
        self.inner.get("snapshot_time")
    }

    /// Set the snapshot timestamp
    pub fn set_snapshot_time(&mut self, time: String) {
        self.inner.insert("snapshot_time".to_string(), time);
    }

    /// Get the version
    pub fn version(&self) -> Option<&String> {
        self.inner.get("version")
    }

    /// Set the version
    pub fn set_version(&mut self, version: String) {
        self.inner.insert("version".to_string(), version);
    }

    /// Generic get/insert for other metadata
    pub fn get(&self, key: &MetadataKey) -> Option<&String> {
        self.inner.get(key.as_str())
    }

    pub fn insert(&mut self, key: MetadataKey, value: String) {
        self.inner.insert(key.as_str().to_string(), value);
    }

    pub fn inner(&self) -> &HashMap<String, String> {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut HashMap<String, String> {
        &mut self.inner
    }
}

impl Default for RootSpaceMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for RootSpaceMetadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<RootSpaceMetadata> for HashMap<String, String> {
    fn from(metadata: RootSpaceMetadata) -> Self {
        metadata.inner
    }
}

// =============================================================================
// RootSpaceKind
// =============================================================================

/// The kind of root space
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RootSpaceKind {
    /// A bundle of artifacts (code, tests, docs, protos, contracts, types)
    /// collected at a point in time for inverse mapping
    ArtifactBundle,

    /// A trace of system behavior (execution logs, test results, runtime observations)
    /// used for behavioral inference
    Trace,
}

impl RootSpaceKind {
    pub fn as_str(&self) -> &str {
        match self {
            RootSpaceKind::ArtifactBundle => "artifact_bundle",
            RootSpaceKind::Trace => "trace",
        }
    }
}

impl fmt::Display for RootSpaceKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

// =============================================================================
// RootSpace (Ω)
// =============================================================================

/// RootSpace (Ω): The evidence space from which U0 is constructed
///
/// ## 3-Layer Structure
/// - Layer 1: `id` - Unique identifier (RootSpaceId)
/// - Layer 2: `proof_data` - Proof-essential data (artifact count, source universes)
/// - Layer 3: `meta` - Metadata (kind, snapshot_time, version, human-readable info)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RootSpace {
    /// Layer 1: Unique identifier for this root space
    pub id: RootSpaceId,

    /// Layer 2: Proof-essential data
    pub proof_data: RootSpaceProofData,

    /// Layer 3: Metadata (kind, snapshot_time, version, etc.)
    pub meta: RootSpaceMetadata,
}

impl RootSpace {
    /// Create a new RootSpace as an artifact bundle
    ///
    /// An artifact bundle collects code, tests, docs, protos, contracts, and types
    /// at a point in time for inverse mapping to U0.
    pub fn new_artifact_bundle() -> Self {
        let mut meta = RootSpaceMetadata::new();
        meta.set_kind(RootSpaceKind::ArtifactBundle);

        Self {
            id: RootSpaceId::new(),
            proof_data: RootSpaceProofData::new(),
            meta,
        }
    }

    /// Create a new RootSpace as a trace
    ///
    /// A trace captures system behavior (execution logs, test results, runtime
    /// observations) for behavioral inference toward U0.
    pub fn new_trace() -> Self {
        let mut meta = RootSpaceMetadata::new();
        meta.set_kind(RootSpaceKind::Trace);

        Self {
            id: RootSpaceId::new(),
            proof_data: RootSpaceProofData::new(),
            meta,
        }
    }

    /// Get the kind of this root space from metadata
    pub fn kind(&self) -> Option<RootSpaceKind> {
        self.meta.kind()
    }

    /// Get the snapshot timestamp from metadata
    pub fn snapshot_time(&self) -> Option<&String> {
        self.meta.snapshot_time()
    }

    /// Get the version from metadata
    pub fn version(&self) -> Option<&String> {
        self.meta.version()
    }

    /// Get proof data (for Prover access)
    pub fn get_proof_data(&self) -> &RootSpaceProofData {
        &self.proof_data
    }

    /// Get mutable proof data
    pub fn get_proof_data_mut(&mut self) -> &mut RootSpaceProofData {
        &mut self.proof_data
    }
}
