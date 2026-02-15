/// Artifact Space (Γ_i): A concrete artifact from which specifications are extracted
///
/// An artifact space represents a single source artifact (code file, test file,
/// API spec, documentation, etc.) that participates in reverse mappings to U0.
///
/// ## 3-Layer Structure
/// - Layer 1: Identifier (`id`) - unique identity for referencing
/// - Layer 2: Proof Data (none currently - artifact spaces are inputs, not proof targets)
/// - Layer 3: Metadata (`meta`) - kind, content, source location, human-readable info
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use uuid::Uuid;

use crate::formal::{IdError, MetadataKey};

/// The kind of artifact this space represents
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArtifactKind {
    /// Natural language requirements document
    RequirementsDoc,
    /// API specification (OpenAPI, gRPC proto, etc.)
    APISpec,
    /// Source code implementation
    SourceCode,
    /// Test code (unit, integration, E2E, property-based)
    TestCode,
    /// Type definitions (TypeScript .d.ts, Rust trait, etc.)
    TypeDefinitions,
    /// Formal specification (TLA+, Alloy, Lean4, etc.)
    FormalSpec,
}

impl fmt::Display for ArtifactKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArtifactKind::RequirementsDoc => write!(f, "requirements_doc"),
            ArtifactKind::APISpec => write!(f, "api_spec"),
            ArtifactKind::SourceCode => write!(f, "source_code"),
            ArtifactKind::TestCode => write!(f, "test_code"),
            ArtifactKind::TypeDefinitions => write!(f, "type_definitions"),
            ArtifactKind::FormalSpec => write!(f, "formal_spec"),
        }
    }
}

/// Layer 1: Artifact space identifier (UUID-based)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArtifactSpaceId(String);

impl ArtifactSpaceId {
    /// Create a new artifact space ID (generates UUID)
    pub fn new() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    /// Parse from string (validates UUID format)
    pub fn parse(s: &str) -> Result<Self, IdError> {
        Uuid::parse_str(s).map_err(|_| {
            IdError::InvalidUuid(format!("Invalid UUID for ArtifactSpaceId: {}", s))
        })?;
        Ok(Self(s.to_string()))
    }

    /// Get the string representation
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for ArtifactSpaceId {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for ArtifactSpaceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for ArtifactSpaceId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for ArtifactSpaceId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        ArtifactSpaceId::parse(&s).map_err(serde::de::Error::custom)
    }
}

/// Layer 3: Metadata for ArtifactSpace
///
/// Contains human-readable and organizational information about the artifact.
/// Uses HashMap<String, String> for extensibility, with typed accessors for
/// well-known keys.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ArtifactSpaceMetadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl ArtifactSpaceMetadata {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get the artifact kind
    pub fn kind(&self) -> Option<ArtifactKind> {
        self.inner
            .get("artifact_kind")
            .and_then(|s| match s.as_str() {
                "requirements_doc" => Some(ArtifactKind::RequirementsDoc),
                "api_spec" => Some(ArtifactKind::APISpec),
                "source_code" => Some(ArtifactKind::SourceCode),
                "test_code" => Some(ArtifactKind::TestCode),
                "type_definitions" => Some(ArtifactKind::TypeDefinitions),
                "formal_spec" => Some(ArtifactKind::FormalSpec),
                _ => None,
            })
    }

    /// Set the artifact kind
    pub fn set_kind(&mut self, kind: ArtifactKind) {
        self.inner
            .insert("artifact_kind".to_string(), kind.to_string());
    }

    /// Get the content type (e.g., "text", "file_path", "structured")
    pub fn content_type(&self) -> Option<&String> {
        self.inner.get("content_type")
    }

    /// Set the content type
    pub fn set_content_type(&mut self, content_type: String) {
        self.inner.insert("content_type".to_string(), content_type);
    }

    /// Get the content value (the actual artifact content or path)
    pub fn content_value(&self) -> Option<&String> {
        self.inner.get("content_value")
    }

    /// Set the content value
    pub fn set_content_value(&mut self, content_value: String) {
        self.inner
            .insert("content_value".to_string(), content_value);
    }

    /// Get the source location (file path, URL, etc.)
    pub fn source(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Source.as_str())
    }

    /// Set the source location
    pub fn set_source(&mut self, source: String) {
        self.inner
            .insert(MetadataKey::Source.as_str().to_string(), source);
    }

    /// Generic get by MetadataKey
    pub fn get(&self, key: &MetadataKey) -> Option<&String> {
        self.inner.get(key.as_str())
    }

    /// Generic insert by MetadataKey
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

impl Default for ArtifactSpaceMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for ArtifactSpaceMetadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<ArtifactSpaceMetadata> for HashMap<String, String> {
    fn from(metadata: ArtifactSpaceMetadata) -> Self {
        metadata.inner
    }
}

/// Artifact Space (Γ_i): A source artifact for reverse mapping
///
/// Represents a concrete artifact (code, tests, docs, proto, etc.) from which
/// specifications are extracted via inverse mappings f₀ᵢ⁻¹.
///
/// ## 3-Layer Structure
/// - Layer 1: `id` (ArtifactSpaceId)
/// - Layer 2: (no proof data - artifacts are inputs, not verification targets)
/// - Layer 3: `meta` (ArtifactSpaceMetadata)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArtifactSpace {
    /// Layer 1: Unique identifier
    pub id: ArtifactSpaceId,

    /// Layer 3: Metadata (kind, content, source, etc.)
    pub meta: ArtifactSpaceMetadata,
}

impl ArtifactSpace {
    /// Create an artifact space from inline text content
    pub fn from_text(kind: ArtifactKind, content: String, source: String) -> Self {
        let mut meta = ArtifactSpaceMetadata::new();
        meta.set_kind(kind);
        meta.set_content_type("text".to_string());
        meta.set_content_value(content);
        meta.set_source(source);

        Self {
            id: ArtifactSpaceId::new(),
            meta,
        }
    }

    /// Create an artifact space referencing a file path
    pub fn from_file(kind: ArtifactKind, file_path: String) -> Self {
        let mut meta = ArtifactSpaceMetadata::new();
        meta.set_kind(kind);
        meta.set_content_type("file_path".to_string());
        meta.set_content_value(file_path.clone());
        meta.set_source(file_path);

        Self {
            id: ArtifactSpaceId::new(),
            meta,
        }
    }

    /// Create an artifact space from structured data (e.g., parsed AST, proto schema)
    pub fn from_structured(kind: ArtifactKind, data: String, source: String) -> Self {
        let mut meta = ArtifactSpaceMetadata::new();
        meta.set_kind(kind);
        meta.set_content_type("structured".to_string());
        meta.set_content_value(data);
        meta.set_source(source);

        Self {
            id: ArtifactSpaceId::new(),
            meta,
        }
    }

    /// Read the text content of this artifact (if content_type is "text")
    ///
    /// Returns None if the content type is not "text" or if no content is stored.
    pub fn as_text(&self) -> Option<&String> {
        match self.meta.content_type().map(|s| s.as_str()) {
            Some("text") => self.meta.content_value(),
            _ => None,
        }
    }

    /// Get the artifact kind
    pub fn kind(&self) -> Option<ArtifactKind> {
        self.meta.kind()
    }

    /// Get the source location
    pub fn source(&self) -> Option<&String> {
        self.meta.source()
    }
}
