/// Type-safe metadata system for UDAF model
///
/// This module provides strongly-typed metadata handling to prevent typos in metadata keys
/// and provide convenient accessors for common metadata fields.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Well-known metadata keys
///
/// This enum prevents typos and provides type-safe metadata access.
/// Custom keys can still be used via MetadataKey::Custom(String).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MetadataKey {
    /// Universe identifier (e.g., "U1", "U2")
    Universe,
    /// Source file path
    SourceFile,
    /// RPC method name
    RpcName,
    /// Extractor that produced this specification
    Extractor,
    /// Whether this was inferred (vs. manually written)
    Inferred,
    /// Variable name in code
    Variable,
    /// Implementation code snippet
    ImplCode,
    /// Test code snippet
    TestCode,
    /// Pattern that was matched
    Pattern,
    /// Specific value
    Value,
    /// Minimum constraint value
    Min,
    /// Maximum constraint value
    Max,
    /// Source of the specification
    Source,
    /// Custom key (for extensibility)
    Custom(String),
}

impl MetadataKey {
    /// Convert to string key for HashMap storage
    pub fn as_str(&self) -> &str {
        match self {
            MetadataKey::Universe => "universe",
            MetadataKey::SourceFile => "source_file",
            MetadataKey::RpcName => "rpc_name",
            MetadataKey::Extractor => "extractor",
            MetadataKey::Inferred => "inferred",
            MetadataKey::Variable => "variable",
            MetadataKey::ImplCode => "impl_code",
            MetadataKey::TestCode => "test_code",
            MetadataKey::Pattern => "pattern",
            MetadataKey::Value => "value",
            MetadataKey::Min => "min",
            MetadataKey::Max => "max",
            MetadataKey::Source => "source",
            MetadataKey::Custom(s) => s,
        }
    }

    /// Parse from string
    pub fn from_str(s: &str) -> Self {
        match s {
            "universe" => MetadataKey::Universe,
            "source_file" => MetadataKey::SourceFile,
            "rpc_name" => MetadataKey::RpcName,
            "extractor" => MetadataKey::Extractor,
            "inferred" => MetadataKey::Inferred,
            "variable" => MetadataKey::Variable,
            "impl_code" => MetadataKey::ImplCode,
            "test_code" => MetadataKey::TestCode,
            "pattern" => MetadataKey::Pattern,
            "value" => MetadataKey::Value,
            "min" => MetadataKey::Min,
            "max" => MetadataKey::Max,
            "source" => MetadataKey::Source,
            other => MetadataKey::Custom(other.to_string()),
        }
    }
}

impl From<&str> for MetadataKey {
    fn from(s: &str) -> Self {
        MetadataKey::from_str(s)
    }
}

impl From<String> for MetadataKey {
    fn from(s: String) -> Self {
        MetadataKey::from_str(&s)
    }
}

/// Generic metadata container
///
/// Internally stores HashMap<String, String> for serialization compatibility,
/// but provides type-safe access through MetadataKey.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Metadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl Metadata {
    /// Create empty metadata
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get value by metadata key
    pub fn get(&self, key: &MetadataKey) -> Option<&String> {
        self.inner.get(key.as_str())
    }

    /// Get value by string key (for compatibility)
    pub fn get_str(&self, key: &str) -> Option<&String> {
        self.inner.get(key)
    }

    /// Insert value with metadata key
    pub fn insert(&mut self, key: MetadataKey, value: String) -> Option<String> {
        self.inner.insert(key.as_str().to_string(), value)
    }

    /// Insert value with string key (for compatibility)
    pub fn insert_str(&mut self, key: String, value: String) -> Option<String> {
        self.inner.insert(key, value)
    }

    /// Remove value by metadata key
    pub fn remove(&mut self, key: &MetadataKey) -> Option<String> {
        self.inner.remove(key.as_str())
    }

    /// Check if key exists
    pub fn contains_key(&self, key: &MetadataKey) -> bool {
        self.inner.contains_key(key.as_str())
    }

    /// Get the inner HashMap (for direct access when needed)
    pub fn inner(&self) -> &HashMap<String, String> {
        &self.inner
    }

    /// Get mutable reference to inner HashMap
    pub fn inner_mut(&mut self) -> &mut HashMap<String, String> {
        &mut self.inner
    }
}

impl Default for Metadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for Metadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<Metadata> for HashMap<String, String> {
    fn from(metadata: Metadata) -> Self {
        metadata.inner
    }
}

/// Metadata for Universe with convenient accessors
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct UniverseMetadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl UniverseMetadata {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get source file (if this universe was extracted from a specific file)
    pub fn source_file(&self) -> Option<&String> {
        self.inner.get(MetadataKey::SourceFile.as_str())
    }

    /// Set source file
    pub fn set_source_file(&mut self, path: String) {
        self.inner.insert(MetadataKey::SourceFile.as_str().to_string(), path);
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

impl Default for UniverseMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for UniverseMetadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<UniverseMetadata> for HashMap<String, String> {
    fn from(metadata: UniverseMetadata) -> Self {
        metadata.inner
    }
}

/// Metadata for Domain with convenient accessors
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DomainMetadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl DomainMetadata {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get source specification
    pub fn source(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Source.as_str())
    }

    /// Set source specification
    pub fn set_source(&mut self, source: String) {
        self.inner.insert(MetadataKey::Source.as_str().to_string(), source);
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

impl Default for DomainMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for DomainMetadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<DomainMetadata> for HashMap<String, String> {
    fn from(metadata: DomainMetadata) -> Self {
        metadata.inner
    }
}

/// Metadata for Constraint with convenient accessors
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConstraintMetadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl ConstraintMetadata {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get pattern that was matched
    pub fn pattern(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Pattern.as_str())
    }

    /// Set pattern
    pub fn set_pattern(&mut self, pattern: String) {
        self.inner.insert(MetadataKey::Pattern.as_str().to_string(), pattern);
    }

    /// Get constraint value
    pub fn value(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Value.as_str())
    }

    /// Set constraint value
    pub fn set_value(&mut self, value: String) {
        self.inner.insert(MetadataKey::Value.as_str().to_string(), value);
    }

    /// Get minimum constraint value
    pub fn min(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Min.as_str())
    }

    /// Set minimum constraint value
    pub fn set_min(&mut self, min: String) {
        self.inner.insert(MetadataKey::Min.as_str().to_string(), min);
    }

    /// Get maximum constraint value
    pub fn max(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Max.as_str())
    }

    /// Set maximum constraint value
    pub fn set_max(&mut self, max: String) {
        self.inner.insert(MetadataKey::Max.as_str().to_string(), max);
    }

    /// Get source text
    pub fn source(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Source.as_str())
    }

    /// Set source text
    pub fn set_source(&mut self, source: String) {
        self.inner.insert(MetadataKey::Source.as_str().to_string(), source);
    }

    /// Generic get/insert for other metadata
    pub fn get(&self, key: &MetadataKey) -> Option<&String> {
        self.inner.get(key.as_str())
    }

    /// Get value by string key (for compatibility)
    pub fn get_str(&self, key: &str) -> Option<&String> {
        self.inner.get(key)
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

impl Default for ConstraintMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for ConstraintMetadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<ConstraintMetadata> for HashMap<String, String> {
    fn from(metadata: ConstraintMetadata) -> Self {
        metadata.inner
    }
}

/// Metadata for TransformFunction with convenient accessors
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransformMetadata {
    #[serde(flatten)]
    inner: HashMap<String, String>,
}

impl TransformMetadata {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Get extractor name (for AST analysis transforms)
    pub fn extractor(&self) -> Option<&String> {
        self.inner.get(MetadataKey::Extractor.as_str())
    }

    /// Set extractor name
    pub fn set_extractor(&mut self, extractor: String) {
        self.inner.insert(MetadataKey::Extractor.as_str().to_string(), extractor);
    }

    /// Get source file (for file-based transforms)
    pub fn source_file(&self) -> Option<&String> {
        self.inner.get(MetadataKey::SourceFile.as_str())
    }

    /// Set source file
    pub fn set_source_file(&mut self, path: String) {
        self.inner.insert(MetadataKey::SourceFile.as_str().to_string(), path);
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

impl Default for TransformMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashMap<String, String>> for TransformMetadata {
    fn from(map: HashMap<String, String>) -> Self {
        Self { inner: map }
    }
}

impl From<TransformMetadata> for HashMap<String, String> {
    fn from(metadata: TransformMetadata) -> Self {
        metadata.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metadata_key_as_str() {
        assert_eq!(MetadataKey::Universe.as_str(), "universe");
        assert_eq!(MetadataKey::SourceFile.as_str(), "source_file");
        assert_eq!(MetadataKey::Custom("foo".to_string()).as_str(), "foo");
    }

    #[test]
    fn test_metadata_key_from_str() {
        assert_eq!(MetadataKey::from_str("universe"), MetadataKey::Universe);
        assert_eq!(MetadataKey::from_str("source_file"), MetadataKey::SourceFile);
        assert_eq!(MetadataKey::from_str("unknown"), MetadataKey::Custom("unknown".to_string()));
    }

    #[test]
    fn test_metadata_insert_get() {
        let mut meta = Metadata::new();
        meta.insert(MetadataKey::Universe, "U1".to_string());
        assert_eq!(meta.get(&MetadataKey::Universe), Some(&"U1".to_string()));
    }

    #[test]
    fn test_constraint_metadata_accessors() {
        let mut meta = ConstraintMetadata::new();
        meta.set_pattern("at_least".to_string());
        meta.set_min("5".to_string());
        meta.set_max("10".to_string());

        assert_eq!(meta.pattern(), Some(&"at_least".to_string()));
        assert_eq!(meta.min(), Some(&"5".to_string()));
        assert_eq!(meta.max(), Some(&"10".to_string()));
    }

    #[test]
    fn test_metadata_serialization() {
        let mut meta = Metadata::new();
        meta.insert(MetadataKey::Universe, "U1".to_string());
        meta.insert(MetadataKey::Custom("custom_key".to_string()), "custom_value".to_string());

        let json = serde_json::to_string(&meta).unwrap();
        let deserialized: Metadata = serde_json::from_str(&json).unwrap();

        assert_eq!(deserialized.get(&MetadataKey::Universe), Some(&"U1".to_string()));
        assert_eq!(deserialized.get(&MetadataKey::Custom("custom_key".to_string())), Some(&"custom_value".to_string()));
    }
}
