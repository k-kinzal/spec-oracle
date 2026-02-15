/// Generic metadata container
///
/// Internally stores HashMap<String, String> for serialization compatibility,
/// but provides type-safe access through MetadataKey.
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use super::MetadataKey;

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
