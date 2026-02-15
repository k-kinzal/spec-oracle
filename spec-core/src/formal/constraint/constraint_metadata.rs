/// Metadata for Constraint with convenient accessors

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::formal::MetadataKey;

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
