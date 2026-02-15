/// Metadata for Domain with convenient accessors
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::formal::MetadataKey;

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
