/// Metadata for Universe with convenient accessors
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::formal::MetadataKey;

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
