/// Metadata for TransformFunction with convenient accessors
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::formal::MetadataKey;

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
