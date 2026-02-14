use crate::graph::SpecGraph;
use std::path::{Path, PathBuf};

#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Serialization error: {0}")]
    Serde(#[from] serde_json::Error),
}

/// File-based persistence for the specification graph.
pub struct FileStore {
    path: PathBuf,
}

impl FileStore {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
        }
    }

    pub fn load(&self) -> Result<SpecGraph, StoreError> {
        if !self.path.exists() {
            return Ok(SpecGraph::new());
        }
        let data = std::fs::read_to_string(&self.path)?;
        let mut graph: SpecGraph = serde_json::from_str(&data)?;
        graph.rebuild_indices();
        Ok(graph)
    }

    pub fn save(&self, graph: &SpecGraph) -> Result<(), StoreError> {
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let data = serde_json::to_string_pretty(graph)?;
        std::fs::write(&self.path, data)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeKind;
    use std::collections::HashMap;

    #[test]
    fn save_and_load_roundtrip() {
        let dir = std::env::temp_dir().join(format!("spec_oracle_test_{}", uuid::Uuid::new_v4()));
        let store = FileStore::new(dir.join("specs.json"));

        let mut graph = SpecGraph::new();
        graph.add_node("test node".into(), NodeKind::Assertion, HashMap::new());

        store.save(&graph).unwrap();
        let loaded = store.load().unwrap();
        assert_eq!(loaded.node_count(), 1);

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn load_nonexistent_returns_empty() {
        let store = FileStore::new("/tmp/nonexistent_spec_oracle_test.json");
        let graph = store.load().unwrap();
        assert_eq!(graph.node_count(), 0);
    }
}
