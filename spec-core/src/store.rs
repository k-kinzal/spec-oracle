use crate::graph::SpecGraph;
use std::path::{Path, PathBuf};

#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("JSON serialization error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("YAML serialization error: {0}")]
    Yaml(#[from] serde_yaml::Error),
}

/// Unified storage interface supporting both file-based and directory-based storage
pub enum Store {
    /// File-based storage (.spec/specs.json)
    File(FileStore),
    /// Directory-based storage (.spec/nodes/*.yaml + .spec/edges.yaml)
    Directory(DirectoryStore),
}

impl Store {
    /// Load specification graph from storage
    pub fn load(&self) -> Result<SpecGraph, StoreError> {
        match self {
            Store::File(store) => store.load(),
            Store::Directory(store) => store.load(),
        }
    }

    /// Save specification graph to storage
    pub fn save(&self, graph: &SpecGraph) -> Result<(), StoreError> {
        match self {
            Store::File(store) => store.save(graph),
            Store::Directory(store) => store.save(graph),
        }
    }

    /// Create a Store from a file path
    pub fn from_file(path: impl AsRef<Path>) -> Self {
        Store::File(FileStore::new(path))
    }

    /// Create a Store from a directory path
    pub fn from_directory(path: impl AsRef<Path>) -> Self {
        Store::Directory(DirectoryStore::new(path))
    }
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

/// Directory-based persistence for the specification graph.
/// Each node is saved as an individual YAML file for better merge conflict resolution.
pub struct DirectoryStore {
    base_path: PathBuf,
}

impl DirectoryStore {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            base_path: path.as_ref().to_path_buf(),
        }
    }

    fn nodes_dir(&self) -> PathBuf {
        self.base_path.join("nodes")
    }

    fn edges_file(&self) -> PathBuf {
        self.base_path.join("edges.yaml")
    }

    fn metadata_file(&self) -> PathBuf {
        self.base_path.join("metadata.yaml")
    }

    pub fn load(&self) -> Result<SpecGraph, StoreError> {
        if !self.base_path.exists() {
            return Ok(SpecGraph::new());
        }

        let mut graph = SpecGraph::new();

        // Load nodes from individual YAML files
        let nodes_dir = self.nodes_dir();
        if nodes_dir.exists() {
            for entry in std::fs::read_dir(&nodes_dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("yaml") {
                    let content = std::fs::read_to_string(&path)?;
                    let node: crate::graph::SpecNodeData = serde_yaml::from_str(&content)?;
                    graph.add_node_from_loaded(node);
                }
            }
        }

        // Load edges from edges.yaml
        let edges_file = self.edges_file();
        if edges_file.exists() {
            let content = std::fs::read_to_string(&edges_file)?;
            let edges: Vec<crate::graph::Edge> = serde_yaml::from_str(&content)?;
            for edge in edges {
                let _ = graph.add_edge_from_loaded(edge);
            }
        }

        graph.rebuild_indices();
        Ok(graph)
    }

    pub fn save(&self, graph: &SpecGraph) -> Result<(), StoreError> {
        std::fs::create_dir_all(&self.base_path)?;
        let nodes_dir = self.nodes_dir();
        std::fs::create_dir_all(&nodes_dir)?;

        // Clean up: remove all existing YAML files to ensure removed nodes are deleted
        if nodes_dir.exists() {
            // Collect file paths first to avoid iterator corruption
            let yaml_files: Vec<PathBuf> = std::fs::read_dir(&nodes_dir)?
                .filter_map(|entry| entry.ok())
                .map(|e| e.path())
                .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("yaml"))
                .collect();

            // Delete files after iteration is complete
            for path in &yaml_files {
                std::fs::remove_file(&path)?;
            }
        }

        // Save each node as individual YAML file
        for node in graph.nodes() {
            let filename = format!("{}.yaml", node.id);
            let path = nodes_dir.join(filename);
            let content = serde_yaml::to_string(&node)?;
            std::fs::write(&path, content)?;
        }

        // Save edges as single YAML file
        let edges: Vec<_> = graph.edges().collect();
        let edges_content = serde_yaml::to_string(&edges)?;
        std::fs::write(self.edges_file(), edges_content)?;

        Ok(())
    }
}

#[cfg(test)]
mod directory_store_tests {
    use super::*;
    use crate::graph::NodeKind;
    use std::collections::HashMap;

    #[test]
    fn directory_store_roundtrip() {
        let dir = std::env::temp_dir().join(format!("spec_oracle_dir_test_{}", uuid::Uuid::new_v4()));
        let store = DirectoryStore::new(&dir);

        let mut graph = SpecGraph::new();
        let node = graph.add_node("test node".into(), NodeKind::Assertion, HashMap::new());
        let node_id = node.id.clone();

        store.save(&graph).unwrap();

        // Verify individual node file exists
        let node_file = dir.join("nodes").join(format!("{}.yaml", node_id));
        assert!(node_file.exists());

        // Verify roundtrip
        let loaded = store.load().unwrap();
        assert_eq!(loaded.node_count(), 1);

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn directory_store_load_nonexistent() {
        let dir = std::env::temp_dir().join(format!("spec_oracle_nonexistent_{}", uuid::Uuid::new_v4()));
        let store = DirectoryStore::new(&dir);
        let graph = store.load().unwrap();
        assert_eq!(graph.node_count(), 0);
    }
}
