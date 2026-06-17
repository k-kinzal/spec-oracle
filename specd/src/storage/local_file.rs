//! Local filesystem storage backend
//!
//! Stores project data in local directories using the DirectoryStore format:
//! - Each node as individual YAML file in nodes/
//! - All edges in edges.yaml
//! - Project config in config.ini

use anyhow::{Context, Result};
use spec_core::data::SpecRepository;
use spec_core::formal::UDAFModel;
use spec_core::store::{DirectoryStore, Store};
use std::path::PathBuf;

use super::StorageBackend;

/// Local filesystem storage backend
///
/// Uses DirectoryStore for efficient Git-friendly storage:
/// - Individual YAML files per node (better merge conflict resolution)
/// - Single edges.yaml file
/// - Human-readable format
#[derive(Debug, Clone)]
pub struct LocalFileBackend {
    base_path: PathBuf,
}

impl LocalFileBackend {
    /// Create a new local file backend with the given base path
    ///
    /// The base path should point to a directory where projects are stored.
    /// Each project will have its own subdirectory under the base path.
    pub fn new(base_path: PathBuf) -> Self {
        Self { base_path }
    }

    /// Get the directory path for a specific project
    fn project_dir(&self, project: &str) -> PathBuf {
        self.base_path.join(project)
    }

    /// Create a DirectoryStore for the given project
    fn store_for_project(&self, project: &str) -> DirectoryStore {
        DirectoryStore::new(self.project_dir(project))
    }
}

impl StorageBackend for LocalFileBackend {
    fn save_udaf_model(&self, project: &str, model: &UDAFModel) -> Result<()> {
        let project_dir = self.project_dir(project);

        // Ensure project directory exists
        std::fs::create_dir_all(&project_dir).with_context(|| {
            format!(
                "Failed to create project directory: {}",
                project_dir.display()
            )
        })?;

        // Serialize UDAFModel to JSON
        let model_json = serde_json::to_string_pretty(model)
            .with_context(|| "Failed to serialize UDAFModel")?;

        // Write to udaf-model.json
        let model_path = project_dir.join("udaf-model.json");
        std::fs::write(&model_path, model_json).with_context(|| {
            format!("Failed to write UDAFModel to {}", model_path.display())
        })?;

        Ok(())
    }

    fn load_udaf_model(&self, project: &str) -> Result<UDAFModel> {
        let project_dir = self.project_dir(project);

        if !project_dir.exists() {
            anyhow::bail!("Project not found: {}", project);
        }

        let model_path = project_dir.join("udaf-model.json");

        // If udaf-model.json doesn't exist, create a new model
        if !model_path.exists() {
            return Ok(UDAFModel::new());
        }

        // Read and deserialize UDAFModel
        let model_json = std::fs::read_to_string(&model_path).with_context(|| {
            format!("Failed to read UDAFModel from {}", model_path.display())
        })?;

        serde_json::from_str(&model_json)
            .with_context(|| "Failed to deserialize UDAFModel")
    }

    fn save_repository(&self, project: &str, repo: &SpecRepository) -> Result<()> {
        let project_dir = self.project_dir(project);

        // Ensure project directory exists
        std::fs::create_dir_all(&project_dir).with_context(|| {
            format!(
                "Failed to create project directory: {}",
                project_dir.display()
            )
        })?;

        // Use DirectoryStore to save
        let store = Store::from_directory(project_dir);
        store
            .save(repo)
            .with_context(|| format!("Failed to save repository for project: {}", project))?;

        Ok(())
    }

    fn load_repository(&self, project: &str) -> Result<SpecRepository> {
        let project_dir = self.project_dir(project);

        if !project_dir.exists() {
            anyhow::bail!("Project not found: {}", project);
        }

        // Use DirectoryStore to load
        let store = Store::from_directory(project_dir);
        store
            .load()
            .with_context(|| format!("Failed to load repository for project: {}", project))
    }

    fn delete_project(&self, project: &str) -> Result<()> {
        let project_dir = self.project_dir(project);

        if !project_dir.exists() {
            anyhow::bail!("Project not found: {}", project);
        }

        std::fs::remove_dir_all(&project_dir).with_context(|| {
            format!(
                "Failed to delete project directory: {}",
                project_dir.display()
            )
        })?;

        Ok(())
    }

    fn exists(&self, project: &str) -> bool {
        self.project_dir(project).exists()
    }

    fn project_path(&self, project: &str) -> Option<PathBuf> {
        Some(self.project_dir(project))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use spec_core::data::NodeKind;
    use std::collections::HashMap;
    use tempfile::TempDir;

    #[test]
    fn test_save_and_load_repository() {
        let temp_dir = TempDir::new().unwrap();
        let backend = LocalFileBackend::new(temp_dir.path().to_path_buf());

        let mut repo = SpecRepository::new();
        repo.add_node(
            "Test specification".to_string(),
            NodeKind::Assertion,
            HashMap::new(),
        );

        // Save repository
        backend.save_repository("test-project", &repo).unwrap();

        // Verify directory exists
        assert!(backend.exists("test-project"));

        // Load repository
        let loaded = backend.load_repository("test-project").unwrap();
        assert_eq!(loaded.node_count(), 1);
    }

    #[test]
    fn test_delete_project() {
        let temp_dir = TempDir::new().unwrap();
        let backend = LocalFileBackend::new(temp_dir.path().to_path_buf());

        let repo = SpecRepository::new();
        backend.save_repository("test-project", &repo).unwrap();
        assert!(backend.exists("test-project"));

        backend.delete_project("test-project").unwrap();
        assert!(!backend.exists("test-project"));
    }

    #[test]
    fn test_load_nonexistent_project() {
        let temp_dir = TempDir::new().unwrap();
        let backend = LocalFileBackend::new(temp_dir.path().to_path_buf());

        let result = backend.load_repository("nonexistent");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Project not found"));
    }

    #[test]
    fn test_delete_nonexistent_project() {
        let temp_dir = TempDir::new().unwrap();
        let backend = LocalFileBackend::new(temp_dir.path().to_path_buf());

        let result = backend.delete_project("nonexistent");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Project not found"));
    }

    #[test]
    fn test_project_path() {
        let temp_dir = TempDir::new().unwrap();
        let backend = LocalFileBackend::new(temp_dir.path().to_path_buf());

        let path = backend.project_path("test-project");
        assert!(path.is_some());
        assert_eq!(
            path.unwrap(),
            temp_dir.path().join("test-project")
        );
    }

    #[test]
    fn test_directory_structure() {
        let temp_dir = TempDir::new().unwrap();
        let backend = LocalFileBackend::new(temp_dir.path().to_path_buf());

        let mut repo = SpecRepository::new();
        let node = repo.add_node(
            "Test node".to_string(),
            NodeKind::Assertion,
            HashMap::new(),
        );
        let node_id = node.id.clone();

        backend.save_repository("test-project", &repo).unwrap();

        // Verify directory structure
        let project_dir = temp_dir.path().join("test-project");
        assert!(project_dir.exists());
        assert!(project_dir.join("nodes").exists());
        assert!(project_dir.join("edges.yaml").exists());
        assert!(project_dir
            .join("nodes")
            .join(format!("{}.yaml", node_id))
            .exists());
    }
}
