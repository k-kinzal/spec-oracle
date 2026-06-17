//! Project management for specd
//!
//! This module provides project/namespace support, allowing specd to manage
//! multiple independent specification projects (like docker contexts).

use anyhow::{anyhow, Context, Result};
use spec_core::data::SpecRepository;
use spec_core::formal::UDAFModel;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use crate::config::{ProjectConfig, StorageConfig};
use crate::storage::{LocalFileBackend, StorageBackend};

/// Project manager handles multiple projects with different storage backends
#[derive(Debug)]
pub struct ProjectManager {
    /// Base path for global project storage (typically ~/.specd/projects)
    base_path: PathBuf,
    /// Map of project name to project handle
    projects: Arc<RwLock<HashMap<String, Arc<ProjectHandle>>>>,
    /// Currently active project
    current_project: Arc<RwLock<Option<String>>>,
}

/// Handle to a project (metadata + storage backend)
#[derive(Debug)]
pub struct ProjectHandle {
    pub name: String,
    pub description: String,
    pub created_at: i64,
    storage_backend: Box<dyn StorageBackend>,
    storage_config: StorageConfig,
}

/// Full project data (metadata + UDA/f model + repository)
#[derive(Debug)]
pub struct Project {
    pub name: String,
    pub description: String,
    pub created_at: i64,
    pub udaf_model: UDAFModel,
    pub repository: SpecRepository,
}

/// Project information for listing
#[derive(Debug, Clone)]
pub struct ProjectInfo {
    pub name: String,
    pub description: String,
    pub created_at: i64,
    pub node_count: usize,
    pub edge_count: usize,
    pub storage: StorageConfig,
}

impl ProjectManager {
    /// Create a new project manager with the given base path
    pub fn new(base_path: PathBuf) -> Self {
        Self {
            base_path,
            projects: Arc::new(RwLock::new(HashMap::new())),
            current_project: Arc::new(RwLock::new(None)),
        }
    }

    /// Get the base path for project storage
    pub fn base_path(&self) -> &Path {
        &self.base_path
    }

    /// Ensure the default project exists
    ///
    /// If no projects exist, create a "default" project automatically.
    pub fn ensure_default(&mut self) -> Result<()> {
        let projects = self.projects.read().unwrap();
        if projects.is_empty() {
            drop(projects); // Release read lock before acquiring write lock

            self.create_project(
                "default".to_string(),
                "Default project".to_string(),
                StorageConfig::LocalFile {
                    base_path: self.base_path.clone(),
                },
            )?;

            let mut current = self.current_project.write().unwrap();
            *current = Some("default".to_string());
        }
        Ok(())
    }

    /// Discover and load existing projects from base_path
    pub fn discover_projects(&mut self) -> Result<()> {
        if !self.base_path.exists() {
            return Ok(());
        }

        for entry in std::fs::read_dir(&self.base_path)
            .with_context(|| format!("Failed to read projects directory: {}", self.base_path.display()))?
        {
            let entry = entry?;
            let path = entry.path();

            if !path.is_dir() {
                continue;
            }

            // Check for config.ini
            let config_path = path.join("config.ini");
            if config_path.exists() {
                if let Ok(config) = ProjectConfig::load(&config_path) {
                    self.register_project_from_config(config)?;
                }
            }
        }

        Ok(())
    }

    /// Register a project from an existing ProjectConfig
    fn register_project_from_config(&mut self, config: ProjectConfig) -> Result<()> {
        let storage_backend = create_storage_backend(&config.storage)?;

        let handle = Arc::new(ProjectHandle {
            name: config.name.clone(),
            description: config.description,
            created_at: config.created_at,
            storage_backend,
            storage_config: config.storage,
        });

        let mut projects = self.projects.write().unwrap();
        projects.insert(config.name, handle);

        Ok(())
    }

    /// Create a new project with specified storage backend
    pub fn create_project(
        &mut self,
        name: String,
        description: String,
        storage: StorageConfig,
    ) -> Result<()> {
        // Check if project already exists
        {
            let projects = self.projects.read().unwrap();
            if projects.contains_key(&name) {
                return Err(anyhow!("Project already exists: {}", name));
            }
        }

        let storage_backend = create_storage_backend(&storage)?;

        // Initialize new UDA/f model (with U0 created automatically)
        let udaf_model = UDAFModel::new();
        storage_backend.save_udaf_model(&name, &udaf_model)?;

        // Initialize empty repository
        let repository = SpecRepository::new();
        storage_backend.save_repository(&name, &repository)?;

        // Save project config
        let config = ProjectConfig {
            name: name.clone(),
            description: description.clone(),
            created_at: chrono::Utc::now().timestamp(),
            storage: storage.clone(),
        };

        // Determine config file path based on storage type
        let config_path = match &storage {
            StorageConfig::LocalFile { base_path } => {
                let project_dir = base_path.join(&name);
                std::fs::create_dir_all(&project_dir)?;
                project_dir.join("config.ini")
            }
            _ => self.base_path.join(&name).join("config.ini"),
        };

        config.save(&config_path)?;

        // Register project
        let handle = Arc::new(ProjectHandle {
            name: name.clone(),
            description,
            created_at: config.created_at,
            storage_backend,
            storage_config: storage,
        });

        let mut projects = self.projects.write().unwrap();
        projects.insert(name, handle);

        Ok(())
    }

    /// Load a project's data
    pub fn load_project(&self, name: &str) -> Result<Project> {
        let projects = self.projects.read().unwrap();
        let handle = projects
            .get(name)
            .ok_or_else(|| anyhow!("Project not found: {}", name))?;

        let udaf_model = handle.storage_backend.load_udaf_model(name)?;
        let repository = handle.storage_backend.load_repository(name)?;

        Ok(Project {
            name: handle.name.clone(),
            description: handle.description.clone(),
            created_at: handle.created_at,
            udaf_model,
            repository,
        })
    }

    /// Save a project's data
    pub fn save_project(&self, project: &Project) -> Result<()> {
        let projects = self.projects.read().unwrap();
        let handle = projects
            .get(&project.name)
            .ok_or_else(|| anyhow!("Project not found: {}", project.name))?;

        handle
            .storage_backend
            .save_udaf_model(&project.name, &project.udaf_model)?;
        handle
            .storage_backend
            .save_repository(&project.name, &project.repository)?;

        Ok(())
    }

    /// Switch to a different project
    pub fn switch_project(&self, name: &str) -> Result<()> {
        let projects = self.projects.read().unwrap();
        if !projects.contains_key(name) {
            return Err(anyhow!("Project not found: {}", name));
        }
        drop(projects);

        let mut current = self.current_project.write().unwrap();
        *current = Some(name.to_string());

        Ok(())
    }

    /// Get the current project name
    pub fn current_project(&self) -> Option<String> {
        self.current_project.read().unwrap().clone()
    }

    /// Get the current project or a named project
    pub fn get_current_or_named(&self, project_name: &str) -> Result<String> {
        if project_name.is_empty() {
            self.current_project()
                .ok_or_else(|| anyhow!("No current project set. Use 'spec project use <name>' to select one."))
        } else {
            Ok(project_name.to_string())
        }
    }

    /// List all projects
    pub fn list_projects(&self) -> Result<Vec<ProjectInfo>> {
        let projects = self.projects.read().unwrap();

        let mut infos = Vec::new();
        for handle in projects.values() {
            // Load repository to get counts
            let repo = match handle.storage_backend.load_repository(&handle.name) {
                Ok(r) => r,
                Err(_) => SpecRepository::new(), // Fallback to empty if load fails
            };

            infos.push(ProjectInfo {
                name: handle.name.clone(),
                description: handle.description.clone(),
                created_at: handle.created_at,
                node_count: repo.node_count(),
                edge_count: repo.edge_count(),
                storage: handle.storage_config.clone(),
            });
        }

        // Sort by creation time (newest first)
        infos.sort_by(|a, b| b.created_at.cmp(&a.created_at));

        Ok(infos)
    }

    /// Delete a project
    pub fn delete_project(&mut self, name: &str) -> Result<()> {
        let mut projects = self.projects.write().unwrap();
        let handle = projects
            .remove(name)
            .ok_or_else(|| anyhow!("Project not found: {}", name))?;

        // Delete from storage
        handle.storage_backend.delete_project(name)?;

        // Delete config file
        let config_path = match &handle.storage_config {
            StorageConfig::LocalFile { base_path } => base_path.join(name).join("config.ini"),
            _ => self.base_path.join(name).join("config.ini"),
        };

        if config_path.exists() {
            std::fs::remove_file(config_path)?;
        }

        drop(projects);

        // If this was the current project, unset it
        let mut current = self.current_project.write().unwrap();
        if current.as_deref() == Some(name) {
            *current = None;
        }

        Ok(())
    }

    /// Check if a project exists
    pub fn project_exists(&self, name: &str) -> bool {
        let projects = self.projects.read().unwrap();
        projects.contains_key(name)
    }
}

/// Create a storage backend from configuration
fn create_storage_backend(config: &StorageConfig) -> Result<Box<dyn StorageBackend>> {
    match config {
        StorageConfig::LocalFile { base_path } => {
            Ok(Box::new(LocalFileBackend::new(base_path.clone())))
        }
        StorageConfig::Database { .. } => {
            Err(anyhow!("Database storage backend not yet implemented"))
        }
        StorageConfig::S3 { .. } => Err(anyhow!("S3 storage backend not yet implemented")),
        StorageConfig::Git { .. } => Err(anyhow!("Git storage backend not yet implemented")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_create_and_load_project() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.create_project(
            "test-project".to_string(),
            "Test project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        assert!(pm.project_exists("test-project"));

        let project = pm.load_project("test-project").unwrap();
        assert_eq!(project.name, "test-project");
        assert_eq!(project.description, "Test project");
    }

    #[test]
    fn test_switch_project() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.create_project(
            "project1".to_string(),
            "Project 1".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        pm.create_project(
            "project2".to_string(),
            "Project 2".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        pm.switch_project("project1").unwrap();
        assert_eq!(pm.current_project(), Some("project1".to_string()));

        pm.switch_project("project2").unwrap();
        assert_eq!(pm.current_project(), Some("project2".to_string()));
    }

    #[test]
    fn test_list_projects() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.create_project(
            "project1".to_string(),
            "First project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        pm.create_project(
            "project2".to_string(),
            "Second project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        let projects = pm.list_projects().unwrap();
        assert_eq!(projects.len(), 2);

        let names: Vec<&str> = projects.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"project1"));
        assert!(names.contains(&"project2"));
    }

    #[test]
    fn test_delete_project() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.create_project(
            "test-project".to_string(),
            "Test project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        assert!(pm.project_exists("test-project"));

        pm.delete_project("test-project").unwrap();
        assert!(!pm.project_exists("test-project"));
    }

    #[test]
    fn test_duplicate_project_name() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.create_project(
            "test-project".to_string(),
            "Test project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        let result = pm.create_project(
            "test-project".to_string(),
            "Duplicate project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        );

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Project already exists"));
    }

    #[test]
    fn test_ensure_default() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.ensure_default().unwrap();

        assert!(pm.project_exists("default"));
        assert_eq!(pm.current_project(), Some("default".to_string()));
    }

    #[test]
    fn test_get_current_or_named() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf());

        pm.create_project(
            "test-project".to_string(),
            "Test project".to_string(),
            StorageConfig::LocalFile {
                base_path: temp_dir.path().to_path_buf(),
            },
        )
        .unwrap();

        pm.switch_project("test-project").unwrap();

        // Empty string should return current project
        let result = pm.get_current_or_named("").unwrap();
        assert_eq!(result, "test-project");

        // Named project should return that project
        let result = pm.get_current_or_named("test-project").unwrap();
        assert_eq!(result, "test-project");
    }
}
