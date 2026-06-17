//! Migration tools for importing legacy .spec/ directories
//!
//! This module provides functionality to import existing .spec/ directories
//! into the new project-based architecture with UDAFModel support.

use anyhow::{anyhow, Context, Result};
use spec_core::data::SpecRepository;
use spec_core::formal::{UDAFModel, ModelSync};
use spec_core::store::{DirectoryStore, FileStore, Store};
use std::path::{Path, PathBuf};

use crate::config::StorageConfig;
use crate::project::{ProjectManager, Project};

/// Report from importing a legacy project
#[derive(Debug)]
pub struct ImportReport {
    pub nodes_imported: usize,
    pub edges_imported: usize,
    pub universes_created: usize,
}

/// Import a legacy .spec/ directory into a new project
///
/// This function:
/// 1. Detects the storage format (DirectoryStore or FileStore)
/// 2. Loads the SpecRepository
/// 3. Synthesizes a UDAFModel from the repository metadata
/// 4. Creates a new project with both
pub fn import_legacy_spec_directory(
    spec_dir: &Path,
    project_name: String,
    description: String,
    project_manager: &mut ProjectManager,
) -> Result<ImportReport> {
    // 1. Detect and load repository from .spec/
    let repository = detect_and_load_repository(spec_dir)
        .with_context(|| format!("Failed to load repository from {}", spec_dir.display()))?;

    // 2. Synthesize UDAFModel from repository
    let mut udaf_model = UDAFModel::new(); // Creates U0 automatically

    // Extract unique formality layers from repository nodes
    let mut layers_seen = std::collections::HashSet::new();
    for node in repository.list_nodes(None) {
        if node.formality_layer > 0 && !layers_seen.contains(&node.formality_layer) {
            udaf_model
                .add_universe(
                    node.formality_layer,
                    format!("U{}", node.formality_layer),
                    format!("Layer {} specifications", node.formality_layer),
                )
                .map_err(|e| anyhow!("Failed to add universe: {:?}", e))?;
            layers_seen.insert(node.formality_layer);
        }
    }

    // Use ModelSync to populate UDAFModel from SpecRepository
    ModelSync::sync_from_repository(&mut udaf_model, &repository)
        .map_err(|e| anyhow!("Failed to sync UDAFModel from repository: {}", e))?;

    // 3. Create storage config (default to local file in project manager's base path)
    let storage = StorageConfig::LocalFile {
        base_path: project_manager.base_path().to_path_buf(),
    };

    // 4. Create the project
    project_manager
        .create_project(project_name.clone(), description, storage)
        .with_context(|| format!("Failed to create project: {}", project_name))?;

    // 5. Load the project and update it with imported data
    let mut project = project_manager
        .load_project(&project_name)
        .with_context(|| format!("Failed to load newly created project: {}", project_name))?;

    project.udaf_model = udaf_model;
    project.repository = repository.clone();

    // 6. Save the updated project
    project_manager
        .save_project(&project)
        .with_context(|| format!("Failed to save imported project: {}", project_name))?;

    Ok(ImportReport {
        nodes_imported: repository.node_count(),
        edges_imported: repository.edge_count(),
        universes_created: layers_seen.len(),
    })
}

/// Detect storage format and load repository
fn detect_and_load_repository(spec_dir: &Path) -> Result<SpecRepository> {
    if !spec_dir.exists() {
        return Err(anyhow!("Directory does not exist: {}", spec_dir.display()));
    }

    if !spec_dir.is_dir() {
        return Err(anyhow!("Path is not a directory: {}", spec_dir.display()));
    }

    // Priority 1: DirectoryStore format (.spec/nodes/ directory)
    let nodes_dir = spec_dir.join("nodes");
    if nodes_dir.exists() && nodes_dir.is_dir() {
        let store = DirectoryStore::new(spec_dir.to_path_buf());
        return Store::from_directory(spec_dir.to_path_buf())
            .load()
            .with_context(|| "Failed to load DirectoryStore");
    }

    // Priority 2: FileStore format (.spec/specs.json)
    let specs_json = spec_dir.join("specs.json");
    if specs_json.exists() {
        return Store::from_file(specs_json.clone())
            .load()
            .with_context(|| format!("Failed to load FileStore from {}", specs_json.display()));
    }

    // No recognized format found
    Err(anyhow!(
        "No valid spec storage found in {}. Expected either nodes/ directory or specs.json file.",
        spec_dir.display()
    ))
}

/// Find legacy .spec/ directories in the current directory or parent directories
///
/// Searches upward from the current directory to find a .spec/ directory.
pub fn find_legacy_spec_dir() -> Option<PathBuf> {
    let mut dir = std::env::current_dir().ok()?;
    loop {
        let spec_dir = dir.join(".spec");
        if spec_dir.exists() && spec_dir.is_dir() {
            return Some(spec_dir);
        }
        if !dir.pop() {
            break;
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use spec_core::data::NodeKind;
    use std::collections::HashMap;
    use tempfile::TempDir;

    #[test]
    fn test_detect_directory_store() {
        let temp_dir = TempDir::new().unwrap();
        let spec_dir = temp_dir.path().join(".spec");
        std::fs::create_dir_all(spec_dir.join("nodes")).unwrap();
        std::fs::write(spec_dir.join("edges.yaml"), "[]").unwrap(); // edges.yaml should be a sequence

        let result = detect_and_load_repository(&spec_dir);
        if let Err(e) = &result {
            eprintln!("Error: {:#?}", e);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_detect_nonexistent() {
        let temp_dir = TempDir::new().unwrap();
        let spec_dir = temp_dir.path().join(".spec");

        let result = detect_and_load_repository(&spec_dir);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("does not exist"));
    }

    #[test]
    fn test_find_legacy_spec_dir() {
        // This test depends on the current directory structure
        // Just verify it doesn't panic
        let _result = find_legacy_spec_dir();
    }
}
