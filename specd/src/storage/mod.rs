//! Storage backend abstraction for specd
//!
//! This module provides a pluggable storage system where projects can choose
//! where and how to store their data (local files, databases, S3, Git, etc.)

pub mod local_file;

use anyhow::Result;
use spec_core::data::SpecRepository;
use spec_core::formal::UDAFModel;
use std::fmt::Debug;

pub use local_file::LocalFileBackend;

/// Storage backend trait - projects can choose where/how to store data
///
/// All storage backends must be Send + Sync to work in async contexts.
/// Operations return Result to handle failures gracefully.
pub trait StorageBackend: Send + Sync + Debug {
    /// Save a UDA/f model to storage
    ///
    /// # Errors
    /// Returns error if storage is unavailable, permissions denied, or serialization fails
    fn save_udaf_model(&self, project: &str, model: &UDAFModel) -> Result<()>;

    /// Load a UDA/f model from storage
    ///
    /// # Errors
    /// Returns error if project not found, storage unavailable, or deserialization fails
    fn load_udaf_model(&self, project: &str) -> Result<UDAFModel>;

    /// Save a specification repository to storage
    ///
    /// # Errors
    /// Returns error if storage is unavailable, permissions denied, or serialization fails
    fn save_repository(&self, project: &str, repo: &SpecRepository) -> Result<()>;

    /// Load a specification repository from storage
    ///
    /// # Errors
    /// Returns error if project not found, storage unavailable, or deserialization fails
    fn load_repository(&self, project: &str) -> Result<SpecRepository>;

    /// Delete a project's data from storage
    ///
    /// # Errors
    /// Returns error if storage unavailable or permissions denied
    fn delete_project(&self, project: &str) -> Result<()>;

    /// Check if a project exists in storage
    fn exists(&self, project: &str) -> bool;

    /// Get the base path for a project (if applicable to this backend)
    ///
    /// Returns None for backends that don't use filesystem paths (e.g., databases)
    fn project_path(&self, project: &str) -> Option<std::path::PathBuf> {
        let _ = project;
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use spec_core::data::SpecRepository;

    /// Mock storage backend for testing
    #[derive(Debug)]
    struct MockStorage {
        should_fail: bool,
    }

    impl StorageBackend for MockStorage {
        fn save_udaf_model(&self, _project: &str, _model: &UDAFModel) -> Result<()> {
            if self.should_fail {
                anyhow::bail!("Mock storage failure");
            }
            Ok(())
        }

        fn load_udaf_model(&self, _project: &str) -> Result<UDAFModel> {
            if self.should_fail {
                anyhow::bail!("Mock storage failure");
            }
            Ok(UDAFModel::new())
        }

        fn save_repository(&self, _project: &str, _repo: &SpecRepository) -> Result<()> {
            if self.should_fail {
                anyhow::bail!("Mock storage failure");
            }
            Ok(())
        }

        fn load_repository(&self, _project: &str) -> Result<SpecRepository> {
            if self.should_fail {
                anyhow::bail!("Mock storage failure");
            }
            Ok(SpecRepository::new())
        }

        fn delete_project(&self, _project: &str) -> Result<()> {
            if self.should_fail {
                anyhow::bail!("Mock storage failure");
            }
            Ok(())
        }

        fn exists(&self, _project: &str) -> bool {
            !self.should_fail
        }
    }

    #[test]
    fn test_mock_storage_success() {
        let storage = MockStorage { should_fail: false };
        let repo = SpecRepository::new();

        assert!(storage.save_repository("test", &repo).is_ok());
        assert!(storage.load_repository("test").is_ok());
        assert!(storage.exists("test"));
    }

    #[test]
    fn test_mock_storage_failure() {
        let storage = MockStorage { should_fail: true };
        let repo = SpecRepository::new();

        assert!(storage.save_repository("test", &repo).is_err());
        assert!(storage.load_repository("test").is_err());
        assert!(!storage.exists("test"));
    }
}
