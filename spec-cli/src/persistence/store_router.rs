use std::path::PathBuf;

/// Storage type detected in the project
#[derive(Debug, Clone, PartialEq)]
pub enum StorageType {
    /// Directory-based storage (.spec/nodes/*.yaml + .spec/edges.yaml)
    Directory(PathBuf),
    /// File-based storage (.spec/specs.json)
    File(PathBuf),
}

/// Find .spec directory by walking up from current directory
///
/// Searches for a project-local .spec directory by traversing
/// up the directory tree from the current working directory.
///
/// Returns Some(path) if found, None otherwise.
pub fn find_spec_dir() -> Option<PathBuf> {
    let mut current = std::env::current_dir().ok()?;
    loop {
        let spec_dir = current.join(".spec");
        if spec_dir.exists() && spec_dir.is_dir() {
            return Some(spec_dir);
        }
        if !current.pop() {
            break;
        }
    }
    None
}

/// Detect storage type in the project
///
/// Checks for directory-based storage first (.spec/nodes/), then falls back
/// to file-based storage (.spec/specs.json).
///
/// Returns Some(StorageType) if storage is found, None otherwise.
pub fn detect_storage_type() -> Option<StorageType> {
    let spec_dir = find_spec_dir()?;

    // Prioritize directory-based storage (newer format)
    let nodes_dir = spec_dir.join("nodes");
    if nodes_dir.exists() && nodes_dir.is_dir() {
        return Some(StorageType::Directory(spec_dir));
    }

    // Fall back to file-based storage
    let spec_file = spec_dir.join("specs.json");
    if spec_file.exists() {
        return Some(StorageType::File(spec_file));
    }

    None
}

/// Find .spec/specs.json by walking up from current directory
///
/// Searches for a project-local .spec/specs.json file by traversing
/// up the directory tree from the current working directory.
///
/// Returns Some(path) if found, None otherwise.
pub fn find_spec_file() -> Option<PathBuf> {
    let spec_dir = find_spec_dir()?;
    let spec_file = spec_dir.join("specs.json");
    if spec_file.exists() {
        Some(spec_file)
    } else {
        None
    }
}

/// Check if standalone mode should be used
///
/// Returns true if a project-local .spec directory is found.
pub fn should_use_standalone_mode() -> bool {
    find_spec_dir().is_some()
}

/// Get the spec file path, or return None if not in a spec-managed project
pub fn get_spec_file_path() -> Option<PathBuf> {
    find_spec_file()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_spec_dir() {
        // This test assumes running in spec-oracle project
        let path = find_spec_dir();
        assert!(path.is_some(), "Should find .spec directory in project");

        if let Some(p) = path {
            assert!(p.ends_with(".spec"));
        }
    }

    #[test]
    fn test_detect_storage_type() {
        // This test assumes running in spec-oracle project
        let storage = detect_storage_type();
        assert!(storage.is_some(), "Should detect storage type in project");

        if let Some(StorageType::Directory(path)) = storage {
            assert!(path.ends_with(".spec"));
            assert!(path.join("nodes").exists());
        }
    }

    #[test]
    fn test_should_use_standalone_mode() {
        // Should be true when running in spec-oracle project
        assert!(should_use_standalone_mode());
    }
}
