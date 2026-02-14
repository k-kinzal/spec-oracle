use std::path::PathBuf;

/// Find .spec/specs.json by walking up from current directory
///
/// Searches for a project-local .spec/specs.json file by traversing
/// up the directory tree from the current working directory.
///
/// Returns Some(path) if found, None otherwise.
pub fn find_spec_file() -> Option<PathBuf> {
    let mut current = std::env::current_dir().ok()?;
    loop {
        let spec_file = current.join(".spec").join("specs.json");
        if spec_file.exists() {
            return Some(spec_file);
        }
        if !current.pop() {
            break;
        }
    }
    None
}

/// Check if standalone mode should be used
///
/// Returns true if a project-local .spec/specs.json file is found.
pub fn should_use_standalone_mode() -> bool {
    find_spec_file().is_some()
}

/// Get the spec file path, or return None if not in a spec-managed project
pub fn get_spec_file_path() -> Option<PathBuf> {
    find_spec_file()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_spec_file_finds_project_local() {
        // This test assumes running in spec-oracle project
        let path = find_spec_file();
        assert!(path.is_some(), "Should find .spec/specs.json in project");

        if let Some(p) = path {
            assert!(p.ends_with(".spec/specs.json"));
        }
    }

    #[test]
    fn test_should_use_standalone_mode() {
        // Should be true when running in spec-oracle project
        assert!(should_use_standalone_mode());
    }
}
