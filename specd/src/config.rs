use anyhow::{anyhow, Context, Result};
use ini::Ini;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// Global specd configuration
#[derive(Debug, Clone)]
pub struct SpecdConfig {
    pub listen_address: String,
    pub log_level: String,
    pub default_storage: String,
    pub default_path: PathBuf,
}

impl SpecdConfig {
    /// Load configuration from file
    pub fn load(path: &Path) -> Result<Self> {
        let conf = Ini::load_from_file(path)
            .with_context(|| format!("Failed to load config from {}", path.display()))?;

        let specd_section = conf
            .section(Some("specd"))
            .ok_or_else(|| anyhow!("Missing [specd] section in config"))?;

        let projects_section = conf
            .section(Some("projects"))
            .ok_or_else(|| anyhow!("Missing [projects] section in config"))?;

        let default_path_str = projects_section
            .get("default_path")
            .unwrap_or("~/.specd/projects");

        let default_path = expand_tilde(default_path_str);

        Ok(Self {
            listen_address: specd_section
                .get("listen_address")
                .unwrap_or("[::1]:50051")
                .to_string(),
            log_level: specd_section
                .get("log_level")
                .unwrap_or("info")
                .to_string(),
            default_storage: projects_section
                .get("default_storage")
                .unwrap_or("local")
                .to_string(),
            default_path,
        })
    }

    /// Get default config file path
    pub fn default_config_path() -> PathBuf {
        dirs::home_dir()
            .unwrap_or_else(|| PathBuf::from("."))
            .join(".specd")
            .join("config.ini")
    }

    /// Load config or use defaults if file doesn't exist
    pub fn load_or_default() -> Result<Self> {
        let config_path = Self::default_config_path();
        if config_path.exists() {
            Self::load(&config_path)
        } else {
            Ok(Self::default())
        }
    }

    /// Save configuration to file
    pub fn save(&self, path: &Path) -> Result<()> {
        let mut conf = Ini::new();

        conf.with_section(Some("specd"))
            .set("listen_address", &self.listen_address)
            .set("log_level", &self.log_level);

        conf.with_section(Some("projects"))
            .set("default_storage", &self.default_storage)
            .set("default_path", &self.default_path.display().to_string());

        // Ensure parent directory exists
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("Failed to create config directory: {}", parent.display()))?;
        }

        conf.write_to_file(path)
            .with_context(|| format!("Failed to write config to {}", path.display()))?;

        Ok(())
    }
}

impl Default for SpecdConfig {
    fn default() -> Self {
        Self {
            listen_address: "[::1]:50051".to_string(),
            log_level: "info".to_string(),
            default_storage: "local".to_string(),
            default_path: dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".specd")
                .join("projects"),
        }
    }
}

/// Storage backend configuration (serializable)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "backend", rename_all = "lowercase")]
pub enum StorageConfig {
    #[serde(rename = "local")]
    LocalFile {
        #[serde(default)]
        base_path: PathBuf
    },

    #[serde(rename = "postgres")]
    Database {
        connection_string: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        schema: Option<String>,
    },

    #[serde(rename = "s3")]
    S3 {
        bucket: String,
        prefix: String,
        region: String,
    },

    #[serde(rename = "git")]
    Git {
        repo_url: String,
        branch: String,
        path_prefix: String,
    },
}

/// Project-specific configuration
#[derive(Debug, Clone)]
pub struct ProjectConfig {
    pub name: String,
    pub description: String,
    pub created_at: i64,
    pub storage: StorageConfig,
}

impl ProjectConfig {
    /// Load project configuration from file
    pub fn load(path: &Path) -> Result<Self> {
        let conf = Ini::load_from_file(path)
            .with_context(|| format!("Failed to load project config from {}", path.display()))?;

        let project_section = conf
            .section(Some("project"))
            .ok_or_else(|| anyhow!("Missing [project] section"))?;

        let storage_section = conf
            .section(Some("storage"))
            .ok_or_else(|| anyhow!("Missing [storage] section"))?;

        let storage = match storage_section.get("backend").unwrap_or("local") {
            "local" => {
                let path_str = storage_section.get("path").unwrap_or(".");
                StorageConfig::LocalFile {
                    base_path: expand_tilde(path_str),
                }
            }
            "postgres" | "postgresql" => StorageConfig::Database {
                connection_string: storage_section
                    .get("connection_string")
                    .ok_or_else(|| anyhow!("Missing connection_string for postgres backend"))?
                    .to_string(),
                schema: storage_section.get("schema").map(|s: &str| s.to_string()),
            },
            "s3" => StorageConfig::S3 {
                bucket: storage_section
                    .get("bucket")
                    .ok_or_else(|| anyhow!("Missing bucket for s3 backend"))?
                    .to_string(),
                prefix: storage_section.get("prefix").unwrap_or("").to_string(),
                region: storage_section
                    .get("region")
                    .ok_or_else(|| anyhow!("Missing region for s3 backend"))?
                    .to_string(),
            },
            "git" => StorageConfig::Git {
                repo_url: storage_section
                    .get("repo_url")
                    .ok_or_else(|| anyhow!("Missing repo_url for git backend"))?
                    .to_string(),
                branch: storage_section.get("branch").unwrap_or("main").to_string(),
                path_prefix: storage_section.get("path_prefix").unwrap_or("").to_string(),
            },
            backend => return Err(anyhow!("Unknown storage backend: {}", backend)),
        };

        Ok(Self {
            name: project_section
                .get("name")
                .ok_or_else(|| anyhow!("Missing project name"))?
                .to_string(),
            description: project_section
                .get("description")
                .unwrap_or("")
                .to_string(),
            created_at: project_section
                .get("created_at")
                .and_then(|s: &str| s.parse::<i64>().ok())
                .unwrap_or(0),
            storage,
        })
    }

    /// Save project configuration to file
    pub fn save(&self, path: &Path) -> Result<()> {
        let mut conf = Ini::new();

        conf.with_section(Some("project"))
            .set("name", &self.name)
            .set("description", &self.description)
            .set("created_at", &self.created_at.to_string());

        let mut storage_section = conf.with_section(Some("storage"));
        match &self.storage {
            StorageConfig::LocalFile { base_path } => {
                storage_section.set("backend", "local");
                storage_section.set("path", &base_path.display().to_string());
            }
            StorageConfig::Database {
                connection_string,
                schema,
            } => {
                storage_section.set("backend", "postgres");
                storage_section.set("connection_string", connection_string);
                if let Some(s) = schema {
                    storage_section.set("schema", s);
                }
            }
            StorageConfig::S3 {
                bucket,
                prefix,
                region,
            } => {
                storage_section.set("backend", "s3");
                storage_section.set("bucket", bucket);
                storage_section.set("prefix", prefix);
                storage_section.set("region", region);
            }
            StorageConfig::Git {
                repo_url,
                branch,
                path_prefix,
            } => {
                storage_section.set("backend", "git");
                storage_section.set("repo_url", repo_url);
                storage_section.set("branch", branch);
                storage_section.set("path_prefix", path_prefix);
            }
        }

        // Ensure parent directory exists
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("Failed to create directory: {}", parent.display()))?;
        }

        conf.write_to_file(path)
            .with_context(|| format!("Failed to write project config to {}", path.display()))?;

        Ok(())
    }
}

/// Expand ~ to home directory
fn expand_tilde(path_str: &str) -> PathBuf {
    if path_str.starts_with("~/") {
        if let Some(home) = dirs::home_dir() {
            return home.join(&path_str[2..]);
        }
    }
    PathBuf::from(path_str)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_specd_config_default() {
        let config = SpecdConfig::default();
        assert_eq!(config.listen_address, "[::1]:50051");
        assert_eq!(config.log_level, "info");
        assert_eq!(config.default_storage, "local");
    }

    #[test]
    fn test_specd_config_save_and_load() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("config.ini");

        let config = SpecdConfig::default();
        config.save(&config_path).unwrap();

        let loaded = SpecdConfig::load(&config_path).unwrap();
        assert_eq!(loaded.listen_address, config.listen_address);
        assert_eq!(loaded.log_level, config.log_level);
    }

    #[test]
    fn test_project_config_local_storage() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("project_config.ini");

        let project_config = ProjectConfig {
            name: "test-project".to_string(),
            description: "Test project".to_string(),
            created_at: 1234567890,
            storage: StorageConfig::LocalFile {
                base_path: PathBuf::from("/tmp/test"),
            },
        };

        project_config.save(&config_path).unwrap();

        let loaded = ProjectConfig::load(&config_path).unwrap();
        assert_eq!(loaded.name, "test-project");
        assert_eq!(loaded.description, "Test project");

        match loaded.storage {
            StorageConfig::LocalFile { base_path } => {
                assert_eq!(base_path, PathBuf::from("/tmp/test"));
            }
            _ => panic!("Expected LocalFile storage"),
        }
    }

    #[test]
    fn test_expand_tilde() {
        let expanded = expand_tilde("~/test/path");
        if let Some(home) = dirs::home_dir() {
            assert_eq!(expanded, home.join("test/path"));
        }

        let no_tilde = expand_tilde("/absolute/path");
        assert_eq!(no_tilde, PathBuf::from("/absolute/path"));
    }
}
