/// Well-known metadata keys
///
/// This enum prevents typos and provides type-safe metadata access.
/// Custom keys can still be used via MetadataKey::Custom(String).

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MetadataKey {
    /// Universe identifier (e.g., "U1", "U2")
    Universe,
    /// Source file path
    SourceFile,
    /// RPC method name
    RpcName,
    /// Extractor that produced this specification
    Extractor,
    /// Whether this was inferred (vs. manually written)
    Inferred,
    /// Variable name in code
    Variable,
    /// Implementation code snippet
    ImplCode,
    /// Test code snippet
    TestCode,
    /// Pattern that was matched
    Pattern,
    /// Specific value
    Value,
    /// Minimum constraint value
    Min,
    /// Maximum constraint value
    Max,
    /// Source of the specification
    Source,
    /// Custom key (for extensibility)
    Custom(String),
}

impl MetadataKey {
    /// Convert to string key for HashMap storage
    pub fn as_str(&self) -> &str {
        match self {
            MetadataKey::Universe => "universe",
            MetadataKey::SourceFile => "source_file",
            MetadataKey::RpcName => "rpc_name",
            MetadataKey::Extractor => "extractor",
            MetadataKey::Inferred => "inferred",
            MetadataKey::Variable => "variable",
            MetadataKey::ImplCode => "impl_code",
            MetadataKey::TestCode => "test_code",
            MetadataKey::Pattern => "pattern",
            MetadataKey::Value => "value",
            MetadataKey::Min => "min",
            MetadataKey::Max => "max",
            MetadataKey::Source => "source",
            MetadataKey::Custom(s) => s,
        }
    }

    /// Parse from string
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Self {
        match s {
            "universe" => MetadataKey::Universe,
            "source_file" => MetadataKey::SourceFile,
            "rpc_name" => MetadataKey::RpcName,
            "extractor" => MetadataKey::Extractor,
            "inferred" => MetadataKey::Inferred,
            "variable" => MetadataKey::Variable,
            "impl_code" => MetadataKey::ImplCode,
            "test_code" => MetadataKey::TestCode,
            "pattern" => MetadataKey::Pattern,
            "value" => MetadataKey::Value,
            "min" => MetadataKey::Min,
            "max" => MetadataKey::Max,
            "source" => MetadataKey::Source,
            other => MetadataKey::Custom(other.to_string()),
        }
    }
}

impl From<&str> for MetadataKey {
    fn from(s: &str) -> Self {
        MetadataKey::from_str(s)
    }
}

impl From<String> for MetadataKey {
    fn from(s: String) -> Self {
        MetadataKey::from_str(&s)
    }
}
