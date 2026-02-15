/// Transform function identifier with enforced "f_{source}_to_{target}" format
///
/// Valid formats:
/// - "f_U1_to_U0" (inverse mapping)
/// - "f_U1_to_U2" (forward/parallel mapping)
use serde::{Deserialize, Serialize, Deserializer, Serializer};
use std::fmt;
use crate::formal::universe::UniverseId;
use crate::formal::IdError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TransformId(String);

impl TransformId {
    /// Create an inverse mapping ID: f_{source}_to_U0
    pub fn inverse(source: &UniverseId) -> Self {
        Self(format!("f_{}_to_U0", source.as_str()))
    }

    /// Create a forward/parallel mapping ID: f_{source}_to_{target}
    pub fn forward(source: &UniverseId, target: &UniverseId) -> Self {
        Self(format!("f_{}_to_{}", source.as_str(), target.as_str()))
    }

    /// Parse from string (validates format)
    pub fn parse(s: &str) -> Result<Self, IdError> {
        if !s.starts_with("f_") {
            return Err(IdError::InvalidFormat(
                format!("Transform ID must start with 'f_', got: {}", s),
            ));
        }

        if !s.contains("_to_") {
            return Err(IdError::InvalidFormat(
                format!("Transform ID must contain '_to_', got: {}", s),
            ));
        }

        // Extract source and target
        let parts: Vec<&str> = s.split("_to_").collect();
        if parts.len() != 2 {
            return Err(IdError::InvalidFormat(
                format!("Invalid transform ID format: {}", s),
            ));
        }

        let source_part = parts[0].strip_prefix("f_").ok_or_else(|| {
            IdError::InvalidFormat(format!("Invalid source in: {}", s))
        })?;

        // Validate source and target as UniverseIds
        UniverseId::parse(source_part)?;
        UniverseId::parse(parts[1])?;

        Ok(Self(s.to_string()))
    }

    /// Get the source universe ID
    pub fn source(&self) -> UniverseId {
        let parts: Vec<&str> = self.0.split("_to_").collect();
        let source_str = parts[0].strip_prefix("f_").unwrap();
        UniverseId::parse(source_str).unwrap()
    }

    /// Get the target universe ID
    pub fn target(&self) -> UniverseId {
        let parts: Vec<&str> = self.0.split("_to_").collect();
        UniverseId::parse(parts[1]).unwrap()
    }

    /// Get the string representation
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for TransformId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for TransformId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for TransformId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        TransformId::parse(&s).map_err(serde::de::Error::custom)
    }
}
