/// Type-safe ID system for UDAF model
///
/// This module provides strongly-typed identifiers for Universe, Domain, Spec, and Transform
/// to prevent type confusion and enforce naming conventions.

use serde::{Deserialize, Serialize, Deserializer, Serializer};
use std::fmt;
use uuid::Uuid;

/// Error type for ID parsing and validation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdError {
    InvalidFormat(String),
    InvalidLayer(String),
    InvalidUuid(String),
}

impl fmt::Display for IdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IdError::InvalidFormat(msg) => write!(f, "Invalid ID format: {}", msg),
            IdError::InvalidLayer(msg) => write!(f, "Invalid layer: {}", msg),
            IdError::InvalidUuid(msg) => write!(f, "Invalid UUID: {}", msg),
        }
    }
}

impl std::error::Error for IdError {}

/// Universe identifier with enforced "U{layer}" format
///
/// Valid formats: "U0", "U1", "U2", etc.
/// Layer must be a non-negative integer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UniverseId(String);

impl UniverseId {
    /// Create U0 (root universe)
    pub fn root() -> Self {
        Self("U0".to_string())
    }

    /// Create a projection universe (U1, U2, ...)
    pub fn projection(layer: u8) -> Result<Self, IdError> {
        if layer == 0 {
            return Err(IdError::InvalidLayer(
                "Use UniverseId::root() for U0".to_string(),
            ));
        }
        Ok(Self(format!("U{}", layer)))
    }

    /// Parse from string, validating format
    pub fn parse(s: &str) -> Result<Self, IdError> {
        if !s.starts_with('U') {
            return Err(IdError::InvalidFormat(
                format!("Universe ID must start with 'U', got: {}", s),
            ));
        }

        let layer_str = &s[1..];
        layer_str.parse::<u8>().map_err(|_| {
            IdError::InvalidFormat(format!("Invalid layer number in: {}", s))
        })?;

        Ok(Self(s.to_string()))
    }

    /// Get the layer number
    pub fn layer(&self) -> u8 {
        self.0[1..].parse().unwrap_or(0)
    }

    /// Get the string representation
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for UniverseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for UniverseId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for UniverseId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        UniverseId::parse(&s).map_err(serde::de::Error::custom)
    }
}

/// Domain identifier (UUID-based)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DomainId(String);

impl DomainId {
    /// Create a new domain ID (generates UUID)
    pub fn new() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    /// Parse from string (validates UUID format)
    pub fn parse(s: &str) -> Result<Self, IdError> {
        Uuid::parse_str(s).map_err(|_| {
            IdError::InvalidUuid(format!("Invalid UUID for DomainId: {}", s))
        })?;
        Ok(Self(s.to_string()))
    }

    /// Get the string representation
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for DomainId {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for DomainId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for DomainId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for DomainId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        DomainId::parse(&s).map_err(serde::de::Error::custom)
    }
}

/// Specification identifier (UUID-based)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SpecId(String);

impl SpecId {
    /// Create a new spec ID (generates UUID)
    pub fn new() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    /// Parse from string (validates UUID format)
    pub fn parse(s: &str) -> Result<Self, IdError> {
        Uuid::parse_str(s).map_err(|_| {
            IdError::InvalidUuid(format!("Invalid UUID for SpecId: {}", s))
        })?;
        Ok(Self(s.to_string()))
    }

    /// Get the string representation
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for SpecId {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for SpecId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for SpecId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for SpecId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        SpecId::parse(&s).map_err(serde::de::Error::custom)
    }
}

/// Transform function identifier with enforced "f_{source}_to_{target}" format
///
/// Valid formats:
/// - "f_U1_to_U0" (inverse mapping)
/// - "f_U1_to_U2" (forward/parallel mapping)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_universe_id_root() {
        let id = UniverseId::root();
        assert_eq!(id.as_str(), "U0");
        assert_eq!(id.layer(), 0);
    }

    #[test]
    fn test_universe_id_projection() {
        let id = UniverseId::projection(3).unwrap();
        assert_eq!(id.as_str(), "U3");
        assert_eq!(id.layer(), 3);
    }

    #[test]
    fn test_universe_id_projection_rejects_zero() {
        assert!(UniverseId::projection(0).is_err());
    }

    #[test]
    fn test_universe_id_parse_valid() {
        let id = UniverseId::parse("U5").unwrap();
        assert_eq!(id.layer(), 5);
    }

    #[test]
    fn test_universe_id_parse_invalid() {
        assert!(UniverseId::parse("X5").is_err());
        assert!(UniverseId::parse("Uabc").is_err());
        assert!(UniverseId::parse("5").is_err());
    }

    #[test]
    fn test_domain_id_new() {
        let id = DomainId::new();
        assert!(Uuid::parse_str(id.as_str()).is_ok());
    }

    #[test]
    fn test_spec_id_new() {
        let id = SpecId::new();
        assert!(Uuid::parse_str(id.as_str()).is_ok());
    }

    #[test]
    fn test_transform_id_inverse() {
        let source = UniverseId::projection(2).unwrap();
        let id = TransformId::inverse(&source);
        assert_eq!(id.as_str(), "f_U2_to_U0");
        assert_eq!(id.source().as_str(), "U2");
        assert_eq!(id.target().as_str(), "U0");
    }

    #[test]
    fn test_transform_id_forward() {
        let source = UniverseId::projection(1).unwrap();
        let target = UniverseId::projection(2).unwrap();
        let id = TransformId::forward(&source, &target);
        assert_eq!(id.as_str(), "f_U1_to_U2");
        assert_eq!(id.source().as_str(), "U1");
        assert_eq!(id.target().as_str(), "U2");
    }

    #[test]
    fn test_transform_id_parse_valid() {
        let id = TransformId::parse("f_U3_to_U1").unwrap();
        assert_eq!(id.source().as_str(), "U3");
        assert_eq!(id.target().as_str(), "U1");
    }

    #[test]
    fn test_transform_id_parse_invalid() {
        assert!(TransformId::parse("invalid").is_err());
        assert!(TransformId::parse("f_U1").is_err());
        assert!(TransformId::parse("U1_to_U2").is_err());
        assert!(TransformId::parse("f_X1_to_U2").is_err());
    }
}
