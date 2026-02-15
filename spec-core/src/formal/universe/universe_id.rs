/// Universe identifier with enforced "U{layer}" format
///
/// Valid formats: "U0", "U1", "U2", etc.
/// Layer must be a non-negative integer.

use serde::{Deserialize, Serialize, Deserializer, Serializer};
use std::fmt;
use crate::formal::IdError;

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
        Self::parse(&s).map_err(serde::de::Error::custom)
    }
}

impl From<String> for UniverseId {
    fn from(s: String) -> Self {
        Self::parse(&s).expect("Invalid UniverseId format")
    }
}

impl From<&str> for UniverseId {
    fn from(s: &str) -> Self {
        Self::parse(s).expect("Invalid UniverseId format")
    }
}
