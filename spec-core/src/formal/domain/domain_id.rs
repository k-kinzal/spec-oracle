/// Domain identifier (UUID-based)
use serde::{Deserialize, Serialize, Deserializer, Serializer};
use std::fmt;
use uuid::Uuid;
use crate::formal::IdError;

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
