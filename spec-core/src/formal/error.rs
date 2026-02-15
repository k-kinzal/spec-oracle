/// Error type for ID parsing and validation

use std::fmt;

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
