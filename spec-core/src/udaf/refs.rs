/// Type-safe reference set system for UDAF model
///
/// This module provides strongly-typed ID collections to ensure that
/// reference sets only contain valid IDs of the correct type.

use serde::{Deserialize, Serialize, Deserializer, Serializer};
use std::collections::HashSet;
use super::ids::{SpecId, DomainId};

/// Type-safe set of specification IDs
///
/// Internally stores HashSet<String> for serialization compatibility,
/// but enforces type safety through the API.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecSet {
    inner: HashSet<String>,
}

impl SpecSet {
    /// Create an empty set
    pub fn new() -> Self {
        Self {
            inner: HashSet::new(),
        }
    }

    /// Insert a specification ID
    pub fn insert(&mut self, id: SpecId) -> bool {
        self.inner.insert(id.as_str().to_string())
    }

    /// Insert a specification ID from string (validates format)
    pub fn insert_str(&mut self, id_str: String) -> Result<bool, super::ids::IdError> {
        let id = SpecId::parse(&id_str)?;
        Ok(self.inner.insert(id.as_str().to_string()))
    }

    /// Check if set contains a specification ID
    pub fn contains(&self, id: &SpecId) -> bool {
        self.inner.contains(id.as_str())
    }

    /// Check if set contains an ID string (for compatibility)
    pub fn contains_str(&self, id_str: &str) -> bool {
        self.inner.contains(id_str)
    }

    /// Remove a specification ID
    pub fn remove(&mut self, id: &SpecId) -> bool {
        self.inner.remove(id.as_str())
    }

    /// Get the number of IDs in the set
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if the set is empty
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Iterate over IDs as strings (for compatibility)
    pub fn iter_str(&self) -> impl Iterator<Item = &String> {
        self.inner.iter()
    }

    /// Iterate over parsed SpecIds
    ///
    /// Note: This validates each ID during iteration. IDs that fail validation are skipped.
    pub fn iter(&self) -> impl Iterator<Item = SpecId> + '_ {
        self.inner.iter().filter_map(|s| SpecId::parse(s).ok())
    }

    /// Validate all IDs in the set
    ///
    /// Returns Err if any ID fails to parse as a valid SpecId.
    pub fn validate(&self) -> Result<(), super::ids::IdError> {
        for id_str in &self.inner {
            SpecId::parse(id_str)?;
        }
        Ok(())
    }

    /// Check reference integrity: all IDs in this set exist in the given set
    ///
    /// Returns the list of IDs that don't exist in the reference set.
    pub fn check_integrity(&self, valid_ids: &HashSet<String>) -> Vec<String> {
        self.inner
            .iter()
            .filter(|id| !valid_ids.contains(*id))
            .cloned()
            .collect()
    }

    /// Get the inner HashSet (for direct access when needed)
    pub fn inner(&self) -> &HashSet<String> {
        &self.inner
    }

    /// Get mutable reference to inner HashSet
    pub fn inner_mut(&mut self) -> &mut HashSet<String> {
        &mut self.inner
    }
}

impl Default for SpecSet {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashSet<String>> for SpecSet {
    fn from(set: HashSet<String>) -> Self {
        Self { inner: set }
    }
}

impl From<SpecSet> for HashSet<String> {
    fn from(set: SpecSet) -> Self {
        set.inner
    }
}

impl Serialize for SpecSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for SpecSet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let inner = HashSet::<String>::deserialize(deserializer)?;
        Ok(Self { inner })
    }
}

/// Type-safe set of domain IDs
///
/// Internally stores HashSet<String> for serialization compatibility,
/// but enforces type safety through the API.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainSet {
    inner: HashSet<String>,
}

impl DomainSet {
    /// Create an empty set
    pub fn new() -> Self {
        Self {
            inner: HashSet::new(),
        }
    }

    /// Insert a domain ID
    pub fn insert(&mut self, id: DomainId) -> bool {
        self.inner.insert(id.as_str().to_string())
    }

    /// Insert a domain ID from string (validates format)
    pub fn insert_str(&mut self, id_str: String) -> Result<bool, super::ids::IdError> {
        let id = DomainId::parse(&id_str)?;
        Ok(self.inner.insert(id.as_str().to_string()))
    }

    /// Check if set contains a domain ID
    pub fn contains(&self, id: &DomainId) -> bool {
        self.inner.contains(id.as_str())
    }

    /// Check if set contains an ID string (for compatibility)
    pub fn contains_str(&self, id_str: &str) -> bool {
        self.inner.contains(id_str)
    }

    /// Remove a domain ID
    pub fn remove(&mut self, id: &DomainId) -> bool {
        self.inner.remove(id.as_str())
    }

    /// Get the number of IDs in the set
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if the set is empty
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Iterate over IDs as strings (for compatibility)
    pub fn iter_str(&self) -> impl Iterator<Item = &String> {
        self.inner.iter()
    }

    /// Iterate over parsed DomainIds
    ///
    /// Note: This validates each ID during iteration. IDs that fail validation are skipped.
    pub fn iter(&self) -> impl Iterator<Item = DomainId> + '_ {
        self.inner.iter().filter_map(|s| DomainId::parse(s).ok())
    }

    /// Validate all IDs in the set
    ///
    /// Returns Err if any ID fails to parse as a valid DomainId.
    pub fn validate(&self) -> Result<(), super::ids::IdError> {
        for id_str in &self.inner {
            DomainId::parse(id_str)?;
        }
        Ok(())
    }

    /// Check reference integrity: all IDs in this set exist in the given set
    ///
    /// Returns the list of IDs that don't exist in the reference set.
    pub fn check_integrity(&self, valid_ids: &HashSet<String>) -> Vec<String> {
        self.inner
            .iter()
            .filter(|id| !valid_ids.contains(*id))
            .cloned()
            .collect()
    }

    /// Get the inner HashSet (for direct access when needed)
    pub fn inner(&self) -> &HashSet<String> {
        &self.inner
    }

    /// Get mutable reference to inner HashSet
    pub fn inner_mut(&mut self) -> &mut HashSet<String> {
        &mut self.inner
    }

    /// Convert to Vec for compatibility (since subdomains was Vec<String>)
    pub fn to_vec(&self) -> Vec<String> {
        self.inner.iter().cloned().collect()
    }

    /// Create from Vec for compatibility
    pub fn from_vec(vec: Vec<String>) -> Self {
        Self {
            inner: vec.into_iter().collect(),
        }
    }
}

impl Default for DomainSet {
    fn default() -> Self {
        Self::new()
    }
}

impl From<HashSet<String>> for DomainSet {
    fn from(set: HashSet<String>) -> Self {
        Self { inner: set }
    }
}

impl From<DomainSet> for HashSet<String> {
    fn from(set: DomainSet) -> Self {
        set.inner
    }
}

impl From<Vec<String>> for DomainSet {
    fn from(vec: Vec<String>) -> Self {
        Self::from_vec(vec)
    }
}

impl From<DomainSet> for Vec<String> {
    fn from(set: DomainSet) -> Self {
        set.to_vec()
    }
}

impl Serialize for DomainSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Serialize as Vec to match the original Vec<String> format
        let vec: Vec<String> = self.to_vec();
        vec.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for DomainSet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let vec = Vec::<String>::deserialize(deserializer)?;
        Ok(Self::from_vec(vec))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spec_set_insert_contains() {
        let mut set = SpecSet::new();
        let id = SpecId::new();

        assert!(set.insert(id.clone()));
        assert!(set.contains(&id));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_spec_set_validate() {
        let mut set = SpecSet::new();
        set.insert(SpecId::new());
        set.insert(SpecId::new());

        assert!(set.validate().is_ok());
    }

    #[test]
    fn test_spec_set_check_integrity() {
        let mut set = SpecSet::new();
        let id1 = SpecId::new();
        let id2 = SpecId::new();
        set.insert(id1.clone());
        set.insert(id2.clone());

        let mut valid = HashSet::new();
        valid.insert(id1.as_str().to_string());

        let missing = set.check_integrity(&valid);
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0], id2.as_str());
    }

    #[test]
    fn test_domain_set_insert_contains() {
        let mut set = DomainSet::new();
        let id = DomainId::new();

        assert!(set.insert(id.clone()));
        assert!(set.contains(&id));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_domain_set_vec_conversion() {
        let id1 = DomainId::new();
        let id2 = DomainId::new();

        let vec = vec![id1.as_str().to_string(), id2.as_str().to_string()];
        let set = DomainSet::from_vec(vec.clone());

        assert_eq!(set.len(), 2);

        let converted_vec = set.to_vec();
        assert_eq!(converted_vec.len(), 2);
    }

    #[test]
    fn test_spec_set_serialization() {
        let mut set = SpecSet::new();
        set.insert(SpecId::new());

        let json = serde_json::to_string(&set).unwrap();
        let deserialized: SpecSet = serde_json::from_str(&json).unwrap();

        assert_eq!(set.len(), deserialized.len());
    }

    #[test]
    fn test_domain_set_serialization() {
        let mut set = DomainSet::new();
        set.insert(DomainId::new());

        let json = serde_json::to_string(&set).unwrap();
        let deserialized: DomainSet = serde_json::from_str(&json).unwrap();

        assert_eq!(set.len(), deserialized.len());
    }
}
