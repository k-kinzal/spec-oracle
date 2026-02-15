/// Type-safe set of domain IDs
///
/// Internally stores HashSet<String> for serialization compatibility,
/// but enforces type safety through the API.
use serde::{Deserialize, Serialize, Deserializer, Serializer};
use std::collections::HashSet;
use super::DomainId;
use crate::formal::IdError;

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
    pub fn insert_str(&mut self, id_str: String) -> Result<bool, IdError> {
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
    pub fn validate(&self) -> Result<(), IdError> {
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

impl From<Vec<String>> for DomainSet {
    fn from(vec: Vec<String>) -> Self {
        Self {
            inner: vec.into_iter().collect(),
        }
    }
}

impl From<DomainSet> for HashSet<String> {
    fn from(set: DomainSet) -> Self {
        set.inner
    }
}

impl Serialize for DomainSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for DomainSet {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let inner = HashSet::<String>::deserialize(deserializer)?;
        Ok(Self { inner })
    }
}
