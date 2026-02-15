/// Serde helpers for HashMap with typed IDs

use serde::{Serialize, Deserialize};
use serde::de::Deserializer;
use serde::ser::Serializer;
use std::collections::HashMap;
use crate::formal::*;

pub mod universe_map_serde {
    use super::*;

    pub fn serialize<S>(map: &HashMap<UniverseId, Universe>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, Universe> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<UniverseId, Universe>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, Universe>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                UniverseId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

pub mod domain_map_serde {
    use super::*;

    pub fn serialize<S>(map: &HashMap<DomainId, Domain>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, Domain> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<DomainId, Domain>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, Domain>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                DomainId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

pub mod admissible_map_serde {
    use super::*;

    pub fn serialize<S>(map: &HashMap<SpecId, AdmissibleSet>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, AdmissibleSet> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<SpecId, AdmissibleSet>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, AdmissibleSet>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                SpecId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}

pub mod transform_map_serde {
    use super::*;

    pub fn serialize<S>(map: &HashMap<TransformId, TransformFunction>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, TransformFunction> = map
            .iter()
            .map(|(k, v)| (k.as_str().to_string(), v.clone()))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<TransformId, TransformFunction>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map = HashMap::<String, TransformFunction>::deserialize(deserializer)?;
        string_map
            .into_iter()
            .map(|(k, v)| {
                TransformId::parse(&k)
                    .map(|id| (id, v))
                    .map_err(serde::de::Error::custom)
            })
            .collect()
    }
}
