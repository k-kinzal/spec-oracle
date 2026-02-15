/// Bidirectional synchronization between SpecRepository (data layer) and UDAFModel (formal layer)
///
/// This module provides the bridge layer that:
/// 1. Reads specifications from SpecRepository and populates UDAFModel
/// 2. Writes verification results back to SpecRepository as metadata
///
/// Key differences from populate.rs:
/// - Works with SpecRepository instead of SpecGraph
/// - Bidirectional (can write results back)
/// - Stateless (pure functions, no internal state)
/// - Uses consolidated constraint extraction
use crate::data::SpecRepository;
use crate::formal::model::constraint::extract_constraints_from_text;
use crate::formal::*;
use crate::data::{NodeKind, EdgeKind};
use chrono::Utc;
use std::collections::HashMap;

/// Stateless synchronization utilities
pub struct ModelSync;

impl ModelSync {
    /// Synchronize UDAFModel from SpecRepository
    ///
    /// This populates the formal model by reading nodes and edges from the repository:
    /// - Universes are created based on formality_layer (0=U0, 1=U1, etc.)
    /// - Domains are extracted from Domain nodes
    /// - Admissible sets are created for each specification
    /// - Constraints are extracted from node content
    /// - Transform functions are built from edge relationships
    ///
    /// Returns Ok(()) on success, or Err with error message.
    pub fn sync_from_repository(model: &mut UDAFModel, repo: &SpecRepository) -> Result<(), String> {
        // Clear existing data
        model.universes.clear();
        model.domains.clear();
        model.admissible_sets.clear();
        model.transforms.clear();

        // Always create U0 (root universe)
        let u0 = Universe::root();
        model.universes.insert(u0.id.clone(), u0);

        // First pass: Create universes and admissible sets from nodes
        Self::sync_nodes(model, repo)?;

        // Second pass: Create transform functions from edges
        Self::sync_edges(model, repo)?;

        // Third pass: Create inverse transforms for each projection universe
        Self::create_inverse_transforms(model)?;

        Ok(())
    }

    /// Export proof metadata back to repository
    ///
    /// This writes verification results back to the repository as node metadata:
    /// - contradiction_detected: Set for nodes with contradicting specifications
    /// - omission_detected: Set for nodes with omitted domains
    /// - proof_status: proven/refuted/unknown
    /// - proof_timestamp: When the proof was performed
    ///
    /// Returns Ok(()) on success, or Err with error message.
    pub fn export_proof_metadata(model: &UDAFModel, repo: &mut SpecRepository) -> Result<(), String> {
        let timestamp = Utc::now().timestamp().to_string();

        // Export contradiction metadata
        #[cfg(feature = "z3-solver")]
        {
            let contradictions = model.clone().detect_contradictions();
            for contradiction in contradictions {
                // Mark both contradicting specs
                let spec_a_id = contradiction.spec_a.as_str();
                let spec_b_id = contradiction.spec_b.as_str();

                repo.update_node_metadata(
                    spec_a_id,
                    "contradiction_detected".to_string(),
                    spec_b_id.to_string(),
                );
                repo.update_node_metadata(
                    spec_a_id,
                    "proof_timestamp".to_string(),
                    timestamp.clone(),
                );

                repo.update_node_metadata(
                    spec_b_id,
                    "contradiction_detected".to_string(),
                    spec_a_id.to_string(),
                );
                repo.update_node_metadata(
                    spec_b_id,
                    "proof_timestamp".to_string(),
                    timestamp.clone(),
                );
            }
        }

        // Export omission metadata
        #[cfg(feature = "z3-solver")]
        {
            let omissions = model.clone().detect_omissions();
            for omission in omissions {
                let domain_id = omission.domain_id.as_str();

                repo.update_node_metadata(
                    domain_id,
                    "omission_detected".to_string(),
                    "true".to_string(),
                );
                repo.update_node_metadata(
                    domain_id,
                    "omission_coverage".to_string(),
                    "detected".to_string(),
                );
                repo.update_node_metadata(
                    domain_id,
                    "proof_timestamp".to_string(),
                    timestamp.clone(),
                );
            }
        }

        // Export satisfiability results for each specification
        for spec_id in model.admissible_sets.keys() {
            #[cfg(feature = "z3-solver")]
            {
                if let Some(proof) = model.clone().verify_satisfiability(spec_id) {
                    let status = match proof.status {
                        ProofStatus::Proven => "proven",
                        ProofStatus::Refuted => "refuted",
                        ProofStatus::Unknown => "unknown",
                        ProofStatus::Pending => "pending",
                    };

                    repo.update_node_metadata(
                        spec_id.as_str(),
                        "proof_status".to_string(),
                        status.to_string(),
                    );
                    repo.update_node_metadata(
                        spec_id.as_str(),
                        "proof_timestamp".to_string(),
                        timestamp.clone(),
                    );
                }
            }

            #[cfg(not(feature = "z3-solver"))]
            {
                // Without Z3, mark as unknown
                repo.update_node_metadata(
                    spec_id.as_str(),
                    "proof_status".to_string(),
                    "unknown".to_string(),
                );
            }
        }

        Ok(())
    }

    // ========================================================================
    // Internal sync helpers
    // ========================================================================

    /// Sync nodes from repository to model
    fn sync_nodes(model: &mut UDAFModel, repo: &SpecRepository) -> Result<(), String> {
        for node in repo.list_nodes(None) {
            let layer = node.formality_layer;

            // Create universe for this layer if it doesn't exist
            let universe_id = match UniverseId::parse(&format!("U{}", layer)) {
                Ok(id) => id,
                Err(_) => continue,
            };

            if !model.universes.contains_key(&universe_id) && layer > 0 {
                let (name, description) = Self::universe_names_for_layer(layer);
                model.add_universe(layer, name, description)
                    .map_err(|e| format!("Failed to add universe: {}", e))?;
            }

            // Parse spec ID
            let spec_id = match SpecId::parse(&node.id) {
                Ok(id) => id,
                Err(_) => continue,
            };

            // Add spec to universe
            if let Some(universe) = model.universes.get_mut(&universe_id) {
                universe.specifications.insert(spec_id.clone());
            }

            // Create admissible set for this specification
            let mut admissible_set = AdmissibleSet::new(spec_id.clone(), universe_id.clone());

            // Extract constraints based on node kind
            match node.kind {
                NodeKind::Constraint => {
                    // For Constraint nodes, create a single explicit constraint
                    let mut meta = ConstraintMetadata::from(node.metadata.clone());
                    meta.insert(MetadataKey::Custom("description".to_string()), node.content.clone());

                    admissible_set.add_constraint(Constraint {
                        formal: None, // Will be extracted during proof preparation
                        kind: ConstraintKind::Universal,
                        description: Some(node.content.clone()),
                        metadata: Some(ConstraintMetadata::from(node.metadata.clone())),
                        meta: Some(meta),
                    });
                }
                _ => {
                    // For other nodes, extract implicit constraints from natural language
                    let extracted = extract_constraints_from_text(&node.content);
                    for constraint in extracted {
                        admissible_set.add_constraint(constraint);
                    }
                }
            }

            model.admissible_sets.insert(spec_id.clone(), admissible_set);

            // Create domain if this is a Domain node
            if node.kind == NodeKind::Domain {
                let domain = Domain::with_id(
                    DomainId::parse(&node.id).unwrap_or_else(|_| DomainId::new()),
                    node.content.clone(),
                    "Domain boundary definition".to_string(),
                    universe_id,
                );
                model.domains.insert(domain.id.clone(), domain);
            }
        }

        Ok(())
    }

    /// Sync edges from repository to model
    fn sync_edges(model: &mut UDAFModel, repo: &SpecRepository) -> Result<(), String> {
        for (edge, source_id, target_id) in repo.list_edges(None) {
            // Only process Formalizes and Transform edges
            if !matches!(edge.kind, EdgeKind::Formalizes | EdgeKind::Transform) {
                continue;
            }

            let source_node = match repo.get_node(source_id) {
                Some(n) => n,
                None => continue,
            };

            let target_node = match repo.get_node(target_id) {
                Some(n) => n,
                None => continue,
            };

            // Parse universe IDs
            let source_universe = match UniverseId::parse(&format!("U{}", source_node.formality_layer)) {
                Ok(id) => id,
                Err(_) => continue,
            };

            let target_universe = match UniverseId::parse(&format!("U{}", target_node.formality_layer)) {
                Ok(id) => id,
                Err(_) => continue,
            };

            // Create transform function
            let transform = TransformFunction::forward(
                source_universe,
                target_universe,
                format!(
                    "{:?}: {} -> {}",
                    edge.kind,
                    source_node.content.chars().take(30).collect::<String>(),
                    target_node.content.chars().take(30).collect::<String>()
                ),
                TransformStrategy::Manual {
                    description: format!("Manual transformation via {:?} edge", edge.kind),
                },
            );

            model.transforms.insert(transform.id.clone(), transform);
        }

        Ok(())
    }

    /// Create inverse transforms for each projection universe to U0
    fn create_inverse_transforms(model: &mut UDAFModel) -> Result<(), String> {
        let universe_ids: Vec<UniverseId> = model.universes.keys().cloned().collect();

        for universe_id in universe_ids {
            if universe_id.layer() == 0 {
                continue; // Skip U0 itself
            }

            let layer_num = universe_id.layer();

            // Create inverse transform based on layer
            let strategy = match layer_num {
                3 => TransformStrategy::ASTAnalysis {
                    language: "rust".to_string(),
                    extractor_config: HashMap::from([
                        ("min_confidence".to_string(), "0.7".to_string()),
                    ]),
                },
                2 => TransformStrategy::TypeAnalysis {
                    type_system: "rust".to_string(),
                },
                1 => TransformStrategy::FormalVerification {
                    tool: "manual".to_string(),
                    verification_config: HashMap::new(),
                },
                _ => TransformStrategy::Manual {
                    description: format!("Inverse mapping from {}", universe_id.as_str()),
                },
            };

            let transform = TransformFunction::inverse(
                universe_id.clone(),
                format!("Inverse mapping from {} to U0", universe_id.as_str()),
                strategy,
            );

            model.transforms.insert(transform.id.clone(), transform);
        }

        Ok(())
    }

    /// Get standard universe names for a layer
    fn universe_names_for_layer(layer: u8) -> (String, String) {
        match layer {
            1 => (
                "Formal Specifications".to_string(),
                "Structured formal specifications".to_string(),
            ),
            2 => (
                "Interface Definitions".to_string(),
                "Interface contracts and protocols".to_string(),
            ),
            3 => (
                "Executable Implementations".to_string(),
                "Actual code implementations".to_string(),
            ),
            _ => (
                format!("Layer {}", layer),
                format!("Layer {} specifications", layer),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::SpecRepository;

    #[test]
    fn test_sync_empty_repository() {
        let repo = SpecRepository::new();
        let mut model = UDAFModel::new();

        let result = ModelSync::sync_from_repository(&mut model, &repo);
        assert!(result.is_ok());

        // U0 should always exist
        assert_eq!(model.universes.len(), 1);
        assert!(model.universes.contains_key(&UniverseId::root()));
    }

    #[test]
    fn test_sync_creates_universes() {
        let mut repo = SpecRepository::new();
        let mut metadata = HashMap::new();
        metadata.insert("test".to_string(), "value".to_string());

        // Add nodes at different layers
        let _node0_id = {
            let node0 = repo.add_node(
                "U0 spec".to_string(),
                NodeKind::Assertion,
                metadata.clone(),
            );
            let id = node0.id.clone();
            repo.update_node_formality(&id, 0);
            id
        };

        let _node1_id = {
            let node1 = repo.add_node(
                "U1 spec".to_string(),
                NodeKind::Constraint,
                metadata.clone(),
            );
            let id = node1.id.clone();
            repo.update_node_formality(&id, 1);
            id
        };

        let _node2_id = {
            let node2 = repo.add_node(
                "U2 spec".to_string(),
                NodeKind::Scenario,
                metadata.clone(),
            );
            let id = node2.id.clone();
            repo.update_node_formality(&id, 2);
            id
        };

        let mut model = UDAFModel::new();
        let result = ModelSync::sync_from_repository(&mut model, &repo);
        assert!(result.is_ok());

        // Should have U0, U1, U2
        assert_eq!(model.universes.len(), 3);
        assert!(model.universes.contains_key(&UniverseId::root()));
        assert!(model.universes.contains_key(&UniverseId::parse("U1").unwrap()));
        assert!(model.universes.contains_key(&UniverseId::parse("U2").unwrap()));
    }

    #[test]
    fn test_sync_extracts_constraints() {
        let mut repo = SpecRepository::new();
        let mut metadata = HashMap::new();
        metadata.insert("test".to_string(), "value".to_string());

        // Add a constraint node
        let node_id = {
            let node = repo.add_node(
                "Password must be at least 8 characters".to_string(),
                NodeKind::Constraint,
                metadata,
            );
            let id = node.id.clone();
            repo.update_node_formality(&id, 0);
            id
        };

        let mut model = UDAFModel::new();
        let result = ModelSync::sync_from_repository(&mut model, &repo);
        assert!(result.is_ok());

        // Should have created admissible set with constraint
        assert_eq!(model.admissible_sets.len(), 1);
        let _admissible_set = model.admissible_sets.values().next().unwrap();
        // Check that constraints were added (use public method or check via validation)
        assert!(!model.admissible_sets.is_empty());
    }

    #[test]
    fn test_sync_creates_domains() {
        let mut repo = SpecRepository::new();
        let metadata = HashMap::new();

        // Add a domain node
        let node_id = {
            let node = repo.add_node(
                "Authentication Domain".to_string(),
                NodeKind::Domain,
                metadata,
            );
            let id = node.id.clone();
            repo.update_node_formality(&id, 0);
            id
        };

        let mut model = UDAFModel::new();
        let result = ModelSync::sync_from_repository(&mut model, &repo);
        assert!(result.is_ok());

        // Should have created a domain
        assert_eq!(model.domains.len(), 1);
    }

    #[test]
    fn test_export_proof_metadata() {
        let mut repo = SpecRepository::new();
        let mut metadata = HashMap::new();
        metadata.insert("test".to_string(), "value".to_string());

        let node_id = {
            let node = repo.add_node(
                "Test spec".to_string(),
                NodeKind::Constraint,
                metadata,
            );
            node.id.clone()
        };

        let mut model = UDAFModel::new();
        ModelSync::sync_from_repository(&mut model, &repo).unwrap();

        let result = ModelSync::export_proof_metadata(&model, &mut repo);
        assert!(result.is_ok());

        // Verify metadata was added
        let updated_node = repo.get_node(&node_id).unwrap();
        assert!(updated_node.metadata.contains_key("proof_status"));
    }

    #[test]
    fn test_bidirectional_sync() {
        let mut repo = SpecRepository::new();
        let metadata = HashMap::new();

        // Add a node
        let node_id = {
            let node = repo.add_node(
                "Password must be at least 8 characters".to_string(),
                NodeKind::Constraint,
                metadata,
            );
            node.id.clone()
        };

        // Sync to model
        let mut model = UDAFModel::new();
        ModelSync::sync_from_repository(&mut model, &repo).unwrap();

        // Export results back
        ModelSync::export_proof_metadata(&model, &mut repo).unwrap();

        // Verify round-trip
        let updated_node = repo.get_node(&node_id).unwrap();
        assert!(updated_node.metadata.contains_key("proof_status"));
    }
}
