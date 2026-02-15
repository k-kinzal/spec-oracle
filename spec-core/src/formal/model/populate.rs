/// Populate UDAFModel from SpecGraph

use std::collections::HashMap;
use crate::formal::*;
use crate::{SpecGraph, NodeKind, EdgeKind};
use super::UDAFModel;

impl UDAFModel {
    /// Populate UDAFModel from a SpecGraph
    ///
    /// This synchronizes the theoretical model with the practical graph representation.
    pub fn populate_from_graph(&mut self, graph: &SpecGraph) {
        // Clear existing data
        self.universes.clear();
        self.domains.clear();
        self.admissible_sets.clear();
        self.transforms.clear();

        // Always create U0
        let u0 = Universe::root();
        self.universes.insert(u0.id.clone(), u0);

        // Analyze nodes and populate universes
        for node in graph.list_nodes(None) {
            let layer = node.formality_layer;

            // Parse universe ID - skip if invalid
            let universe_id = match UniverseId::parse(&format!("U{}", layer)) {
                Ok(id) => id,
                Err(_) => continue,
            };

            // Create universe if it doesn't exist
            if !self.universes.contains_key(&universe_id) && layer > 0 {
                let (name, description) = match layer {
                    1 => ("Formal Specifications".to_string(), "Structured formal specifications".to_string()),
                    2 => ("Interface Definitions".to_string(), "Interface contracts and protocols".to_string()),
                    3 => ("Executable Implementations".to_string(), "Actual code implementations".to_string()),
                    _ => (format!("Layer {}", layer), format!("Layer {} specifications", layer)),
                };
                // add_universe now returns Result, but we can ignore errors here since we validated layer
                let _ = self.add_universe(layer, name, description);
            }

            // Parse spec ID - skip if invalid
            let spec_id = match SpecId::parse(&node.id) {
                Ok(id) => id,
                Err(_) => continue,
            };

            // Add spec to universe
            if let Some(universe) = self.universes.get_mut(&universe_id) {
                universe.specifications.insert(spec_id.clone());
            }

            // Create admissible set for this specification
            let mut admissible_set = AdmissibleSet::new(spec_id.clone(), universe_id.clone());

            // Extract constraints from content
            if node.kind == NodeKind::Constraint {
                // Convert graph metadata (HashMap<String, String>) to ConstraintMetadata
                let mut meta = ConstraintMetadata::from(node.metadata.clone());
                meta.insert(MetadataKey::Custom("description".to_string()), node.content.clone());

                admissible_set.add_constraint(Constraint {
                    // Layer 2: Proof data
                    formal: None,  // Will be extracted from meta.description during proof preparation
                    kind: ConstraintKind::Universal,
                    // OLD fields (for compatibility)
                    description: Some(node.content.clone()),
                    metadata: Some(ConstraintMetadata::from(node.metadata.clone())),
                    // NEW field (preferred)
                    meta: Some(meta),
                });
            } else {
                // For non-Constraint nodes, extract implicit constraints from natural language
                let extracted = self.extract_constraints_from_text(&node.content);
                for constraint in extracted {
                    admissible_set.add_constraint(constraint);
                }
            }

            self.admissible_sets.insert(spec_id.clone(), admissible_set);

            // Create domain if this is a Domain node
            if node.kind == NodeKind::Domain {
                let domain = Domain::with_id(
                    DomainId::parse(&node.id).unwrap_or_else(|_| DomainId::new()),
                    node.content.clone(),
                    "Domain boundary definition".to_string(),
                    universe_id,
                );
                self.domains.insert(domain.id.clone(), domain);
            }
        }

        // Analyze edges to create transform functions
        for (edge, source_id, target_id) in graph.list_edges(None) {
            if edge.kind == EdgeKind::Formalizes {
                // Create a transform function for this formalization
                let source_node = graph.get_node(source_id);
                let target_node = graph.get_node(target_id);

                if let (Some(source), Some(target)) = (source_node, target_node) {
                    // Parse universe IDs
                    let source_universe = match UniverseId::parse(&format!("U{}", source.formality_layer)) {
                        Ok(id) => id,
                        Err(_) => continue,
                    };
                    let target_universe = match UniverseId::parse(&format!("U{}", target.formality_layer)) {
                        Ok(id) => id,
                        Err(_) => continue,
                    };

                    // Create forward transform
                    let transform = TransformFunction::forward(
                        source_universe,
                        target_universe,
                        format!("Formalizes: {} -> {}",
                            source.content.chars().take(30).collect::<String>(),
                            target.content.chars().take(30).collect::<String>()),
                        TransformStrategy::Manual {
                            description: "Manual formalization via Formalizes edge".to_string(),
                        },
                    );
                    self.transforms.insert(transform.id.clone(), transform);
                }
            }
        }

        // Create inverse transforms for each projection universe to U0
        for (universe_id, _universe) in &self.universes {
            if universe_id.layer() == 0 {
                continue;  // Skip U0 itself
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
            self.transforms.insert(transform.id.clone(), transform);
        }
    }
}
