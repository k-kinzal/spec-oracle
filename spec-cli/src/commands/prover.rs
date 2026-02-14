/// Formal verification commands using Prover and U/D/A/f model
///
/// This module implements formal proof commands that leverage the Prover
/// to verify consistency, satisfiability, and inspect the U/D/A/f model structure.

use spec_core::{Store, Prover, UDAFModel, NodeKind, EdgeKind, ProofStatus};
use crate::utils::parse_formality_layer;

/// Execute ProveConsistency command in standalone mode
pub fn execute_prove_consistency_standalone(
    store: &Store,
    spec_a: String,
    spec_b: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔬 Proving Consistency Between Specifications\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get the specifications
    let node_a = graph.get_node(&spec_a);
    let node_b = graph.get_node(&spec_b);

    if node_a.is_none() {
        eprintln!("❌ Specification A '{}' not found", spec_a);
        std::process::exit(1);
    }
    if node_b.is_none() {
        eprintln!("❌ Specification B '{}' not found", spec_b);
        std::process::exit(1);
    }

    let node_a = node_a.unwrap();
    let node_b = node_b.unwrap();

    println!("📋 Specification A:");
    println!("   ID:      [{}]", &spec_a[..8]);
    println!("   Content: {}", node_a.content);
    println!("   Kind:    {:?}", node_a.kind);
    println!();

    println!("📋 Specification B:");
    println!("   ID:      [{}]", &spec_b[..8]);
    println!("   Content: {}", node_b.content);
    println!("   Kind:    {:?}", node_b.kind);
    println!();

    // Get admissible sets
    let admissible_a = udaf_model.admissible_sets.get(&spec_a);
    let admissible_b = udaf_model.admissible_sets.get(&spec_b);

    if admissible_a.is_none() || admissible_b.is_none() {
        println!("⚠️  Admissible sets not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    let admissible_a = admissible_a.unwrap();
    let admissible_b = admissible_b.unwrap();

    println!("🔍 Admissible Set A: {} constraints", admissible_a.constraints.len());
    for (i, constraint) in admissible_a.constraints.iter().enumerate() {
        println!("   {}: {} ({:?})", i+1, constraint.description, constraint.kind);
    }
    println!();

    println!("🔍 Admissible Set B: {} constraints", admissible_b.constraints.len());
    for (i, constraint) in admissible_b.constraints.iter().enumerate() {
        println!("   {}: {} ({:?})", i+1, constraint.description, constraint.kind);
    }
    println!();

    // Prove consistency
    let mut prover = Prover::new();
    let proof = prover.prove_consistency(admissible_a, admissible_b);

    println!("═══════════════════════════════════════════════════════════════\n");
    println!("📜 Formal Proof Generated\n");
    println!("Property: {:?}", proof.property);
    println!("Method:   {:?}", proof.method);
    println!("Status:   {:?}", proof.status);
    println!();

    println!("Proof Steps:");
    for (i, step) in proof.steps.iter().enumerate() {
        println!("  {}. {}", i+1, step.description);
        println!("     Justification: {}", step.justification);
        println!();
    }

    match proof.status {
        ProofStatus::Proven => {
            println!("✅ PROVEN: Specifications are consistent");
            println!("   ∃x. (x ∈ A₁ ∧ x ∈ A₂) - There exists an implementation satisfying both");
        }
        ProofStatus::Refuted => {
            println!("❌ REFUTED: Specifications contradict each other");
            println!("   A₁ ∩ A₂ = ∅ - Admissible sets are disjoint");
            println!("   No implementation can satisfy both specifications simultaneously");
        }
        ProofStatus::Unknown => {
            println!("❓ UNKNOWN: Could not prove or refute");
            println!("   Current solver is incomplete (heuristic-based)");
            println!("   SMT solver integration needed for complete verification");
        }
        ProofStatus::Pending => {
            println!("⏳ PENDING: Proof in progress");
        }
    }

    Ok(())
}

/// Execute ProveSatisfiability command in standalone mode
pub fn execute_prove_satisfiability_standalone(
    store: &Store,
    spec: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔬 Proving Satisfiability of Specification\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get the specification
    let node = graph.get_node(&spec);

    if node.is_none() {
        eprintln!("❌ Specification '{}' not found", spec);
        std::process::exit(1);
    }

    let node = node.unwrap();

    println!("📋 Specification:");
    println!("   ID:      [{}]", &spec[..8]);
    println!("   Content: {}", node.content);
    println!("   Kind:    {:?}", node.kind);
    println!();

    // Get admissible set
    let admissible = udaf_model.admissible_sets.get(&spec);

    if admissible.is_none() {
        println!("⚠️  Admissible set not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    let admissible = admissible.unwrap();

    println!("🔍 Admissible Set: {} constraints", admissible.constraints.len());
    for (i, constraint) in admissible.constraints.iter().enumerate() {
        println!("   {}: {} ({:?})", i+1, constraint.description, constraint.kind);
    }
    println!();

    // Prove satisfiability
    let mut prover = Prover::new();
    let proof = prover.prove_satisfiability(admissible);

    println!("═══════════════════════════════════════════════════════════════\n");
    println!("📜 Formal Proof Generated\n");
    println!("Property: {:?}", proof.property);
    println!("Method:   {:?}", proof.method);
    println!("Status:   {:?}", proof.status);
    println!();

    println!("Proof Steps:");
    for (i, step) in proof.steps.iter().enumerate() {
        println!("  {}. {}", i+1, step.description);
        println!("     Justification: {}", step.justification);
        println!();
    }

    match proof.status {
        ProofStatus::Proven => {
            println!("✅ PROVEN: Specification is satisfiable");
            println!("   ∃x. x ∈ A - There exists an implementation satisfying the specification");
        }
        ProofStatus::Refuted => {
            println!("❌ REFUTED: Specification is unsatisfiable");
            println!("   A = ∅ - Admissible set is empty");
            println!("   No implementation can satisfy this specification");
        }
        ProofStatus::Unknown => {
            println!("❓ UNKNOWN: Could not prove or refute");
            println!("   Current solver is incomplete (heuristic-based)");
            println!("   SMT solver integration needed for complete verification");
        }
        ProofStatus::Pending => {
            println!("⏳ PENDING: Proof in progress");
        }
    }

    Ok(())
}

/// Execute InspectModel command in standalone mode
pub fn execute_inspect_model_standalone(
    store: &Store,
    verbose: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;

    println!("🔍 Inspecting U/D/A/f Model Structure\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Populate UDAFModel from graph
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("📊 Populating U/D/A/f model from SpecGraph...\n");

    // Analyze Universes (U)
    println!("📦 Universes (U):");
    println!("   The specification space is stratified into formality layers:\n");

    let mut layer_stats = std::collections::HashMap::new();
    let mut universe_metadata = std::collections::HashMap::new();

    for node in graph.list_nodes(None) {
        let layer = parse_formality_layer(node.formality_layer as u8);
        *layer_stats.entry(layer).or_insert(0) += 1;

        if let Some(universe) = node.metadata.get("universe") {
            *universe_metadata.entry(universe.clone()).or_insert(0) += 1;
        }
    }

    for layer in 0..=3 {
        let count = layer_stats.get(&layer).unwrap_or(&0);
        let layer_name = match layer {
            0 => "U0 (Root Requirements)",
            1 => "U1 (Formal Specifications)",
            2 => "U2 (Interface Definitions)",
            3 => "U3 (Executable Implementations)",
            _ => "U? (Unknown)",
        };
        let udaf_count = udaf_model.universes.get(&format!("U{}", layer))
            .map(|u| u.specifications.len())
            .unwrap_or(0);
        println!("   • {}: {} specifications (UDAFModel: {})", layer_name, count, udaf_count);
    }
    println!();

    if !universe_metadata.is_empty() {
        println!("   Distinct universe tags:");
        for (universe, count) in &universe_metadata {
            println!("     - \"{}\": {} nodes", universe, count);
        }
        println!();
    }

    // Analyze Domains (D)
    println!("🌐 Domains (D):");
    println!("   The target scope of specifications:\n");

    let domain_nodes: Vec<_> = graph.list_nodes(Some(NodeKind::Domain));

    if domain_nodes.is_empty() {
        println!("   ⚠️  No explicit domain boundaries defined");
        println!("      (Domain definitions help prevent specification leakage)\n");
    } else {
        for node in &domain_nodes {
            println!("   • [{}] {}", &node.id[..8], node.content);
        }
        println!();
    }

    // Analyze Admissible Sets (A)
    println!("✓ Admissible Sets (A):");
    println!("   The set of permitted implementations for each specification:\n");

    let constraint_count = graph.list_nodes(Some(NodeKind::Constraint)).len();
    let assertion_count = graph.list_nodes(Some(NodeKind::Assertion)).len();
    let scenario_count = graph.list_nodes(Some(NodeKind::Scenario)).len();

    println!("   • Constraints (∀): {} universal invariants", constraint_count);
    println!("   • Assertions:      {} concrete claims", assertion_count);
    println!("   • Scenarios (∃):   {} existential requirements", scenario_count);
    println!();
    println!("   Note: Each specification implicitly defines A = {{impl | impl satisfies spec}}");
    println!("         Explicit A computation is not yet implemented.\n");

    // Analyze Transform Functions (f)
    println!("🔗 Transform Functions (f):");
    println!("   Mappings between universes that preserve specification semantics:\n");

    let mut transform_counts = std::collections::HashMap::new();

    for (edge, _source, _target) in graph.list_edges(None) {
        *transform_counts.entry(edge.kind.clone()).or_insert(0) += 1;
    }

    for (kind, count) in &transform_counts {
        let description = match kind {
            EdgeKind::Formalizes => "f: Ui → Uj (formalization)",
            EdgeKind::Transform => "f: Ui → Uj (transformation)",
            EdgeKind::Refines => "refinement (within-layer)",
            EdgeKind::DerivesFrom => "derivation (provenance)",
            EdgeKind::DependsOn => "dependency",
            EdgeKind::Contradicts => "contradiction (⊥)",
            EdgeKind::Synonym => "equivalence (≡)",
            EdgeKind::Composes => "composition",
        };
        println!("   • {:20}: {} edges", description, count);
    }
    println!();

    // Show UDAFModel transforms
    println!("   UDAFModel Transforms:");
    println!("   {} transform functions defined", udaf_model.transforms.len());
    if verbose {
        for (id, transform) in &udaf_model.transforms {
            println!("     - {}: {} -> {}", id, transform.source_universe, transform.target_universe);
            println!("       Strategy: {:?}", transform.kind);
        }
    }
    println!();

    // Theory alignment
    println!("📐 Theoretical Model Status:");
    println!("   From conversation.md and motivation.md:\n");

    println!("   ✅ U (Universe):       Implemented via formality_layer (0-3)");
    println!("   ⚠️  D (Domain):         Partially implemented (NodeKind::Domain exists)");
    println!("   ✅ A (Admissible Set): Populated from graph nodes");
    println!("   ✅ f (Transform):      Transform functions NOW EXECUTABLE via RustExtractor");
    println!();

    println!("   Key insight from motivation.md:");
    println!("   U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ f₀₃⁻¹(U3)");
    println!("   (Root specs are the union of inverse mappings from all layers)\n");

    // Verification metrics
    println!("📊 Model Consistency:");
    let complete_ratio = if let Some(&u0_count) = layer_stats.get(&0) {
        let complete = layer_stats.get(&3).unwrap_or(&0);
        (complete * 100) / u0_count.max(1)
    } else {
        0
    };

    println!("   Completeness estimate:  ~{}%", complete_ratio);
    println!("   (Percentage of U0 requirements with U3 implementations)");
    println!("   Run 'spec verify-layers' for precise multi-layer verification.\n");

    if verbose {
        println!("═══════════════════════════════════════════════════════════════");
        println!("Verbose Mode: Detailed Node Distribution\n");

        for layer in 0..=3 {
            let layer_name = match layer {
                0 => "U0",
                1 => "U1",
                2 => "U2",
                3 => "U3",
                _ => "U?",
            };

            let layer_nodes: Vec<_> = graph.list_nodes(None).into_iter()
                .filter(|n| parse_formality_layer(n.formality_layer) == layer)
                .collect();

            if !layer_nodes.is_empty() {
                println!("{} Specifications ({}):", layer_name, layer_nodes.len());
                for node in layer_nodes.iter().take(5) {
                    let preview = if node.content.len() > 60 {
                        format!("{}...", &node.content[..57])
                    } else {
                        node.content.clone()
                    };
                    println!("  • [{}] {}", &node.id[..8], preview);
                }
                if layer_nodes.len() > 5 {
                    println!("  ... and {} more", layer_nodes.len() - 5);
                }
                println!();
            }
        }
    }

    println!("═══════════════════════════════════════════════════════════════");

    Ok(())
}
