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

/// Execute ProveImplication command in standalone mode
pub fn execute_prove_implication_standalone(
    store: &Store,
    antecedent_id: String,
    consequent_id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔬 Proving Implication Between Specifications\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get the specifications
    let node_a = graph.get_node(&antecedent_id);
    let node_b = graph.get_node(&consequent_id);

    if node_a.is_none() {
        eprintln!("❌ Specification (antecedent) '{}' not found", antecedent_id);
        std::process::exit(1);
    }
    if node_b.is_none() {
        eprintln!("❌ Specification (consequent) '{}' not found", consequent_id);
        std::process::exit(1);
    }

    let node_a = node_a.unwrap();
    let node_b = node_b.unwrap();

    println!("📋 Antecedent (A1):");
    println!("   ID:      [{}]", &antecedent_id[..8]);
    println!("   Content: {}", node_a.content);
    println!("   Kind:    {:?}", node_a.kind);
    println!();

    println!("📋 Consequent (A2):");
    println!("   ID:      [{}]", &consequent_id[..8]);
    println!("   Content: {}", node_b.content);
    println!("   Kind:    {:?}", node_b.kind);
    println!();

    // Get admissible sets
    let admissible_a = udaf_model.admissible_sets.get(&antecedent_id);
    let admissible_b = udaf_model.admissible_sets.get(&consequent_id);

    if admissible_a.is_none() || admissible_b.is_none() {
        println!("⚠️  Admissible sets not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    let admissible_a = admissible_a.unwrap();
    let admissible_b = admissible_b.unwrap();

    // Extract constraints (handle both old and new structure)
    let constraints_a = if let Some(ref proof_data) = admissible_a.proof_data {
        &proof_data.constraints
    } else if let Some(ref constraints) = admissible_a.constraints {
        constraints
    } else {
        eprintln!("❌ No constraints found in antecedent admissible set");
        std::process::exit(1);
    };

    let constraints_b = if let Some(ref proof_data) = admissible_b.proof_data {
        &proof_data.constraints
    } else if let Some(ref constraints) = admissible_b.constraints {
        constraints
    } else {
        eprintln!("❌ No constraints found in consequent admissible set");
        std::process::exit(1);
    };

    println!("🔍 Antecedent Constraints: {}", constraints_a.len());
    for (i, constraint) in constraints_a.iter().enumerate() {
        let desc = if let Some(ref meta) = constraint.meta {
            meta.get_str("description").map(|s| s.as_str())
        } else {
            constraint.description.as_deref()
        }.unwrap_or("(no description)");
        println!("   {}: {} ({:?})", i+1, desc, constraint.kind);
    }
    println!();

    println!("🔍 Consequent Constraints: {}", constraints_b.len());
    for (i, constraint) in constraints_b.iter().enumerate() {
        let desc = if let Some(ref meta) = constraint.meta {
            meta.get_str("description").map(|s| s.as_str())
        } else {
            constraint.description.as_deref()
        }.unwrap_or("(no description)");
        println!("   {}: {} ({:?})", i+1, desc, constraint.kind);
    }
    println!();

    // Prove implication
    let mut prover = Prover::new();
    let proof = prover.prove_implication(admissible_a, admissible_b);

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
            println!("✅ PROVEN: A1 ⊆ A2 (Implication holds)");
            println!("   Every implementation satisfying A1 also satisfies A2");
        }
        ProofStatus::Refuted => {
            println!("❌ REFUTED: A1 ⊄ A2 (Implication does not hold)");
            println!("   Counterexample exists: some implementation satisfies A1 but not A2");
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

/// Execute ProveConsistencyWithinDomain command in standalone mode
pub fn execute_prove_consistency_domain_standalone(
    store: &Store,
    spec_a_id: String,
    spec_b_id: String,
    domain_id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔬 Proving Consistency Within Domain\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get the specifications
    let node_a = graph.get_node(&spec_a_id);
    let node_b = graph.get_node(&spec_b_id);
    let node_domain = graph.get_node(&domain_id);

    if node_a.is_none() {
        eprintln!("❌ Specification A '{}' not found", spec_a_id);
        std::process::exit(1);
    }
    if node_b.is_none() {
        eprintln!("❌ Specification B '{}' not found", spec_b_id);
        std::process::exit(1);
    }
    if node_domain.is_none() {
        eprintln!("❌ Domain '{}' not found", domain_id);
        std::process::exit(1);
    }

    let node_a = node_a.unwrap();
    let node_b = node_b.unwrap();
    let node_domain = node_domain.unwrap();

    println!("📋 Specification A:");
    println!("   ID:      [{}]", &spec_a_id[..8]);
    println!("   Content: {}", node_a.content);
    println!("   Kind:    {:?}", node_a.kind);
    println!();

    println!("📋 Specification B:");
    println!("   ID:      [{}]", &spec_b_id[..8]);
    println!("   Content: {}", node_b.content);
    println!("   Kind:    {:?}", node_b.kind);
    println!();

    println!("🌐 Domain:");
    println!("   ID:      [{}]", &domain_id[..8]);
    println!("   Content: {}", node_domain.content);
    println!("   Kind:    {:?}", node_domain.kind);
    println!();

    // Get admissible sets and domain
    let admissible_a = udaf_model.admissible_sets.get(&spec_a_id);
    let admissible_b = udaf_model.admissible_sets.get(&spec_b_id);
    let domain = udaf_model.domains.get(&domain_id);

    if admissible_a.is_none() || admissible_b.is_none() {
        println!("⚠️  Admissible sets not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    if domain.is_none() {
        println!("⚠️  Domain not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    let admissible_a = admissible_a.unwrap();
    let admissible_b = admissible_b.unwrap();
    let domain = domain.unwrap();

    // Extract constraints
    let constraints_a = if let Some(ref proof_data) = admissible_a.proof_data {
        &proof_data.constraints
    } else if let Some(ref constraints) = admissible_a.constraints {
        constraints
    } else {
        &vec![]
    };

    let constraints_b = if let Some(ref proof_data) = admissible_b.proof_data {
        &proof_data.constraints
    } else if let Some(ref constraints) = admissible_b.constraints {
        constraints
    } else {
        &vec![]
    };

    let domain_constraints = if let Some(ref proof_data) = domain.proof_data {
        &proof_data.constraints
    } else {
        &vec![]
    };

    println!("🔍 Admissible Set A: {} constraints", constraints_a.len());
    for (i, constraint) in constraints_a.iter().enumerate() {
        let desc = if let Some(ref meta) = constraint.meta {
            meta.get_str("description").map(|s| s.as_str())
        } else {
            constraint.description.as_deref()
        }.unwrap_or("(no description)");
        println!("   {}: {} ({:?})", i+1, desc, constraint.kind);
    }
    println!();

    println!("🔍 Admissible Set B: {} constraints", constraints_b.len());
    for (i, constraint) in constraints_b.iter().enumerate() {
        let desc = if let Some(ref meta) = constraint.meta {
            meta.get_str("description").map(|s| s.as_str())
        } else {
            constraint.description.as_deref()
        }.unwrap_or("(no description)");
        println!("   {}: {} ({:?})", i+1, desc, constraint.kind);
    }
    println!();

    println!("🔍 Domain Constraints: {}", domain_constraints.len());
    if domain_constraints.is_empty() {
        println!("   ⚠️  Domain has no formal constraints");
        println!("   Will fall back to A-only consistency check");
    } else {
        for (i, constraint) in domain_constraints.iter().enumerate() {
            let desc = if let Some(ref meta) = constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("(no description)");
            println!("   {}: {} ({:?})", i+1, desc, constraint.kind);
        }
    }
    println!();

    // Prove consistency within domain
    let mut prover = Prover::new();
    let proof = prover.prove_consistency_within_domain(admissible_a, admissible_b, domain);

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
            println!("✅ PROVEN: Specifications are consistent within domain");
            println!("   ∃x. (x ∈ A₁ ∧ x ∈ A₂ ∧ x ∈ D) - Implementation exists satisfying both specs within domain");
        }
        ProofStatus::Refuted => {
            println!("❌ REFUTED: Specifications contradict each other within domain");
            println!("   A₁ ∩ A₂ ∩ D = ∅ - No implementation can satisfy both within domain");
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

/// Execute ProveCompleteness command in standalone mode
pub fn execute_prove_completeness_standalone(
    store: &Store,
    domain_id: String,
    spec_ids: Vec<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔬 Proving Domain Completeness (Coverage)\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get the domain
    let node_domain = graph.get_node(&domain_id);

    if node_domain.is_none() {
        eprintln!("❌ Domain '{}' not found", domain_id);
        std::process::exit(1);
    }

    let node_domain = node_domain.unwrap();

    println!("🌐 Domain:");
    println!("   ID:      [{}]", &domain_id[..8]);
    println!("   Content: {}", node_domain.content);
    println!("   Kind:    {:?}", node_domain.kind);
    println!();

    // Get domain from model
    let domain = udaf_model.domains.get(&domain_id);

    if domain.is_none() {
        println!("⚠️  Domain not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    let domain = domain.unwrap();

    // Extract domain constraints
    let domain_constraints = if let Some(ref proof_data) = domain.proof_data {
        &proof_data.constraints
    } else {
        &vec![]
    };

    println!("🔍 Domain Constraints: {}", domain_constraints.len());
    if domain_constraints.is_empty() {
        println!("   ❌ Domain has no formal constraints");
        println!("   Cannot prove completeness without formalized domain");
        std::process::exit(1);
    } else {
        for (i, constraint) in domain_constraints.iter().enumerate() {
            let desc = if let Some(ref meta) = constraint.meta {
                meta.get_str("description").map(|s| s.as_str())
            } else {
                constraint.description.as_deref()
            }.unwrap_or("(no description)");
            println!("   {}: {} ({:?})", i+1, desc, constraint.kind);
        }
    }
    println!();

    // Get covering specifications
    let mut covering_specs = Vec::new();

    println!("📋 Covering Specifications ({}):", spec_ids.len());
    for (i, spec_id) in spec_ids.iter().enumerate() {
        let node = graph.get_node(spec_id);
        if node.is_none() {
            eprintln!("❌ Specification '{}' not found", spec_id);
            std::process::exit(1);
        }
        let node = node.unwrap();

        let admissible = udaf_model.admissible_sets.get(spec_id);
        if admissible.is_none() {
            println!("⚠️  Admissible set for '{}' not found", spec_id);
            continue;
        }

        covering_specs.push(admissible.unwrap());

        println!("   {}. [{}] {}", i+1, &spec_id[..8], node.content);
    }
    println!();

    if covering_specs.is_empty() {
        eprintln!("❌ No valid covering specifications found");
        std::process::exit(1);
    }

    // Prove completeness
    let mut prover = Prover::new();
    let proof = prover.prove_completeness(domain, &covering_specs);

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
            println!("✅ PROVEN: Domain is fully covered (D ⊆ D_S)");
            println!("   Every element of domain is covered by some specification");
            println!("   No coverage gaps (漏れB) detected");
        }
        ProofStatus::Refuted => {
            println!("❌ REFUTED: Coverage gap exists");
            println!("   D ⊄ D_S - Some domain elements are not covered by any specification");
            println!("   漏れB (coverage gap) detected - check counterexample in proof steps");
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

/// Execute DetectUnderspecification command in standalone mode
pub fn execute_detect_underspec_standalone(
    store: &Store,
    spec_id: String,
    domain_id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔬 Detecting Underspecification (漏れA)\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get the specification and domain
    let node_spec = graph.get_node(&spec_id);
    let node_domain = graph.get_node(&domain_id);

    if node_spec.is_none() {
        eprintln!("❌ Specification '{}' not found", spec_id);
        std::process::exit(1);
    }
    if node_domain.is_none() {
        eprintln!("❌ Domain '{}' not found", domain_id);
        std::process::exit(1);
    }

    let node_spec = node_spec.unwrap();
    let node_domain = node_domain.unwrap();

    println!("📋 Specification:");
    println!("   ID:      [{}]", &spec_id[..8]);
    println!("   Content: {}", node_spec.content);
    println!("   Kind:    {:?}", node_spec.kind);
    println!();

    println!("🌐 Domain:");
    println!("   ID:      [{}]", &domain_id[..8]);
    println!("   Content: {}", node_domain.content);
    println!("   Kind:    {:?}", node_domain.kind);
    println!();

    // Get admissible set and domain
    let admissible = udaf_model.admissible_sets.get(&spec_id);
    let domain = udaf_model.domains.get(&domain_id);
    let universe = udaf_model.universes.values().next(); // Get any universe for context

    if admissible.is_none() {
        println!("⚠️  Admissible set not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    if domain.is_none() {
        println!("⚠️  Domain not found in U/D/A/f model");
        println!("   Run 'spec inspect-model' to verify model state");
        std::process::exit(1);
    }

    let admissible = admissible.unwrap();
    let domain = domain.unwrap();
    let universe = universe.unwrap_or_else(|| {
        eprintln!("❌ No universe found in U/D/A/f model");
        std::process::exit(1);
    });

    // Detect underspecification
    let prover = Prover::new();
    let report = prover.detect_underspecification(admissible, domain, universe);

    println!("═══════════════════════════════════════════════════════════════\n");
    println!("📊 Underspecification Analysis Report\n");

    println!("Specification: [{}]", &spec_id[..8]);
    println!("Domain:        [{}]", &domain_id[..8]);
    println!();

    if report.is_likely_underspecified {
        println!("⚠️  LIKELY UNDERSPECIFIED (漏れA detected)");
    } else {
        println!("✅ Appears adequately specified");
    }
    println!("   Confidence: {:.1}%", report.confidence * 100.0);
    println!();

    if !report.reasons.is_empty() {
        println!("Reasons:");
        for (i, reason) in report.reasons.iter().enumerate() {
            println!("  {}. {}", i+1, reason);
        }
        println!();
    }

    if !report.suggestions.is_empty() {
        println!("Suggestions:");
        for (i, suggestion) in report.suggestions.iter().enumerate() {
            println!("  {}. {}", i+1, suggestion);
        }
        println!();
    }

    println!("═══════════════════════════════════════════════════════════════");
    println!();
    println!("Note: Underspecification detection is heuristic-based.");
    println!("      漏れA (underspecification) is a design choice, not an error.");
    println!("      Use this report to guide specification refinement decisions.");

    Ok(())
}
