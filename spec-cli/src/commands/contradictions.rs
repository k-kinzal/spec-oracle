/// DetectContradictions command: Formal verification of specification consistency
///
/// Uses Z3 SMT solver to prove/refute consistency between specifications.

use crate::proto;
use spec_core::{FileStore, Prover, UDAFModel, ProofStatus};
use tonic::Request;

/// Execute DetectContradictions in standalone mode
pub fn execute_contradictions_standalone(
    store: &FileStore,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let mut udaf_model = UDAFModel::new();
    udaf_model.populate_from_graph(&graph);

    println!("🔍 Detecting Contradictions (Formal Verification)\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Get all nodes to check pairwise
    let nodes = graph.list_nodes(None);
    let mut contradictions_found = 0;
    let mut checked_pairs = 0;

    println!("Analyzing {} specifications...\n", nodes.len());

    let mut prover = Prover::new();

    for i in 0..nodes.len() {
        for j in i+1..nodes.len() {
            let node_a = &nodes[i];
            let node_b = &nodes[j];
            checked_pairs += 1;

            // Get admissible sets
            if let (Some(admissible_a), Some(admissible_b)) = (
                udaf_model.admissible_sets.get(&node_a.id),
                udaf_model.admissible_sets.get(&node_b.id),
            ) {
                // Skip if either has no constraints (nothing to prove)
                if admissible_a.constraints.is_empty() || admissible_b.constraints.is_empty() {
                    continue;
                }

                // Prove consistency
                let proof = prover.prove_consistency(admissible_a, admissible_b);

                // Check if refuted (contradiction detected)
                if proof.status == ProofStatus::Refuted {
                    contradictions_found += 1;

                    println!("❌ Contradiction #{}\n", contradictions_found);
                    println!("   Specification A:");
                    println!("     ID:      [{}]", &node_a.id[..8]);
                    println!("     Content: {}", node_a.content);
                    println!("     Constraints: {}", admissible_a.constraints.len());
                    for c in &admissible_a.constraints {
                        println!("       - {} ({})", c.description, c.formal.as_ref().unwrap_or(&"none".to_string()));
                    }
                    println!();

                    println!("   Specification B:");
                    println!("     ID:      [{}]", &node_b.id[..8]);
                    println!("     Content: {}", node_b.content);
                    println!("     Constraints: {}", admissible_b.constraints.len());
                    for c in &admissible_b.constraints {
                        println!("       - {} ({})", c.description, c.formal.as_ref().unwrap_or(&"none".to_string()));
                    }
                    println!();

                    println!("   Formal Proof:");
                    for (step_num, step) in proof.steps.iter().enumerate() {
                        println!("     {}. {}", step_num + 1, step.description);
                    }
                    println!();

                    println!("   Mathematical Result:");
                    println!("     A₁ ∩ A₂ = ∅ (admissible sets are disjoint)");
                    println!("     No implementation can satisfy both specifications");
                    println!("\n   ───────────────────────────────────────────────────────────\n");
                }
            }
        }
    }

    println!("═══════════════════════════════════════════════════════════════\n");
    println!("Summary:");
    println!("  Specifications checked: {}", nodes.len());
    println!("  Pairwise comparisons: {}", checked_pairs);
    println!("  Contradictions found: {}", contradictions_found);
    println!();

    if contradictions_found == 0 {
        println!("✅ No contradictions detected");
        println!("   All specifications are mutually consistent");
    } else {
        println!("⚠️  {} contradiction(s) detected", contradictions_found);
        println!("   Review and resolve contradictions before proceeding");
    }

    Ok(())
}

/// Execute DetectContradictions in server mode
pub async fn execute_contradictions_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
        .await?;
    let contradictions = resp.into_inner().contradictions;

    if contradictions.is_empty() {
        println!("No contradictions detected.");
    } else {
        println!("Found {} contradiction(s):", contradictions.len());
        for c in contradictions {
            let a = c.node_a.unwrap();
            let b = c.node_b.unwrap();
            println!("\n  Contradiction:");
            println!("    Node A [{}]: {}", a.id, a.content);
            println!("    Node B [{}]: {}", b.id, b.content);
            println!("    Reason: {}", c.explanation);
        }
    }

    Ok(())
}
