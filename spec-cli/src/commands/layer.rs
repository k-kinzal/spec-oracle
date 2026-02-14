/// Layer verification and consistency checking commands
///
/// This module provides operations for verifying multi-layer specification consistency,
/// including completeness (U0→U3) and soundness (U3→U0) checks.

use spec_core::Store;
use crate::utils::parse_formality_layer;

/// Execute VerifyLayers command in standalone mode
///
/// Verifies multi-layer specification consistency:
/// - Checks completeness: every U0 requirement has U3 implementation
/// - Checks soundness: every U3 implementation traces to U0 requirement
pub fn execute_verify_layers_standalone(store: &Store) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;

    println!("🔍 Verifying multi-layer specification consistency...\n");

    // Find all nodes by formality layer
    let mut u0_nodes = Vec::new();
    let mut u1_nodes = Vec::new();
    let mut u2_nodes = Vec::new();
    let mut u3_nodes = Vec::new();

    for node in graph.list_nodes(None) {
        let layer = parse_formality_layer(node.formality_layer as u8);

        match layer {
            0 => u0_nodes.push(node),
            1 => u1_nodes.push(node),
            2 => u2_nodes.push(node),
            3 => u3_nodes.push(node),
            _ => {}
        }
    }

    println!("📊 Layer Distribution:");
    println!("   U0 (Requirements):     {} specs", u0_nodes.len());
    println!("   U1 (Formal):           {} specs", u1_nodes.len());
    println!("   U2 (Interface):        {} specs", u2_nodes.len());
    println!("   U3 (Implementation):   {} specs", u3_nodes.len());
    println!();

    // Check U0 → U3 completeness (every requirement has implementation)
    println!("🔬 Checking Completeness (U0 → U3):");
    let mut incomplete_count = 0;
    let mut complete_chains = Vec::new();

    for u0_node in &u0_nodes {
        // Find U3 nodes reachable from this U0 via Formalizes edges
        let mut u3_implementations = Vec::new();
        let relationships = graph.trace_relationships(&u0_node.id, 999);

        for (related_node, edge_kind, direction, _depth) in &relationships {
            // Check if this is a Formalizes edge pointing forward
            use spec_core::EdgeKind;
            if *edge_kind == EdgeKind::Formalizes && direction == "outgoing" {
                let related_layer = parse_formality_layer(related_node.formality_layer);

                if related_layer == 3 {
                    u3_implementations.push(related_node.id.clone());
                }
            }
        }

        if u3_implementations.is_empty() {
            incomplete_count += 1;
            println!("   ⚠️  [{}] {} (no U3 implementation)", &u0_node.id[..8], u0_node.content);
        } else {
            complete_chains.push((u0_node.id.clone(), u3_implementations));
        }
    }

    if incomplete_count == 0 {
        println!("   ✅ All {} U0 requirements have U3 implementations", u0_nodes.len());
    } else {
        println!("   ⚠️  {} of {} U0 requirements lack U3 implementations", incomplete_count, u0_nodes.len());
    }
    println!();

    // Check U3 → U0 soundness (every implementation has requirement)
    println!("🔬 Checking Soundness (U3 → U0):");
    let mut unsound_count = 0;

    for u3_node in &u3_nodes {
        // Find U0 nodes reachable from this U3 via Formalizes edges (backwards)
        let mut u0_requirements = Vec::new();
        let relationships = graph.trace_relationships(&u3_node.id, 999);

        for (related_node, edge_kind, direction, _depth) in &relationships {
            // Check if this is a Formalizes edge pointing backward
            use spec_core::EdgeKind;
            if *edge_kind == EdgeKind::Formalizes && direction == "incoming" {
                let related_layer = parse_formality_layer(related_node.formality_layer);

                if related_layer == 0 {
                    u0_requirements.push(related_node.id.clone());
                }
            }
        }

        if u0_requirements.is_empty() {
            unsound_count += 1;
            println!("   ⚠️  [{}] {} (no U0 requirement)", &u3_node.id[..8], u3_node.content);
        }
    }

    if unsound_count == 0 {
        println!("   ✅ All {} U3 implementations trace to U0 requirements", u3_nodes.len());
    } else {
        println!("   ⚠️  {} of {} U3 implementations lack U0 requirements", unsound_count, u3_nodes.len());
    }
    println!();

    // Summary
    println!("📊 Verification Summary:");

    let completeness_ratio = if u0_nodes.is_empty() {
        100.0
    } else {
        (u0_nodes.len() - incomplete_count) as f64 / u0_nodes.len() as f64 * 100.0
    };

    let soundness_ratio = if u3_nodes.is_empty() {
        100.0
    } else {
        (u3_nodes.len() - unsound_count) as f64 / u3_nodes.len() as f64 * 100.0
    };

    println!("   Completeness (U0→U3): {:.1}%", completeness_ratio);
    println!("   Soundness (U3→U0):    {:.1}%", soundness_ratio);
    println!("   Complete chains:      {}", complete_chains.len());
    println!();

    if incomplete_count == 0 && unsound_count == 0 {
        println!("✅ Multi-layer verification PASSED");
        println!("   All requirements have implementations.");
        println!("   All implementations trace to requirements.");
    } else {
        println!("⚠️  Multi-layer verification found issues:");
        if incomplete_count > 0 {
            println!("   {} incomplete requirements (U0 without U3)", incomplete_count);
        }
        if unsound_count > 0 {
            println!("   {} unsound implementations (U3 without U0)", unsound_count);
        }
    }

    Ok(())
}

/// Execute DetectLayerInconsistencies command in server mode
///
/// Detects inconsistencies in layer relationships (e.g., U3→U0 instead of U0→U3)
pub async fn execute_detect_layer_inconsistencies_server(
    client: &mut crate::proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    use tonic::Request;
    use crate::proto;

    let resp = client
        .detect_layer_inconsistencies(Request::new(proto::DetectLayerInconsistenciesRequest {}))
        .await?;
    let inconsistencies = resp.into_inner().inconsistencies;

    if inconsistencies.is_empty() {
        println!("No layer inconsistencies detected.");
    } else {
        println!("Found {} layer inconsistenc(ies):", inconsistencies.len());
        for i in inconsistencies {
            let src = i.source.unwrap();
            let tgt = i.target.unwrap();
            println!("\n  Layer Inconsistency:");
            println!("    Source [{}] (layer {}): {}", src.id, src.formality_layer, src.content);
            println!("    Target [{}] (layer {}): {}", tgt.id, tgt.formality_layer, tgt.content);
            println!("    Reason: {}", i.explanation);
        }
    }

    Ok(())
}
