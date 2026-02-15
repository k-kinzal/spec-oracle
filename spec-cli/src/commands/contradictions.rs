/// DetectContradictions command: Formal verification of specification consistency
///
/// Uses legacy SpecGraph contradiction detection for now.
/// TODO: Migrate to UDAFModel-based formal verification.

use crate::proto;
use spec_core::Store;
use tonic::Request;

/// Execute DetectContradictions in standalone mode
pub fn execute_contradictions_standalone(
    store: &Store,
) -> Result<(), Box<dyn std::error::Error>> {
    // Use legacy SpecGraph for contradiction detection
    // TODO: Migrate to UDAFModel + ModelSync for formal verification
    let graph = store.load()?;

    println!("🔍 Detecting Contradictions (Legacy Heuristic)\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    let contradictions = graph.detect_contradictions();

    println!("Summary:");
    println!("  Contradictions found: {}", contradictions.len());
    println!();

    if contradictions.is_empty() {
        println!("✅ No contradictions detected");
        println!("   All specifications are mutually consistent");
    } else {
        println!("⚠️  {} contradiction(s) detected", contradictions.len());
        println!();

        for (i, contradiction) in contradictions.iter().enumerate() {
            println!("{}. {}", i + 1, contradiction.explanation);
            println!("   Node A: [{}] {}", &contradiction.node_a.id[..8], contradiction.node_a.content);
            println!("   Node B: [{}] {}", &contradiction.node_b.id[..8], contradiction.node_b.content);
            println!();
        }

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
