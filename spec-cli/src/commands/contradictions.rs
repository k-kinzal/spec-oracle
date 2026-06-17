/// DetectContradictions command (gRPC only)

use crate::proto;
use tonic::Request;

/// Execute DetectContradictions via gRPC
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
