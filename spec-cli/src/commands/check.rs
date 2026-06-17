/// Check command: Detect contradictions and omissions (gRPC only)

use crate::proto;
use tonic::Request;

/// Execute the Check command via gRPC
pub async fn execute_check_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<i32, Box<dyn std::error::Error>> {
    println!("Checking specifications...\n");

    // Check contradictions
    println!("  Checking for contradictions...");
    let contra_resp = client
        .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
        .await?;
    let contradictions = contra_resp.into_inner().contradictions;
    if contradictions.is_empty() {
        println!("  No contradictions found");
    } else {
        println!("  {} contradiction(s) found", contradictions.len());
    }

    // Check omissions
    println!("  Checking for omissions...");
    let omit_resp = client
        .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
        .await?;
    let omissions = omit_resp.into_inner().omissions;
    if omissions.is_empty() {
        println!("  No isolated specifications");
    } else {
        println!("  {} isolated specification(s)", omissions.len());
    }

    // Summary
    println!("\nSummary:");
    println!("  Contradictions: {}", contradictions.len());
    println!("  Isolated specs: {}", omissions.len());

    let total_issues = contradictions.len() + omissions.len();
    let exit_code = if total_issues == 0 {
        println!("\nAll checks passed! No issues found.");
        0
    } else if contradictions.is_empty() {
        println!("\nMinor issues found (isolated specifications may need relationships)");

        if !omissions.is_empty() {
            println!("\nExamples of isolated specifications:");
            for (i, o) in omissions.iter().take(3).enumerate() {
                println!("  {}. {}", i + 1, o.description);
                for n in &o.related_nodes {
                    println!("     - [{}] {}", n.id, n.content);
                }
            }
            if omissions.len() > 3 {
                println!("  ... and {} more", omissions.len() - 3);
            }
        }
        1
    } else {
        println!("\nCritical issues found!");

        // Show contradictions
        println!("\nContradictions:");
        for (i, c) in contradictions.iter().enumerate() {
            println!("  {}. {}", i + 1, c.explanation);
            if let (Some(node_a), Some(node_b)) = (&c.node_a, &c.node_b) {
                println!("     A: [{}] {}", node_a.id, node_a.content);
                println!("     B: [{}] {}", node_b.id, node_b.content);
            }
        }

        1
    };

    Ok(exit_code)
}
