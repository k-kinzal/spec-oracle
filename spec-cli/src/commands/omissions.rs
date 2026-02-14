/// DetectOmissions command: Identify isolated specifications
///
/// Finds specifications that are not connected to other specs through relationships.

use crate::proto;
use spec_core::Store;
use tonic::Request;

/// Execute DetectOmissions in standalone mode
pub fn execute_omissions_standalone(
    store: &Store,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let omissions = graph.detect_omissions();

    if omissions.is_empty() {
        println!("✓ No omissions detected");
    } else {
        println!("Found {} omission(s):", omissions.len());
        for (i, omission) in omissions.iter().enumerate() {
            println!("\n{}. {}", i + 1, omission.description);
            for node in &omission.related_nodes {
                println!("   - [{}] {}", &node.id[..8], node.content);
            }
        }
    }

    Ok(())
}

/// Execute DetectOmissions in server mode
pub async fn execute_omissions_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
        .await?;
    let omissions = resp.into_inner().omissions;

    if omissions.is_empty() {
        println!("No omissions detected.");
    } else {
        println!("Found {} omission(s):", omissions.len());
        for o in omissions {
            println!("\n  {}", o.description);
            for n in o.related_nodes {
                println!("    - [{}] {}", n.id, n.content);
            }
        }
    }

    Ok(())
}
