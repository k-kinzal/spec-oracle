/// DetectOmissions command (gRPC only)

use crate::proto;
use tonic::Request;

/// Execute DetectOmissions via gRPC
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
