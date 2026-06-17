/// Layer verification and consistency checking commands (gRPC only)

use crate::proto;
use tonic::Request;

/// Execute DetectLayerInconsistencies command via gRPC
pub async fn execute_detect_layer_inconsistencies_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
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
