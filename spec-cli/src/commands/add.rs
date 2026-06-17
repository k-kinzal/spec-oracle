/// High-level specification addition command (gRPC only)
///
/// This command now uses UDA/f operations (CreateAdmissibleSet) instead of Node/Edge operations.

use crate::proto;
use std::collections::HashMap;
use tonic::Request;

/// Execute the Add command via gRPC using UDA/f operations
pub async fn execute_add_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
    content: String,
    no_infer: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("Adding specification: {}\n", content);

    // Create constraint from content
    let constraint = proto::UdafConstraint {
        formal: content.clone(),
        kind: proto::UdafConstraintKind::Universal.into(), // Default to UNIVERSAL
        description: content.clone(),
        metadata: HashMap::new(),
    };

    // Create AdmissibleSet in U0 (root universe)
    let resp = client
        .create_admissible_set(Request::new(proto::CreateAdmissibleSetRequest {
            universe_id: "U0".to_string(), // Add to root universe by default
            constraints: vec![constraint],
            metadata: HashMap::new(),
        }))
        .await?;

    let admissible_set = resp.into_inner().admissible_set.unwrap();
    let spec_id = admissible_set.spec_id.clone();

    println!("  Created specification [{}] in U0", &spec_id[..8.min(spec_id.len())]);

    if !no_infer {
        // Automatically infer relationships across all specifications
        println!("\n  Inferring relationships...");
        match client
            .infer_all_relationships(Request::new(proto::InferAllRelationshipsRequest {}))
            .await
        {
            Ok(resp) => {
                let result = resp.into_inner();
                if result.edges_created > 0 {
                    println!("  Created {} automatic relationship(s)", result.edges_created);
                } else {
                    println!("  No new relationships inferred");
                }
            }
            Err(e) => {
                eprintln!("  Warning: Failed to infer relationships: {}", e);
            }
        }
    }

    println!("\nSpecification added successfully");
    println!("  Spec ID: {}", spec_id);
    println!("  Universe: U0");

    Ok(())
}
