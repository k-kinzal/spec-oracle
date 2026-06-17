/// Trace command: Trace specification relationships using UDA/f operations (gRPC only)

use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use tonic::Request;

/// Execute Trace command via gRPC using UDA/f operations
pub async fn execute_trace_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    id: &str,
    _depth: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    // Get the admissible set
    let set_resp = client
        .get_admissible_set(Request::new(proto::GetAdmissibleSetRequest {
            spec_id: id.to_string(),
        }))
        .await?;
    let admissible_set = set_resp.into_inner().admissible_set;

    if admissible_set.is_none() {
        println!("Specification not found: {}", id);
        return Ok(());
    }

    let spec = admissible_set.unwrap();
    println!("Tracing relationships for:");
    println!("   Spec ID: {}", spec.spec_id);
    println!("   Universe: {}", spec.universe_id);
    println!("   Constraints: {}", spec.constraints.len());
    for constraint in &spec.constraints {
        println!("     - {}", constraint.description);
    }
    println!();

    // List all transforms
    let transforms_resp = client
        .list_transforms(Request::new(proto::ListTransformsRequest {
            universe_id: String::new(), // Get all
        }))
        .await?;
    let transforms = transforms_resp.into_inner().transforms;

    // Filter transforms related to this spec's universe
    let related_transforms: Vec<_> = transforms
        .iter()
        .filter(|t| {
            t.source_universe == spec.universe_id || t.target_universe == spec.universe_id
        })
        .collect();

    if related_transforms.is_empty() {
        println!("No transforms found for universe {}.", spec.universe_id);
        println!("\nYou may want to:");
        println!("  - Create transforms using 'spec rpc create-transform'");
        println!("  - Run 'spec infer-relationships' to auto-detect relationships");
    } else {
        println!("Found {} transform(s) for universe {}:", related_transforms.len(), spec.universe_id);
        println!();

        for transform in &related_transforms {
            let arrow = if transform.source_universe == spec.universe_id {
                format!("{} → {}", transform.source_universe, transform.target_universe)
            } else {
                format!("{} → {}", transform.source_universe, transform.target_universe)
            };

            let kind = match transform.kind {
                1 => "FORWARD",
                2 => "INVERSE",
                3 => "PARALLEL",
                _ => "UNKNOWN",
            };

            println!("  [{}] {}", kind, arrow);
            if !transform.description.is_empty() {
                println!("     {}", transform.description);
            }
        }
    }

    // Check for contradictions
    if !spec.contradicts.is_empty() {
        println!("\n⚠️  This specification contradicts {} other spec(s):", spec.contradicts.len());
        for contradicting_id in &spec.contradicts {
            println!("  - {}", contradicting_id);
        }
    }

    Ok(())
}
