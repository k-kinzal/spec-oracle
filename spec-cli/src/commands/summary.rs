/// Summary command: Display specification statistics using UDA/f operations (gRPC only)

use crate::proto;
use crate::presentation::formatter::format_formality_layer;
use std::collections::HashMap;
use tonic::Request;

/// Execute the Summary command via gRPC using UDA/f operations
pub async fn execute_summary_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Get all universes
    let universes_resp = client
        .list_universes(Request::new(proto::ListUniversesRequest {}))
        .await?;
    let universes = universes_resp.into_inner().universes;

    // Get all admissible sets
    let sets_resp = client
        .list_admissible_sets(Request::new(proto::ListAdmissibleSetsRequest {
            universe_id: String::new(), // Get all
        }))
        .await?;
    let admissible_sets = sets_resp.into_inner().admissible_sets;

    // Get all transforms
    let transforms_resp = client
        .list_transforms(Request::new(proto::ListTransformsRequest {
            universe_id: String::new(), // Get all
        }))
        .await?;
    let transforms = transforms_resp.into_inner().transforms;

    // Count by universe (layer)
    let mut by_universe = HashMap::<String, usize>::new();
    for set in &admissible_sets {
        *by_universe.entry(set.universe_id.clone()).or_insert(0) += 1;
    }

    // Run checks
    let contra_resp = client
        .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
        .await?;
    let contradictions = contra_resp.into_inner().contradictions;

    let omit_resp = client
        .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
        .await?;
    let omissions = omit_resp.into_inner().omissions;

    // Display summary
    println!("Specification Summary\n");
    println!("Total Specifications: {}", admissible_sets.len());
    println!();

    // Show universes
    println!("Universes ({}):", universes.len());
    let mut sorted_universes = universes.clone();
    sorted_universes.sort_by_key(|u| u.layer);
    for universe in &sorted_universes {
        let count = by_universe.get(&universe.id).unwrap_or(&0);
        let layer_label = format_formality_layer(universe.layer as u8);
        println!("  {} ({}) - {}: {} spec(s)",
            universe.id,
            layer_label,
            universe.name,
            count);
    }
    println!();

    // Show specification counts by universe
    if !by_universe.is_empty() {
        println!("Specifications by Universe:");
        let mut universe_vec: Vec<_> = by_universe.iter().collect();
        universe_vec.sort_by_key(|(k, _)| k.as_str());
        for (universe_id, count) in &universe_vec {
            // Find universe name
            let universe_name = sorted_universes
                .iter()
                .find(|u| u.id == **universe_id)
                .map(|u| u.name.as_str())
                .unwrap_or("Unknown");
            println!("  {} ({}): {}", universe_id, universe_name, count);
        }
        println!();
    }

    println!("Transforms: {} mappings", transforms.len());
    if transforms.len() > 0 {
        println!("  Forward: {}", transforms.iter().filter(|t| t.kind == proto::UdafTransformKind::Forward.into()).count());
        println!("  Inverse: {}", transforms.iter().filter(|t| t.kind == proto::UdafTransformKind::Inverse.into()).count());
        println!("  Parallel: {}", transforms.iter().filter(|t| t.kind == proto::UdafTransformKind::Parallel.into()).count());
    }
    println!();

    println!("Health:");
    if contradictions.is_empty() {
        println!("  ✓ No contradictions");
    } else {
        println!("  ✗ {} contradiction(s)", contradictions.len());
    }
    if omissions.is_empty() {
        println!("  ✓ No isolated specs");
    } else {
        println!("  ⚠ {} isolated spec(s)", omissions.len());
    }

    if contradictions.is_empty() && omissions.is_empty() {
        println!("\n✓ Specifications are healthy!");
    } else if !contradictions.is_empty() {
        println!("\n✗ Critical issues found. Run 'spec check' for details.");
    } else {
        println!("\n⚠ Minor issues. Run 'spec check' for details.");
    }

    Ok(())
}
