/// Find command: Search specifications by query (gRPC only)

use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use crate::presentation::formatter::format_formality_layer;
use crate::utils::node_kind_name;
use tonic::Request;

/// Execute Find command via gRPC
pub async fn execute_find_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    query: &str,
    layer: Option<u32>,
    status: Option<String>,
    max: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    // Use Query RPC since there's no dedicated Find RPC
    let search_resp = client
        .query(Request::new(proto::QueryRequest {
            natural_language_query: query.to_string(),
        }))
        .await?;
    let mut results = search_resp.into_inner().matching_nodes;

    // Filter by layer if specified
    if let Some(layer_num) = layer {
        results.retain(|node| {
            if let Some(layer_str) = node.metadata.get("formality_layer") {
                layer_str.parse::<u32>().ok() == Some(layer_num)
            } else {
                node.formality_layer == layer_num
            }
        });
    }

    // Filter by status if specified
    if let Some(ref status_filter) = status {
        results.retain(|node| {
            let node_status = node.metadata.get("status")
                .map(|s| s.as_str())
                .unwrap_or("active");
            node_status == status_filter.as_str()
        });
    }

    // Limit results
    let max_results = max as usize;
    if results.len() > max_results {
        results.truncate(max_results);
    }

    if results.is_empty() {
        println!("No specifications found matching '{}'", query);
    } else {
        println!("Found {} specification(s) matching '{}':", results.len(), query);
        println!();

        for (i, node) in results.iter().enumerate() {
            let layer_label = format_formality_layer(node.formality_layer as u8);
            println!("  {}. [{}] [{}] {} - {}",
                i + 1,
                layer_label,
                &node.id[..8.min(node.id.len())],
                node_kind_name(node.kind),
                node.content
            );
        }

        // Show active filters
        let mut filters = Vec::new();
        if let Some(layer_num) = layer {
            filters.push(format!("layer U{}", layer_num));
        }
        if let Some(ref status_filter) = status {
            filters.push(format!("status: {}", status_filter));
        }
        if !filters.is_empty() {
            println!("\n(Filtered by: {})", filters.join(", "));
        }
    }

    Ok(())
}
