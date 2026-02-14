use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use crate::{format_formality_layer};
use tonic::Request;
use spec_core::{Store, NodeKind as CoreNodeKind};

/// Execute Find command in standalone mode
pub async fn execute_find_standalone(
    store: &Store,
    query: &str,
    layer: Option<u32>,
    max: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    use spec_core::SpecGraph;

    let graph = store.load()?;

    // Search for matching specifications
    let mut results = graph.search(query);

    // Filter by layer if specified
    if let Some(layer_num) = layer {
        results.retain(|node| {
            if let Some(layer_str) = node.metadata.get("formality_layer") {
                layer_str.parse::<u32>().ok() == Some(layer_num)
            } else {
                node.formality_layer as u32 == layer_num
            }
        });
    }

    // Limit results
    let max_results = max as usize;
    if results.len() > max_results {
        results.truncate(max_results);
    }

    if results.is_empty() {
        println!("No specifications found matching '{}'", query);
        println!("\nTry:");
        println!("  - Using different keywords");
        println!("  - Broadening your search");
        println!("  - Using 'spec list-nodes' to see all specifications");
    } else {
        println!("Found {} specification(s) matching '{}':", results.len(), query);
        println!();

        for (i, node) in results.iter().enumerate() {
            let kind_str = match node.kind {
                CoreNodeKind::Assertion => "assertion",
                CoreNodeKind::Constraint => "constraint",
                CoreNodeKind::Scenario => "scenario",
                CoreNodeKind::Definition => "definition",
                CoreNodeKind::Domain => "domain",
            };
            let layer_str = if let Some(l) = node.metadata.get("formality_layer") {
                format!(" [U{}]", l)
            } else {
                format!(" [U{}]", node.formality_layer)
            };
            println!("  {}. [{}]{} {} - {}",
                i + 1,
                &node.id[..8],
                layer_str,
                kind_str,
                node.content
            );
        }

        if let Some(layer_num) = layer {
            println!("\n(Filtered to layer U{})", layer_num);
        }
    }

    Ok(())
}

/// Execute Find command in server mode
pub async fn execute_find_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    query: &str,
    layer: Option<u32>,
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
                &node.id[..8],
                crate::node_kind_name(node.kind),
                node.content
            );
        }

        if let Some(layer_num) = layer {
            println!("\n(Filtered to layer U{})", layer_num);
        }
    }

    Ok(())
}
