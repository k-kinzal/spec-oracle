/// Query command: Search specifications using natural language (gRPC only)

use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use crate::presentation::formatter::format_formality_layer;
use crate::utils::node_kind_name;
use tonic::Request;

/// Execute Query command via gRPC
pub async fn execute_query_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    query: &str,
    ai: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let search_query = if ai {
        println!("Enhancing query with AI...");
        crate::handle_ai_query(query, "claude").await?
    } else {
        query.to_string()
    };

    let resp = client
        .query(Request::new(proto::QueryRequest {
            natural_language_query: search_query,
        }))
        .await?;

    let result = resp.into_inner();
    println!("{}", result.explanation);

    if !result.matching_nodes.is_empty() {
        println!("\nMatching nodes:");
        for node in result.matching_nodes {
            let layer_label = format_formality_layer(node.formality_layer as u8);
            println!("  [{}] [{}] {} - {}",
                layer_label,
                &node.id[..8.min(node.id.len())],
                node_kind_name(node.kind),
                node.content);
        }
    }

    Ok(())
}
