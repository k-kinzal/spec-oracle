use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use crate::{handle_ai_query, node_kind_name, format_formality_layer};
use tonic::Request;
use spec_core::Store;

/// Execute Query command in standalone mode
pub async fn execute_query_standalone(
    store: &Store,
    query: &str,
    ai: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use spec_core::SpecGraph;

    let search_query = if ai {
        println!("Enhancing query with AI...");
        handle_ai_query(query, "claude").await?
    } else {
        query.to_string()
    };

    let graph = store.load()?;

    // Search for matching specifications
    let results = graph.search(&search_query);

    if results.is_empty() {
        println!("No specifications found matching '{}'", search_query);
        println!("\nTry:");
        println!("  - Using different keywords");
        println!("  - Broadening your search");
        println!("  - Using 'spec list-nodes' to see all specifications");
    } else {
        println!("Found {} specification(s) matching '{}':", results.len(), search_query);
        println!();

        for node in &results {
            let layer_label = format_formality_layer(node.formality_layer);
            let kind_str = match node.kind {
                spec_core::NodeKind::Assertion => "assertion",
                spec_core::NodeKind::Constraint => "constraint",
                spec_core::NodeKind::Scenario => "scenario",
                spec_core::NodeKind::Definition => "definition",
                spec_core::NodeKind::Domain => "domain",
            };

            println!("  [{}] [{}] {} - {}",
                layer_label,
                &node.id[..8],
                kind_str,
                node.content
            );
        }
    }

    Ok(())
}

/// Execute Query command in server mode
pub async fn execute_query_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    query: &str,
    ai: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let search_query = if ai {
        println!("Enhancing query with AI...");
        handle_ai_query(query, "claude").await?
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
                node.id,
                node_kind_name(node.kind),
                node.content);
        }
    }

    Ok(())
}
