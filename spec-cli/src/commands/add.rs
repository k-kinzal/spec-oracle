/// High-level specification addition command
///
/// Automatically infers the specification kind and relationships,
/// providing a user-friendly interface for adding specifications.

use crate::proto;
use crate::utils::*;
use spec_core::{Store, NodeKind as CoreNodeKind};
use std::collections::HashMap;
use tonic::Request;

/// Execute the Add command in standalone mode
pub fn execute_add_standalone(
    store: &mut Store,
    content: String,
    no_infer: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("Adding specification: {}\n", content);

    // Load graph
    let mut graph = store.load()?;

    // Infer kind
    let kind = infer_spec_kind(&content);
    println!("  Inferred kind: {}", kind);

    // Add node
    let proto_kind = parse_node_kind(&kind);
    let core_kind = proto_to_core_kind(proto_kind);
    let node = graph.add_node(content.clone(), core_kind, HashMap::new());
    let node_id = node.id.clone();

    println!("  ✓ Created specification [{}]", &node_id[..8]);

    // Auto-infer relationships (unless disabled)
    if !no_infer {
        println!("\n  🔗 Auto-inferring relationships...");
        let report = graph.auto_connect_node(&node_id);

        if report.edges_created > 0 {
            println!("  ✓ Created {} automatic relationship(s)", report.edges_created);
        }

        if !report.suggestions.is_empty() {
            println!("  💡 {} medium-confidence suggestion(s) (use 'spec trace {}' to view)",
                report.suggestions.len(), &node_id[..8]);
        }

        if report.edges_created == 0 && report.suggestions.is_empty() {
            println!("  ℹ️  No automatic relationships found");
            println!("     (This specification may be a new domain or highly unique)");
        }
    }

    // Save graph
    store.save(&graph)?;

    println!("\n✓ Specification added successfully");
    println!("  ID: {}", node_id);
    println!("  Use 'spec trace {}' to view relationships", &node_id[..8]);

    Ok(())
}

/// Execute the Add command in server mode
pub async fn execute_add_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
    content: String,
    no_infer: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("Adding specification: {}\n", content);

    // Infer kind from content
    let kind = infer_spec_kind(&content);
    println!("  Inferred kind: {}", kind);

    // Create the node
    let resp = client
        .add_node(Request::new(proto::AddNodeRequest {
            content: content.clone(),
            kind: parse_node_kind(&kind).into(),
            metadata: HashMap::new(),
        }))
        .await?;
    let node = resp.into_inner().node.unwrap();
    let node_id = node.id.clone();

    println!("  ✓ Created specification [{}]", &node_id[..8]);

    if !no_infer {
        // Find related specifications
        println!("\n  Searching for related specifications...");
        let query_resp = client
            .query(Request::new(proto::QueryRequest {
                natural_language_query: content.clone(),
            }))
            .await?;
        let matches = query_resp.into_inner().matching_nodes;

        if !matches.is_empty() {
            println!("  Found {} related specification(s)", matches.len());
            println!("  Creating relationships...");

            let mut created = 0;
            for related_node in matches.iter().take(5) {
                if related_node.id != node_id {
                    match client
                        .add_edge(Request::new(proto::AddEdgeRequest {
                            source_id: node_id.clone(),
                            target_id: related_node.id.clone(),
                            kind: proto::SpecEdgeKind::Refines.into(),
                            metadata: HashMap::new(),
                        }))
                        .await
                    {
                        Ok(_) => created += 1,
                        Err(_) => {}, // Edge already exists or other error
                    }
                }
            }

            if created > 0 {
                println!("  ✓ Created {} automatic relationship(s)", created);
            }
        } else {
            println!("  ℹ️  No related specifications found");
        }
    }

    println!("\n✓ Specification added successfully");
    println!("  ID: {}", node_id);

    Ok(())
}

/// Unified entry point for the Add command
pub fn execute_add(
    content: String,
    no_infer: bool,
    standalone_mode: bool,
    store: Option<&mut Store>,
    client: Option<&mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>>,
    runtime: Option<&tokio::runtime::Runtime>,
) -> Result<(), Box<dyn std::error::Error>> {
    if standalone_mode {
        if let Some(store) = store {
            execute_add_standalone(store, content, no_infer)
        } else {
            Err("Standalone mode requires a FileStore".into())
        }
    } else {
        if let (Some(client), Some(rt)) = (client, runtime) {
            rt.block_on(execute_add_server(client, content, no_infer))
        } else {
            Err("Server mode requires a client and runtime".into())
        }
    }
}
