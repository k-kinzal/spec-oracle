use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use crate::{format_node_kind, format_edge_kind};
use tonic::Request;
use spec_core::FileStore;
use std::collections::HashMap;

/// Execute Trace command in standalone mode
pub async fn execute_trace_standalone(
    store: &FileStore,
    id: &str,
    depth: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    use spec_core::SpecGraph;

    let graph = store.load()?;

    // Resolve short ID to full UUID if needed
    let full_id = if id.len() == 8 {
        let nodes = graph.list_nodes(None);
        let matches: Vec<_> = nodes.iter()
            .filter(|n| n.id.starts_with(id))
            .collect();

        if matches.is_empty() {
            println!("❌ Node not found with ID starting with: {}", id);
            return Ok(());
        } else if matches.len() > 1 {
            println!("❌ Ambiguous short ID: {}", id);
            return Ok(());
        }
        matches[0].id.clone()
    } else {
        id.to_string()
    };

    // Get the root node
    let root_node = graph.get_node(&full_id);
    if root_node.is_none() {
        println!("❌ Node not found: {}", full_id);
        return Ok(());
    }

    let root = root_node.unwrap();
    println!("📋 Tracing relationships for:");
    println!("   [{}] {}: {}", &root.id[..8], format_node_kind(root.kind), root.content);

    let layer_str = if let Some(l) = root.metadata.get("formality_layer") {
        format!(" [U{}]", l)
    } else if root.formality_layer > 0 {
        format!(" [U{}]", root.formality_layer)
    } else {
        String::new()
    };
    if !layer_str.is_empty() {
        println!("   Layer: {}", layer_str);
    }
    println!();

    // Trace relationships
    let max_depth = if depth == 0 { 999 } else { depth };
    let relationships = graph.trace_relationships(&full_id, max_depth);

    if relationships.is_empty() {
        println!("⚠️  No relationships found for this specification.");
        println!("\nThis specification is isolated. You may want to:");
        println!("  - Add relationships using 'spec add-edge'");
        println!("  - Run 'spec infer-relationships' to auto-detect relationships");
    } else {
        println!("🔗 Found {} relationship(s):", relationships.len());
        println!();

        // Group by depth
        let mut by_depth: HashMap<usize, Vec<_>> = HashMap::new();
        for (node, edge_kind, direction, depth_level) in &relationships {
            by_depth.entry(*depth_level).or_insert_with(Vec::new).push((node, edge_kind, direction));
        }

        let mut depths: Vec<_> = by_depth.keys().collect();
        depths.sort();

        for depth_level in depths {
            let items = by_depth.get(depth_level).unwrap();
            println!("  Level {}:", depth_level);

            for (node, edge_kind, direction) in items {
                let indent = "    ";
                let arrow = if *direction == "outgoing" { "→" } else { "←" };
                let edge_label = format_edge_kind(**edge_kind);

                let node_layer = if let Some(l) = node.metadata.get("formality_layer") {
                    format!(" [U{}]", l)
                } else if node.formality_layer > 0 {
                    format!(" [U{}]", node.formality_layer)
                } else {
                    String::new()
                };

                println!(
                    "{}{} {} [{}]{} {}: {}",
                    indent,
                    arrow,
                    edge_label,
                    &node.id[..8],
                    node_layer,
                    format_node_kind(node.kind),
                    node.content
                );
            }
            println!();
        }

        if depth > 0 && !relationships.is_empty() {
            println!("(Limited to depth {})", depth);
        }
    }

    Ok(())
}

/// Execute Trace command in server mode
pub async fn execute_trace_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    id: &str,
    _depth: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    // Get the root node
    let node_resp = client
        .get_node(Request::new(proto::GetNodeRequest { id: id.to_string() }))
        .await?;
    let root = node_resp.into_inner().node;

    if root.is_none() {
        println!("❌ Node not found: {}", id);
        return Ok(());
    }

    let root_node = root.unwrap();
    println!("📋 Tracing relationships for:");
    println!("   [{}] {}: {}", root_node.id, crate::node_kind_name(root_node.kind), root_node.content);

    let layer_str = if let Some(l) = root_node.metadata.get("formality_layer") {
        format!(" [U{}]", l)
    } else if root_node.formality_layer > 0 {
        format!(" [U{}]", root_node.formality_layer)
    } else {
        String::new()
    };
    if !layer_str.is_empty() {
        println!("   Layer: {}", layer_str);
    }
    println!();

    // For server mode, we need to manually traverse relationships using list_edges
    let edges_resp = client
        .list_edges(Request::new(proto::ListEdgesRequest {
            node_id: id.to_string(),
        }))
        .await?;
    let edges = edges_resp.into_inner().edges;

    if edges.is_empty() {
        println!("⚠️  No relationships found for this specification.");
        println!("\nThis specification is isolated. You may want to:");
        println!("  - Add relationships using 'spec add-edge'");
        println!("  - Run 'spec infer-relationships' to auto-detect relationships");
    } else {
        println!("🔗 Found {} direct relationship(s):", edges.len());
        println!();

        for edge in &edges {
            let arrow = if edge.source_id == id { "→" } else { "←" };
            let other_id = if edge.source_id == id { &edge.target_id } else { &edge.source_id };
            let edge_label = crate::edge_kind_name(edge.kind);

            // Get the other node
            let other_resp = client
                .get_node(Request::new(proto::GetNodeRequest { id: other_id.clone() }))
                .await?;

            if let Some(other_node) = other_resp.into_inner().node {
                let node_layer = if let Some(l) = other_node.metadata.get("formality_layer") {
                    format!(" [U{}]", l)
                } else if other_node.formality_layer > 0 {
                    format!(" [U{}]", other_node.formality_layer)
                } else {
                    String::new()
                };

                println!(
                    "  {} {} [{}]{} {}: {}",
                    arrow,
                    edge_label,
                    other_node.id,
                    node_layer,
                    crate::node_kind_name(other_node.kind),
                    other_node.content
                );
            }
        }

        println!("\nNote: Server mode currently shows only direct relationships.");
        println!("For full traversal, use standalone mode.");
    }

    Ok(())
}
