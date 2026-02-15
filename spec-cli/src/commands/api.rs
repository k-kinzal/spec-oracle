/// Low-level graph API commands (advanced users)
///
/// This module implements direct graph operations for advanced use cases.
/// Most users should use high-level commands instead (add, check, find, etc.)

use crate::proto;
use crate::utils::{parse_node_kind, proto_to_core_kind};
use crate::presentation::formatter::format_formality_layer;
use spec_core::{Store, EdgeKind};
use std::collections::HashMap;
use chrono;

/// Execute AddNode API command in standalone mode
pub fn execute_add_node_standalone(
    store: &mut Store,
    content: String,
    kind: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut graph = store.load()?;
    let proto_kind = parse_node_kind(&kind);
    let core_kind = proto_to_core_kind(proto_kind);
    let node = graph.add_node(content.clone(), core_kind, HashMap::new());
    let node_id = node.id.clone();
    let node_content = node.content.clone();
    let node_kind = node.kind;
    store.save(&graph)?;
    println!("Added node: {}", node_id);
    println!("  Content: {}", node_content);
    println!("  Kind: {:?}", node_kind);
    Ok(())
}

/// Execute GetNode API command in standalone mode
pub fn execute_get_node_standalone(
    store: &Store,
    id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    if let Some(node) = graph.get_node(&id) {
        let layer_label = format_formality_layer(node.formality_layer);

        println!("📋 Node: {}", node.id);
        println!();
        println!("  Content: {}", node.content);
        println!("  Kind: {:?}", node.kind);
        println!("  Layer: {}", layer_label);
        println!();

        // Timestamps
        if node.created_at > 0 {
            let created = chrono::DateTime::from_timestamp(node.created_at, 0)
                .map(|dt| dt.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                .unwrap_or_else(|| format!("timestamp: {}", node.created_at));
            println!("  Created: {}", created);
        }
        if node.modified_at > 0 && node.modified_at != node.created_at {
            let modified = chrono::DateTime::from_timestamp(node.modified_at, 0)
                .map(|dt| dt.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                .unwrap_or_else(|| format!("timestamp: {}", node.modified_at));
            println!("  Modified: {}", modified);
        }

        // Metadata
        if !node.metadata.is_empty() {
            println!();
            println!("  Metadata:");
            for (key, value) in &node.metadata {
                println!("    {}: {}", key, value);
            }
        }

        // Related nodes
        let edges = graph.list_edges(Some(&id));
        if !edges.is_empty() {
            println!();
            println!("  Relationships: {} edge(s)", edges.len());
            for (edge_data, source_id, target_id) in edges.iter().take(10) {
                let (related_id, direction) = if source_id == &id {
                    (target_id, "→")
                } else {
                    (source_id, "←")
                };

                if let Some(related_node) = graph.get_node(related_id) {
                    let related_layer = format_formality_layer(related_node.formality_layer);
                    let preview = related_node.content.chars().take(60).collect::<String>();
                    println!("    {} {:?} [{}] [{}] {}",
                        direction,
                        edge_data.kind,
                        related_layer,
                        &related_id[..8],
                        if related_node.content.len() > 60 {
                            format!("{}...", preview)
                        } else {
                            preview
                        }
                    );
                }
            }
            if edges.len() > 10 {
                println!("    ... and {} more", edges.len() - 10);
            }
        }
    } else {
        eprintln!("❌ Node not found: {}", id);
    }
    Ok(())
}

/// Execute ListNodes API command in standalone mode
pub fn execute_list_nodes_standalone(
    store: &Store,
    kind: Option<String>,
    layer: Option<u8>,
    status: Option<String>,
    full: bool,
    limit: Option<usize>,
    offset: Option<usize>,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let kind_filter = kind.as_ref().map(|k| proto_to_core_kind(parse_node_kind(k)));
    let mut nodes = graph.list_nodes(kind_filter);

    // Apply layer filter if specified
    if let Some(layer_filter) = layer {
        nodes.retain(|n| n.formality_layer == layer_filter);
    }

    // Apply status filter if specified
    if let Some(ref status_filter) = status {
        nodes.retain(|n| {
            let node_status = n.metadata.get("status")
                .map(|s| s.as_str())
                .unwrap_or("active");
            node_status == status_filter.as_str()
        });
    }

    // Summary mode (default)
    if !full {
        println!("📊 Specification Summary");
        println!("Total: {} specifications", nodes.len());
        println!();

        // Group by formality layer
        let mut by_layer = std::collections::HashMap::<u8, usize>::new();
        for node in &nodes {
            *by_layer.entry(node.formality_layer).or_insert(0) += 1;
        }

        println!("By Formality Layer:");
        for layer_num in 0..=3 {
            if let Some(&count) = by_layer.get(&layer_num) {
                let layer_label = format_formality_layer(layer_num);
                let layer_name = match layer_num {
                    0 => "Natural Language Requirements",
                    1 => "Formal Specifications",
                    2 => "Interface Definitions",
                    3 => "Implementation",
                    _ => "Unknown",
                };
                println!("  {}: {} ({} specs)", layer_label, layer_name, count);
            }
        }
        println!();

        // Group by kind
        let mut by_kind = std::collections::HashMap::<String, usize>::new();
        for node in &nodes {
            let kind_str = match node.kind {
                spec_core::graph::NodeKind::Assertion => "Assertions".to_string(),
                spec_core::graph::NodeKind::Constraint => "Constraints".to_string(),
                spec_core::graph::NodeKind::Scenario => "Scenarios".to_string(),
                spec_core::graph::NodeKind::Definition => "Definitions".to_string(),
                spec_core::graph::NodeKind::Domain => "Domains".to_string(),
            };
            *by_kind.entry(kind_str).or_insert(0) += 1;
        }

        println!("By Kind:");
        let mut kind_vec: Vec<_> = by_kind.iter().collect();
        kind_vec.sort_by_key(|(k, _)| k.as_str());
        for (kind, count) in kind_vec {
            println!("  {}: {}", kind, count);
        }
        println!();

        // Group by status
        let mut by_status = std::collections::HashMap::<String, usize>::new();
        for node in &nodes {
            let node_status = node.metadata.get("status")
                .map(|s| s.to_string())
                .unwrap_or_else(|| "active".to_string());
            *by_status.entry(node_status).or_insert(0) += 1;
        }

        if !by_status.is_empty() {
            println!("By Status:");
            let mut status_vec: Vec<_> = by_status.iter().collect();
            status_vec.sort_by_key(|(k, _)| k.as_str());
            for (status, count) in status_vec {
                println!("  {}: {}", status, count);
            }
            println!();
        }

        println!("💡 Use --full to see the complete list");
        println!("💡 Use --layer <N> to filter by formality layer (0-3)");
        println!("💡 Use --kind <type> to filter by kind");
        println!("💡 Use --status <status> to filter by status (active/deprecated/archived)");
        return Ok(());
    }

    // Full mode with optional pagination
    let offset_val = offset.unwrap_or(0);
    let limit_val = limit.unwrap_or(nodes.len());
    let end = std::cmp::min(offset_val + limit_val, nodes.len());
    let page_nodes: Vec<_> = nodes.iter().skip(offset_val).take(limit_val).collect();

    println!("Found {} node(s):", nodes.len());
    if offset_val > 0 || limit.is_some() {
        println!("Showing {} - {} of {}:", offset_val + 1, end, nodes.len());
    }
    println!();

    for node in page_nodes {
        let layer_label = format_formality_layer(node.formality_layer);
        println!("  [{}] [{}] {:?} - {}",
            layer_label,
            &node.id[..8],
            node.kind,
            node.content.chars().take(80).collect::<String>());
    }

    if end < nodes.len() {
        println!();
        println!("... and {} more (use --offset {} to see next page)", nodes.len() - end, end);
    }

    // Show active filters
    let mut filters = Vec::new();
    if layer.is_some() {
        filters.push(format!("layer: U{}", layer.unwrap()));
    }
    if kind.is_some() {
        filters.push(format!("kind: {}", kind.as_ref().unwrap()));
    }
    if let Some(ref status_filter) = status {
        filters.push(format!("status: {}", status_filter));
    }
    if !filters.is_empty() {
        println!();
        println!("(Filtered by: {})", filters.join(", "));
    }

    Ok(())
}

/// Execute RemoveNode API command in standalone mode
pub fn execute_remove_node_standalone(
    store: &mut Store,
    id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut graph = store.load()?;
    graph.remove_node(&id);
    store.save(&graph)?;
    println!("Removed node: {}", id);
    Ok(())
}

/// Execute AddEdge API command in standalone mode
pub fn execute_add_edge_standalone(
    store: &mut Store,
    source: String,
    target: String,
    kind: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut graph = store.load()?;
    let edge_kind = match kind.to_lowercase().as_str() {
        "refines" => EdgeKind::Refines,
        "depends_on" => EdgeKind::DependsOn,
        "contradicts" => EdgeKind::Contradicts,
        "derives_from" => EdgeKind::DerivesFrom,
        "synonym" => EdgeKind::Synonym,
        "composes" => EdgeKind::Composes,
        "formalizes" => EdgeKind::Formalizes,
        _ => EdgeKind::Refines,
    };
    let edge = graph.add_edge(&source, &target, edge_kind, HashMap::new())?;
    let edge_id = edge.id.clone();
    store.save(&graph)?;
    println!("Added edge: {}", edge_id);
    Ok(())
}

/// Execute ListEdges API command in standalone mode
pub fn execute_list_edges_standalone(
    store: &Store,
    node: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let edges = if let Some(ref node_id) = node {
        graph.list_edges(Some(node_id))
    } else {
        graph.list_edges(None)
    };
    println!("Found {} edge(s):", edges.len());

    for (edge_data, source_id, target_id) in &edges {
        // Get source node
        if let Some(source_node) = graph.get_node(source_id) {
            let source_layer = format_formality_layer(source_node.formality_layer);
            let source_preview = source_node.content.chars().take(50).collect::<String>();
            let source_display = if source_node.content.len() > 50 {
                format!("{}...", source_preview)
            } else {
                source_preview
            };

            println!("\n  [{}] [{}] {:?} - {}",
                source_layer,
                &source_id[..8],
                source_node.kind,
                source_display);
        } else {
            println!("\n  [{}] (node not found)", &source_id[..8]);
        }

        println!("    --[{:?}]-->", edge_data.kind);

        // Get target node
        if let Some(target_node) = graph.get_node(target_id) {
            let target_layer = format_formality_layer(target_node.formality_layer);
            let target_preview = target_node.content.chars().take(50).collect::<String>();
            let target_display = if target_node.content.len() > 50 {
                format!("{}...", target_preview)
            } else {
                target_preview
            };

            println!("  [{}] [{}] {:?} - {}",
                target_layer,
                &target_id[..8],
                target_node.kind,
                target_display);
        } else {
            println!("  [{}] (node not found)", &target_id[..8]);
        }
    }

    if !edges.is_empty() {
        println!(); // Add blank line after edges
    }

    Ok(())
}

/// Execute RemoveEdge API command in standalone mode
pub fn execute_remove_edge_standalone(
    store: &mut Store,
    id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut graph = store.load()?;
    graph.remove_edge(&id);
    store.save(&graph)?;
    println!("Removed edge: {}", id);
    Ok(())
}

/// Execute SetUniverse API command in standalone mode
pub fn execute_set_universe_standalone(
    _store: &mut Store,
    _id: String,
    _universe: String,
) -> Result<(), Box<dyn std::error::Error>> {
    eprintln!("SetUniverse not yet supported in standalone mode");
    Ok(())
}

/// Execute FilterByLayer API command in standalone mode
pub fn execute_filter_by_layer_standalone(
    store: &Store,
    min: u32,
    max: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let all_nodes = graph.list_nodes(None);
    let filtered: Vec<_> = all_nodes.into_iter()
        .filter(|n| {
            let layer = n.formality_layer as u32;
            layer >= min && layer <= max
        })
        .collect();

    println!("Found {} node(s) in layers {}-{}:", filtered.len(), min, max);
    for node in filtered {
        let layer_label = format_formality_layer(node.formality_layer);
        println!("  [{}] [{}] {:?} - {}",
            layer_label,
            &node.id[..8],
            node.kind,
            node.content.chars().take(80).collect::<String>());
    }
    Ok(())
}
