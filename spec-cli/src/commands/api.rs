/// Low-level graph API commands (advanced users)
///
/// This module implements direct graph operations for advanced use cases.
/// Most users should use high-level commands instead (add, check, find, etc.)

use crate::proto;
use crate::utils::{parse_node_kind, proto_to_core_kind};
use crate::presentation::formatter::format_formality_layer;
use spec_core::{FileStore, EdgeKind};
use std::collections::HashMap;

/// Execute AddNode API command in standalone mode
pub fn execute_add_node_standalone(
    store: &mut FileStore,
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
    store: &FileStore,
    id: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    if let Some(node) = graph.get_node(&id) {
        println!("Node: {}", node.id);
        println!("  Content: {}", node.content);
        println!("  Kind: {:?}", node.kind);
    } else {
        eprintln!("Node not found: {}", id);
    }
    Ok(())
}

/// Execute ListNodes API command in standalone mode
pub fn execute_list_nodes_standalone(
    store: &FileStore,
    kind: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let kind_filter = kind.as_ref().map(|k| proto_to_core_kind(parse_node_kind(k)));
    let nodes = graph.list_nodes(kind_filter);
    println!("Found {} node(s):", nodes.len());
    for node in nodes {
        let layer_label = format_formality_layer(node.formality_layer);
        println!("  [{}] [{}] {:?} - {}",
            layer_label,
            &node.id[..8],
            node.kind,
            node.content.chars().take(80).collect::<String>());
    }
    Ok(())
}

/// Execute RemoveNode API command in standalone mode
pub fn execute_remove_node_standalone(
    store: &mut FileStore,
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
    store: &mut FileStore,
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
    store: &FileStore,
    node: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;
    let edges = if let Some(ref node_id) = node {
        graph.list_edges(Some(node_id))
    } else {
        graph.list_edges(None)
    };
    println!("Found {} edge(s):", edges.len());
    for (edge_data, source_id, target_id) in edges {
        println!("  {} --[{:?}]--> {}",
            &source_id[..8],
            edge_data.kind,
            &target_id[..8]);
    }
    Ok(())
}

/// Execute RemoveEdge API command in standalone mode
pub fn execute_remove_edge_standalone(
    store: &mut FileStore,
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
    _store: &mut FileStore,
    _id: String,
    _universe: String,
) -> Result<(), Box<dyn std::error::Error>> {
    eprintln!("SetUniverse not yet supported in standalone mode");
    Ok(())
}

/// Execute FilterByLayer API command in standalone mode
pub fn execute_filter_by_layer_standalone(
    store: &FileStore,
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
