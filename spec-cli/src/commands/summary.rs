/// Summary command: Display specification statistics
///
/// This command provides an overview of the specification graph,
/// including counts by kind, layer, health metrics, and relationships.

use spec_core::{Store, NodeKind as CoreNodeKind};
use std::collections::HashMap;

/// Execute the Summary command in standalone mode
pub fn execute_summary_standalone(
    store: &Store,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;

    // Collect statistics
    let nodes = graph.list_nodes(None);
    let total = nodes.len();

    // Count by kind
    let mut by_kind = HashMap::new();
    for node in &nodes {
        *by_kind.entry(node.kind).or_insert(0) += 1;
    }

    // Count by layer
    let mut by_layer = HashMap::new();
    for node in &nodes {
        let layer = node.formality_layer;
        *by_layer.entry(layer).or_insert(0) += 1;
    }

    // Count edges
    let all_edges = graph.list_edges(None);
    let total_edges = all_edges.len();

    // Health metrics
    let contradictions = graph.detect_contradictions();
    let isolated = graph.detect_omissions();

    // Display summary
    println!("📊 Specification Summary\n");
    println!("Total Specifications: {}", total);
    println!();

    println!("By Kind:");
    for (kind, count) in &by_kind {
        let kind_str = match kind {
            CoreNodeKind::Assertion => "  Assertions",
            CoreNodeKind::Constraint => "  Constraints",
            CoreNodeKind::Scenario => "  Scenarios",
            CoreNodeKind::Definition => "  Definitions",
            CoreNodeKind::Domain => "  Domains",
        };
        println!("{}: {}", kind_str, count);
    }
    println!();

    println!("By Formality Layer:");
    let mut sorted_layers: Vec<_> = by_layer.iter().collect();
    sorted_layers.sort_by_key(|(k, _)| *k);
    for (layer, count) in sorted_layers {
        println!("  U{}: {}", layer, count);
    }
    println!();

    println!("Relationships: {} edges", total_edges);
    println!();

    println!("Health:");
    if contradictions.is_empty() {
        println!("  ✓ No contradictions");
    } else {
        println!("  ⚠️  {} contradiction(s)", contradictions.len());
    }
    if isolated.is_empty() {
        println!("  ✓ No isolated specs");
    } else {
        println!("  ⚠️  {} isolated spec(s)", isolated.len());
    }

    if contradictions.is_empty() && isolated.is_empty() {
        println!("\n✅ Specifications are healthy!");
    } else if !contradictions.is_empty() {
        println!("\n❌ Critical issues found. Run 'spec check' for details.");
    } else {
        println!("\n⚠️  Minor issues. Run 'spec check' for details.");
    }

    Ok(())
}
