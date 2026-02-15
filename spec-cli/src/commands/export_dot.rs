/// Export command: Generate DOT format for Graphviz visualization
///
/// This command exports the specification graph in DOT format,
/// which can be visualized using Graphviz tools (dot, neato, etc.).

use spec_core::{Store, NodeKind as CoreNodeKind, EdgeKind as CoreEdgeKind};

/// Execute the export-dot command in standalone mode
pub fn execute_export_dot_standalone(
    store: &Store,
    output_file: Option<String>,
    layer: Option<u32>,
    include_metadata: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let graph = store.load()?;

    // Build DOT format output
    let mut dot = String::new();
    dot.push_str("digraph SpecificationGraph {\n");
    dot.push_str("  rankdir=TB;\n");
    dot.push_str("  node [shape=box, style=rounded];\n");
    dot.push_str("  edge [fontsize=10];\n\n");

    // Add subgraphs for each layer
    for l in 0u8..=3u8 {
        // Skip if layer filter is set and doesn't match
        if let Some(filter_layer) = layer {
            if filter_layer as u8 != l {
                continue;
            }
        }

        dot.push_str(&format!("  subgraph cluster_U{} {{\n", l));
        dot.push_str(&format!("    label=\"U{}: {}\";\n", l, layer_name(l)));
        dot.push_str("    color=lightgray;\n");
        dot.push_str("    style=filled;\n");
        dot.push_str("    fillcolor=\"#f0f0f0\";\n\n");

        // Add nodes for this layer
        let nodes: Vec<_> = graph.list_nodes(None)
            .into_iter()
            .filter(|n| n.formality_layer == l)
            .collect();

        for node in &nodes {
            let id = node.id.to_string();
            let short_id = &id[0..8];

            // Escape content for DOT format
            let content = node.content.replace("\"", "\\\"").replace("\n", "\\n");
            let truncated_content = if content.len() > 50 {
                format!("{}...", &content[0..47])
            } else {
                content.clone()
            };

            // Color by kind
            let color = match node.kind {
                CoreNodeKind::Constraint => "#ffe0e0",
                CoreNodeKind::Assertion => "#e0f0ff",
                CoreNodeKind::Scenario => "#e0ffe0",
                CoreNodeKind::Definition => "#fff0e0",
                CoreNodeKind::Domain => "#f0e0ff",
            };

            let kind_str = match node.kind {
                CoreNodeKind::Constraint => "C",
                CoreNodeKind::Assertion => "A",
                CoreNodeKind::Scenario => "S",
                CoreNodeKind::Definition => "D",
                CoreNodeKind::Domain => "Dom",
            };

            let mut label = format!("[{}] {}\\n{}", kind_str, short_id, truncated_content);

            // Optionally include metadata
            if include_metadata {
                if let Some(source) = node.metadata.get("source_file") {
                    label.push_str(&format!("\\n📁 {}", source));
                }
                if let Some(inferred) = node.metadata.get("inferred") {
                    if inferred == "true" {
                        label.push_str("\\n🤖 auto-extracted");
                    }
                }
            }

            dot.push_str(&format!(
                "    \"{}\" [label=\"{}\", fillcolor=\"{}\", style=filled];\n",
                short_id, label, color
            ));
        }

        dot.push_str("  }\n\n");
    }

    // Add edges
    dot.push_str("  // Edges\n");
    let edges = graph.list_edges(None);
    for (edge_data, source_id, target_id) in &edges {
        // Get source and target nodes to check layers
        let source_node = graph.get_node(source_id)
            .ok_or("Source node not found")?;
        let target_node = graph.get_node(target_id)
            .ok_or("Target node not found")?;

        // Skip if layer filter is set and neither source nor target matches
        if let Some(filter_layer) = layer {
            let filter_layer_u8 = filter_layer as u8;
            if source_node.formality_layer != filter_layer_u8 && target_node.formality_layer != filter_layer_u8 {
                continue;
            }
        }

        let source_short = &source_id[0..8];
        let target_short = &target_id[0..8];

        let (edge_label, edge_style, edge_color) = match edge_data.kind {
            CoreEdgeKind::Refines => ("refines", "solid", "blue"),
            CoreEdgeKind::DependsOn => ("depends", "dashed", "gray"),
            CoreEdgeKind::Contradicts => ("contradicts", "bold", "red"),
            CoreEdgeKind::DerivesFrom => ("derives", "dotted", "purple"),
            CoreEdgeKind::Synonym => ("synonym", "dashed", "green"),
            CoreEdgeKind::Formalizes => ("formalizes", "bold", "darkblue"),
            CoreEdgeKind::Composes => ("composes", "solid", "orange"),
            CoreEdgeKind::Transform => ("transform", "bold", "darkorange"),
        };

        dot.push_str(&format!(
            "  \"{}\" -> \"{}\" [label=\"{}\", style=\"{}\", color=\"{}\"];\n",
            source_short, target_short, edge_label, edge_style, edge_color
        ));
    }

    dot.push_str("}\n");

    // Output to file or stdout
    if let Some(output_path) = output_file {
        std::fs::write(&output_path, dot)?;
        println!("✅ DOT file written to: {}", output_path);
        println!("\nVisualize with:");
        println!("  dot -Tpng {} -o spec-graph.png", output_path);
        println!("  dot -Tsvg {} -o spec-graph.svg", output_path);
    } else {
        println!("{}", dot);
    }

    Ok(())
}

/// Get human-readable name for formality layer
fn layer_name(layer: u8) -> &'static str {
    match layer {
        0 => "Natural Language Requirements",
        1 => "Formal Specifications",
        2 => "Interface Definitions",
        3 => "Implementation",
        _ => "Unknown Layer",
    }
}
