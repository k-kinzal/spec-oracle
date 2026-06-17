/// Export command: Generate DOT format for Graphviz visualization using UDA/f operations (gRPC only)

use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use tonic::Request;

/// Execute the export-dot command via gRPC using UDA/f operations
pub async fn execute_export_dot_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    output_file: Option<String>,
    layer: Option<u32>,
    _include_metadata: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    // Fetch all universes
    let universes_resp = client
        .list_universes(Request::new(proto::ListUniversesRequest {}))
        .await?;
    let universes = universes_resp.into_inner().universes;

    // Fetch all admissible sets
    let sets_resp = client
        .list_admissible_sets(Request::new(proto::ListAdmissibleSetsRequest {
            universe_id: String::new(),
        }))
        .await?;
    let admissible_sets = sets_resp.into_inner().admissible_sets;

    // Fetch all transforms
    let transforms_resp = client
        .list_transforms(Request::new(proto::ListTransformsRequest {
            universe_id: String::new(),
        }))
        .await?;
    let transforms = transforms_resp.into_inner().transforms;

    // Build DOT format output
    let mut dot = String::new();
    dot.push_str("digraph SpecificationGraph {\n");
    dot.push_str("  rankdir=TB;\n");
    dot.push_str("  node [shape=box, style=rounded];\n");
    dot.push_str("  edge [fontsize=10];\n\n");

    // Add subgraphs for each universe
    for universe in &universes {
        // Skip if layer filter is set and doesn't match
        if let Some(filter_layer) = layer {
            if filter_layer != universe.layer {
                continue;
            }
        }

        dot.push_str(&format!("  subgraph cluster_{} {{\n", universe.id));
        dot.push_str(&format!("    label=\"{}: {}\";\n", universe.id, universe.name));
        dot.push_str("    color=lightgray;\n");
        dot.push_str("    style=filled;\n");

        // Color by layer
        let fill_color = match universe.layer {
            0 => "#e0f0ff",  // U0: Light blue
            1 => "#e0ffe0",  // U1: Light green
            2 => "#fff0e0",  // U2: Light orange
            3 => "#ffe0e0",  // U3: Light red
            _ => "#f0f0f0",
        };
        dot.push_str(&format!("    fillcolor=\"{}\";\n\n", fill_color));

        // Add admissible sets for this universe
        let universe_sets: Vec<_> = admissible_sets.iter()
            .filter(|s| s.universe_id == universe.id)
            .collect();

        for set in &universe_sets {
            let short_id = &set.spec_id[..8.min(set.spec_id.len())];

            // Get first constraint as label
            let constraint_text = if set.constraints.is_empty() {
                "No constraints".to_string()
            } else {
                let desc = &set.constraints[0].description;
                if desc.len() > 50 {
                    format!("{}...", &desc[..47])
                } else {
                    desc.clone()
                }
            };

            let constraint_text_escaped = constraint_text.replace("\"", "\\\"").replace("\n", "\\n");
            let label = format!("[{}]\\n{}", short_id, constraint_text_escaped);

            dot.push_str(&format!(
                "    \"{}\" [label=\"{}\", style=filled, fillcolor=\"white\"];\n",
                set.spec_id, label
            ));
        }

        dot.push_str("  }\n\n");
    }

    // Add transforms as edges between universes
    dot.push_str("  // Transforms\n");
    for transform in &transforms {
        // Skip if layer filter is set
        if let Some(filter_layer) = layer {
            let source_universe = universes.iter().find(|u| u.id == transform.source_universe);
            let target_universe = universes.iter().find(|u| u.id == transform.target_universe);

            let source_matches = source_universe.map(|u| u.layer == filter_layer).unwrap_or(false);
            let target_matches = target_universe.map(|u| u.layer == filter_layer).unwrap_or(false);

            if !source_matches || !target_matches {
                continue;
            }
        }

        let kind_label = match transform.kind {
            1 => "FORWARD",
            2 => "INVERSE",
            3 => "PARALLEL",
            _ => "UNKNOWN",
        };

        let (style, color) = match transform.kind {
            1 => ("solid", "blue"),      // Forward: solid blue
            2 => ("dashed", "red"),      // Inverse: dashed red
            3 => ("dotted", "green"),    // Parallel: dotted green
            _ => ("solid", "black"),
        };

        // Draw edge between universe clusters
        dot.push_str(&format!(
            "  \"{}\" -> \"{}\" [label=\"{}\", style=\"{}\", color=\"{}\", lhead=cluster_{}, ltail=cluster_{}];\n",
            transform.source_universe, transform.target_universe,
            kind_label, style, color,
            transform.target_universe, transform.source_universe
        ));
    }

    // Add inter-spec relationships (contradictions)
    dot.push_str("\n  // Contradictions\n");
    for set in &admissible_sets {
        if !set.contradicts.is_empty() {
            for contradicting_id in &set.contradicts {
                dot.push_str(&format!(
                    "  \"{}\" -> \"{}\" [label=\"contradicts\", style=\"bold\", color=\"red\"];\n",
                    set.spec_id, contradicting_id
                ));
            }
        }
    }

    dot.push_str("}\n");

    // Output to file or stdout
    if let Some(output_path) = output_file {
        std::fs::write(&output_path, &dot)?;
        println!("DOT file written to: {}", output_path);
        println!("\nVisualize with:");
        println!("  dot -Tpng {} -o spec-graph.png", output_path);
        println!("  dot -Tsvg {} -o spec-graph.svg", output_path);
        println!("\nGraph statistics:");
        println!("  Universes: {}", universes.len());
        println!("  Specifications: {}", admissible_sets.len());
        println!("  Transforms: {}", transforms.len());
    } else {
        println!("{}", dot);
    }

    Ok(())
}
