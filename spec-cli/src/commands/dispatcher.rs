//! Unified command dispatcher for standalone and server modes
//!
//! This module contains the command dispatch logic, separating it from
//! the CLI parsing layer in main.rs. This achieves the separation of
//! concerns required by the specification.

use crate::proto::spec_oracle_client::SpecOracleClient;
use crate::proto::{self, SpecEdgeKind, SpecNodeKind};
use crate::utils::*;
use crate::presentation::formatter::*;
use crate::ApiCommands;
use spec_core::{Store, NodeKind as CoreNodeKind};
use std::collections::HashMap;
use std::path::PathBuf;
use tonic::Request;

/// Dispatch commands in standalone mode (direct file access, no server)
pub async fn dispatch_standalone(
    command: crate::Commands,
    store: Store,
) -> Result<(), Box<dyn std::error::Error>> {
    use crate::commands;

    let mut store = store;

    match command {
        crate::Commands::Init { path: _ } => {
            // Init command doesn't need existing spec file
            eprintln!("Error: Init command should not reach standalone mode");
            return Ok(());
        }
        crate::Commands::Migrate { source, target } => {
            commands::execute_migrate(source, target)?;
            return Ok(());
        }
        crate::Commands::Add { content, no_infer } => {
            commands::execute_add_standalone(&mut store, content, no_infer)?;
        }
        crate::Commands::Api(api_cmd) => {
            dispatch_api_standalone(&mut store, api_cmd)?;
        }
        crate::Commands::ListNodes { kind, layer, status, full, limit, offset } => {
            dispatch_list_nodes_standalone(&store, kind, layer, status.clone(), full, limit, offset)?;
        }
        crate::Commands::DetectContradictions => {
            commands::execute_contradictions_standalone(&store)?;
        }
        crate::Commands::DetectOmissions => {
            commands::execute_omissions_standalone(&store)?;
        }
        crate::Commands::Check => {
            let exit_code = commands::execute_check_standalone(&store)?;
            std::process::exit(exit_code);
        }
        crate::Commands::Summary => {
            commands::execute_summary_standalone(&store)?;
        }
        crate::Commands::ExportDot { output, layer, metadata } => {
            commands::execute_export_dot_standalone(&store, output, layer, metadata)?;
        }
        crate::Commands::Find { query, layer, status, max } => {
            commands::execute_find_standalone(&store, &query, layer, status.clone(), max).await?;
        }
        crate::Commands::GetNode { id } => {
            eprintln!("⚠️  WARNING: 'spec get-node' is deprecated. Use 'spec api get-node' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
            commands::api::execute_get_node_standalone(&store, id)?;
        }
        crate::Commands::Trace { id, depth } => {
            commands::execute_trace_standalone(&store, &id, depth).await?;
        }
        crate::Commands::VerifyLayers => {
            commands::execute_verify_layers_standalone(&store)?;
        }
        crate::Commands::ProveConsistency { spec_a, spec_b } => {
            commands::execute_prove_consistency_standalone(&store, spec_a, spec_b)?;
        }
        crate::Commands::ProveSatisfiability { spec } => {
            commands::execute_prove_satisfiability_standalone(&store, spec)?;
        }
        crate::Commands::InspectModel { verbose } => {
            commands::execute_inspect_model_standalone(&store, verbose)?;
        }
        crate::Commands::ConstructU0 { execute, verbose } => {
            commands::execute_construct_u0_standalone(&mut store, execute, verbose)?;
        }
        crate::Commands::CleanupLowQuality { execute } => {
            commands::execute_cleanup_low_quality_standalone(&mut store, execute)?;
        }
        crate::Commands::AddEdge { source, target, kind } => {
            eprintln!("⚠️  WARNING: 'spec add-edge' is deprecated. Use 'spec api add-edge' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
            commands::api::execute_add_edge_standalone(&mut store, source, target, kind)?;
        }
        crate::Commands::Extract { source, language, min_confidence } => {
            commands::execute_extract_standalone(&mut store, source, language, min_confidence)?;
        }
        crate::Commands::InferRelationshipsAi { min_confidence, dry_run, limit, interactive } => {
            commands::execute_infer_relationships_ai_standalone(&mut store, min_confidence, dry_run, limit, interactive)?;
        }
        crate::Commands::Archive { id } => {
            commands::execute_archive(&mut store, id)?;
        }
        crate::Commands::Deprecate { id } => {
            commands::execute_deprecate(&mut store, id)?;
        }
        crate::Commands::Activate { id } => {
            commands::execute_activate(&mut store, id)?;
        }
        _ => {
            eprintln!("Command not yet supported in standalone mode.");
            eprintln!("For advanced features, use server mode (start specd first).");
            return Err("Unsupported command in standalone mode".into());
        }
    }

    Ok(())
}

/// Dispatch API commands in standalone mode
fn dispatch_api_standalone(
    store: &mut Store,
    api_cmd: ApiCommands,
) -> Result<(), Box<dyn std::error::Error>> {
    use crate::commands::api;

    match api_cmd {
        ApiCommands::AddNode { content, kind } => {
            api::execute_add_node_standalone(store, content, kind)?;
        }
        ApiCommands::GetNode { id } => {
            api::execute_get_node_standalone(store, id)?;
        }
        ApiCommands::ListNodes { kind, layer, status, full, limit, offset } => {
            api::execute_list_nodes_standalone(store, kind, layer, status.clone(), full, limit, offset)?;
        }
        ApiCommands::RemoveNode { id } => {
            api::execute_remove_node_standalone(store, id)?;
        }
        ApiCommands::AddEdge { source, target, kind } => {
            api::execute_add_edge_standalone(store, source, target, kind)?;
        }
        ApiCommands::ListEdges { node } => {
            api::execute_list_edges_standalone(store, node)?;
        }
        ApiCommands::RemoveEdge { id } => {
            api::execute_remove_edge_standalone(store, id)?;
        }
        ApiCommands::SetUniverse { id, universe } => {
            api::execute_set_universe_standalone(store, id, universe)?;
        }
        ApiCommands::FilterByLayer { min, max } => {
            api::execute_filter_by_layer_standalone(store, min, max)?;
        }
        ApiCommands::GenerateContract { id: _, language: _ } => {
            eprintln!("Contract generation not yet supported in standalone mode");
        }
        ApiCommands::CheckCompliance { id: _, code: _ } => {
            eprintln!("Compliance checking not yet supported in standalone mode");
        }
        ApiCommands::QueryAtTimestamp { timestamp: _ } => {
            eprintln!("Temporal queries not yet supported in standalone mode");
        }
        ApiCommands::DiffTimestamps { from: _, to: _ } => {
            eprintln!("Temporal diff not yet supported in standalone mode");
        }
        ApiCommands::NodeHistory { id: _ } => {
            eprintln!("Node history not yet supported in standalone mode");
        }
        ApiCommands::ComplianceTrend { id: _ } => {
            eprintln!("Compliance trend not yet supported in standalone mode");
        }
    }

    Ok(())
}

/// Dispatch list-nodes command in standalone mode (deprecated)
fn dispatch_list_nodes_standalone(
    store: &Store,
    kind: Option<String>,
    layer: Option<u8>,
    status: Option<String>,
    full: bool,
    limit: Option<usize>,
    offset: Option<usize>,
) -> Result<(), Box<dyn std::error::Error>> {
    eprintln!("⚠️  WARNING: 'spec list-nodes' is deprecated. Use 'spec api list-nodes' instead.");
    eprintln!("   The command will still work but may be removed in a future version.\n");

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
                CoreNodeKind::Assertion => "Assertions".to_string(),
                CoreNodeKind::Constraint => "Constraints".to_string(),
                CoreNodeKind::Scenario => "Scenarios".to_string(),
                CoreNodeKind::Definition => "Definitions".to_string(),
                CoreNodeKind::Domain => "Domains".to_string(),
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

        println!("💡 Use --full to see the complete list");
        println!("💡 Use --layer <N> to filter by formality layer (0-3)");
        println!("💡 Use --kind <type> to filter by kind");
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
        let kind_str = match node.kind {
            CoreNodeKind::Assertion => "assertion",
            CoreNodeKind::Constraint => "constraint",
            CoreNodeKind::Scenario => "scenario",
            CoreNodeKind::Definition => "definition",
            CoreNodeKind::Domain => "domain",
        };
        let layer_label = format_formality_layer(node.formality_layer);
        println!(
            "  [{}] [{}] {} - {}",
            layer_label,
            &node.id[..8],
            kind_str,
            node.content.chars().take(80).collect::<String>()
        );
    }

    if end < nodes.len() {
        println!();
        println!("... and {} more (use --offset {} to see next page)", nodes.len() - end, end);
    }

    Ok(())
}

/// Dispatch commands in server mode (gRPC client)
pub async fn dispatch_server(
    command: crate::Commands,
    mut client: SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    use crate::commands;

    match command {
        crate::Commands::Add { content, no_infer } => {
            commands::execute_add_server(&mut client, content, no_infer).await?;
        }
        crate::Commands::Api(api_cmd) => {
            dispatch_api_server(&mut client, api_cmd).await?;
        }
        crate::Commands::DetectContradictions => {
            commands::execute_contradictions_server(&mut client).await?;
        }
        crate::Commands::DetectOmissions => {
            commands::execute_omissions_server(&mut client).await?;
        }
        crate::Commands::Check => {
            commands::execute_check_server(&mut client).await?;
        }
        crate::Commands::Find { query, layer, status, max } => {
            commands::execute_find_server(&mut client, &query, layer, status.clone(), max).await?;
        }
        crate::Commands::Trace { id, depth } => {
            commands::execute_trace_server(&mut client, &id, depth).await?;
        }
        crate::Commands::Query { query, ai } => {
            commands::execute_query_server(&mut client, &query, ai).await?;
        }
        crate::Commands::VerifyLayers => {
            // VerifyLayers requires standalone mode for now
            println!("VerifyLayers command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
        }
        crate::Commands::Watch { source, language, min_confidence, interval } => {
            commands::execute_watch_server(&mut client, source, language, min_confidence, interval).await?;
        }
        crate::Commands::Init { path } => {
            commands::execute_init(path)?;
        }
        crate::Commands::Migrate { source, target } => {
            commands::execute_migrate(source, target)?;
        }
        crate::Commands::ConstructU0 { execute: _, verbose: _ } => {
            println!("ConstructU0 command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
        }
        crate::Commands::CleanupLowQuality { execute: _ } => {
            println!("CleanupLowQuality command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
            println!("\nReason: This command directly modifies the specification database.");
        }
        _ => {
            eprintln!("Command '{}' not yet implemented in server mode",
                std::any::type_name_of_val(&command));
            return Err("Unsupported command in server mode".into());
        }
    }

    Ok(())
}

/// Dispatch API commands in server mode
async fn dispatch_api_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    api_cmd: ApiCommands,
) -> Result<(), Box<dyn std::error::Error>> {
    // This is a placeholder - the actual implementation needs to be extracted from main.rs
    // For now, return an error
    eprintln!("API commands in server mode not yet fully extracted to dispatcher");
    eprintln!("Command: {:?}", std::any::type_name_of_val(&api_cmd));
    Err("Server mode API dispatch not yet implemented in dispatcher module".into())
}
