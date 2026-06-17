//! Unified command dispatcher (gRPC only)
//!
//! All commands are dispatched via gRPC to specd.
//! There is no standalone mode -- specd must be running.

use crate::proto::spec_oracle_client::SpecOracleClient;
use crate::proto;
use crate::utils::*;
use crate::presentation::formatter::*;
use crate::RpcCommands;
use std::collections::HashMap;
use tonic::Request;

type Client = SpecOracleClient<tonic::transport::Channel>;

/// Dispatch all commands via gRPC
pub async fn dispatch(
    command: crate::Commands,
    mut client: Client,
) -> Result<(), Box<dyn std::error::Error>> {
    match command {
        crate::Commands::Project(project_cmd) => {
            crate::commands::project::dispatch_project(&mut client, project_cmd).await?;
        }

        crate::Commands::Add { content, no_infer } => {
            crate::commands::add::execute_add_server(&mut client, content, no_infer).await?;
        }
        crate::Commands::Rpc(rpc_cmd) => {
            dispatch_rpc(&mut client, rpc_cmd).await?;
        }
        crate::Commands::DetectContradictions => {
            crate::commands::contradictions::execute_contradictions_server(&mut client).await?;
        }
        crate::Commands::DetectOmissions => {
            crate::commands::omissions::execute_omissions_server(&mut client).await?;
        }
        crate::Commands::Check => {
            let exit_code = crate::commands::check::execute_check_server(&mut client).await?;
            if exit_code != 0 {
                std::process::exit(exit_code);
            }
        }
        crate::Commands::Summary => {
            crate::commands::summary::execute_summary_server(&mut client).await?;
        }
        crate::Commands::Find { query, layer, status, max } => {
            crate::commands::find::execute_find_server(&mut client, &query, layer, status, max).await?;
        }
        crate::Commands::Query { query, ai } => {
            crate::commands::query::execute_query_server(&mut client, &query, ai).await?;
        }
        crate::Commands::Trace { id, depth } => {
            crate::commands::trace::execute_trace_server(&mut client, &id, depth).await?;
        }
        crate::Commands::Watch { source, language, min_confidence, interval } => {
            crate::commands::watch::execute_watch_server(&mut client, source, language, min_confidence, interval).await?;
        }
        crate::Commands::DetectLayerInconsistencies => {
            crate::commands::layer::execute_detect_layer_inconsistencies_server(&mut client).await?;
        }
        crate::Commands::DetectInterUniverseInconsistencies => {
            let resp = client
                .detect_inter_universe_inconsistencies(Request::new(proto::DetectInterUniverseInconsistenciesRequest {}))
                .await?;
            let inconsistencies = resp.into_inner().inconsistencies;
            if inconsistencies.is_empty() {
                println!("No inter-universe inconsistencies detected.");
            } else {
                println!("Found {} inter-universe inconsistency(ies):", inconsistencies.len());
                for i in inconsistencies {
                    println!("\n  Universe {} <-> Universe {}", i.universe_a, i.universe_b);
                    if let (Some(a), Some(b)) = (i.spec_a, i.spec_b) {
                        println!("    A: [{}] {}", a.id, a.content);
                        println!("    B: [{}] {}", b.id, b.content);
                    }
                    println!("    Reason: {}", i.explanation);
                }
            }
        }
        crate::Commands::InferRelationships => {
            let resp = client
                .infer_all_relationships(Request::new(proto::InferAllRelationshipsRequest {}))
                .await?;
            let result = resp.into_inner();
            println!("Relationship inference complete:");
            println!("  Edges created: {}", result.edges_created);
            println!("  Suggestions: {}", result.suggestions_count);
            if !result.suggestions.is_empty() {
                println!("\nSuggestions:");
                for (i, s) in result.suggestions.iter().take(10).enumerate() {
                    println!("  {}. {}", i + 1, s);
                }
                if result.suggestions.len() > 10 {
                    println!("  ... and {} more", result.suggestions.len() - 10);
                }
            }
        }
        crate::Commands::ResolveTerm { term } => {
            let resp = client
                .resolve_terminology(Request::new(proto::ResolveTerminologyRequest { term: term.clone() }))
                .await?;
            let result = resp.into_inner();
            if result.definitions.is_empty() && result.synonyms.is_empty() {
                println!("No definitions or synonyms found for '{}'", term);
            } else {
                if !result.definitions.is_empty() {
                    println!("Definitions for '{}':", term);
                    for node in &result.definitions {
                        println!("  [{}] {}", &node.id[..8.min(node.id.len())], node.content);
                    }
                }
                if !result.synonyms.is_empty() {
                    println!("\nSynonyms: {}", result.synonyms.join(", "));
                }
            }
        }
        crate::Commands::Ask { question, ai_cmd } => {
            let answer = crate::handle_ai_query(&question, &ai_cmd).await?;
            println!("{}", answer);
        }
        crate::Commands::FindFormalizations { id } => {
            let resp = client
                .find_formalizations(Request::new(proto::FindFormalizationsRequest { node_id: id.clone() }))
                .await?;
            let result = resp.into_inner();
            if result.formalizations.is_empty() && result.natural_sources.is_empty() {
                println!("No formalizations found for node {}", id);
            } else {
                if !result.formalizations.is_empty() {
                    println!("Formalizations of [{}]:", &id[..8.min(id.len())]);
                    for node in &result.formalizations {
                        let layer = format_formality_layer(node.formality_layer as u8);
                        println!("  [{}] [{}] {}", layer, &node.id[..8.min(node.id.len())], node.content);
                    }
                }
                if !result.natural_sources.is_empty() {
                    println!("\nNatural language sources:");
                    for node in &result.natural_sources {
                        let layer = format_formality_layer(node.formality_layer as u8);
                        println!("  [{}] [{}] {}", layer, &node.id[..8.min(node.id.len())], node.content);
                    }
                }
            }
        }
        crate::Commands::FindRelatedTerms { term, max } => {
            let resp = client
                .find_related_terms(Request::new(proto::FindRelatedTermsRequest {
                    term: term.clone(),
                    max_results: max,
                }))
                .await?;
            let result = resp.into_inner();
            if result.nodes.is_empty() {
                println!("No related terms found for '{}'", term);
            } else {
                println!("Related terms for '{}':", term);
                for scored in &result.nodes {
                    if let Some(ref node) = scored.node {
                        println!("  [{:.2}] [{}] {}", scored.score, &node.id[..8.min(node.id.len())], node.content);
                    }
                }
            }
        }
        crate::Commands::DetectPotentialSynonyms { min_similarity } => {
            let resp = client
                .detect_potential_synonyms(Request::new(proto::DetectPotentialSynonymsRequest {
                    min_similarity,
                }))
                .await?;
            let result = resp.into_inner();
            if result.candidates.is_empty() {
                println!("No potential synonyms detected (threshold: {:.2})", min_similarity);
            } else {
                println!("Found {} potential synonym pair(s):", result.candidates.len());
                for c in &result.candidates {
                    if let (Some(a), Some(b)) = (&c.node_a, &c.node_b) {
                        println!("  [{:.2}] '{}' <-> '{}'", c.similarity,
                            a.content.chars().take(40).collect::<String>(),
                            b.content.chars().take(40).collect::<String>());
                    }
                }
            }
        }
        crate::Commands::TestCoverage => {
            let resp = client
                .get_test_coverage(Request::new(proto::GetTestCoverageRequest {}))
                .await?;
            let result = resp.into_inner();
            println!("Test Coverage Report:");
            println!("  Total testable specs: {}", result.total_testable);
            println!("  With tests:           {}", result.with_tests);
            println!("  Coverage:             {:.1}%", result.coverage_ratio * 100.0);
            if !result.nodes_without_tests.is_empty() {
                println!("\nSpecs without tests:");
                for node in result.nodes_without_tests.iter().take(10) {
                    println!("  [{}] {}", &node.id[..8.min(node.id.len())], node.content);
                }
                if result.nodes_without_tests.len() > 10 {
                    println!("  ... and {} more", result.nodes_without_tests.len() - 10);
                }
            }
        }
        crate::Commands::ComplianceReport => {
            let resp = client
                .get_compliance_report(Request::new(proto::GetComplianceReportRequest {}))
                .await?;
            let result = resp.into_inner();
            if result.entries.is_empty() {
                println!("No compliance data available.");
            } else {
                println!("Compliance Report ({} entries):", result.entries.len());
                for entry in &result.entries {
                    if let Some(ref node) = entry.node {
                        println!("  [{:.1}%] [{}] {}",
                            entry.score * 100.0,
                            &node.id[..8.min(node.id.len())],
                            node.content.chars().take(60).collect::<String>());
                    }
                }
            }
        }
        crate::Commands::ExportDot { output, layer, metadata } => {
            // Export DOT format via listing nodes and edges from server
            crate::commands::export_dot::execute_export_dot_server(&mut client, output, layer, metadata).await?;
        }
    }

    Ok(())
}

/// Dispatch API commands via gRPC
async fn dispatch_rpc(
    client: &mut Client,
    rpc_cmd: RpcCommands,
) -> Result<(), Box<dyn std::error::Error>> {
    match rpc_cmd {
        // === specd RPC Operations (managing UDA/f model) ===
        RpcCommands::CreateUniverse { layer, name, description } => {
            crate::commands::specd_rpc::execute_universe_create(client, layer, name, description).await?;
        }
        RpcCommands::GetUniverse { id } => {
            crate::commands::specd_rpc::execute_universe_get(client, id).await?;
        }
        RpcCommands::ListUniverses => {
            crate::commands::specd_rpc::execute_universe_list(client).await?;
        }
        RpcCommands::DeleteUniverse { id } => {
            crate::commands::specd_rpc::execute_universe_delete(client, id).await?;
        }
        RpcCommands::CreateDomain { universe, name, description } => {
            crate::commands::specd_rpc::execute_domain_create(client, universe, name, description).await?;
        }
        RpcCommands::GetDomain { id } => {
            crate::commands::specd_rpc::execute_domain_get(client, id).await?;
        }
        RpcCommands::ListDomains { universe } => {
            crate::commands::specd_rpc::execute_domain_list(client, universe).await?;
        }
        RpcCommands::UpdateDomainConstraints { domain, constraint } => {
            crate::commands::specd_rpc::execute_domain_update_constraints(client, domain, constraint).await?;
        }
        RpcCommands::CreateTransform { source, target, kind } => {
            crate::commands::specd_rpc::execute_transform_create(client, source, target, kind).await?;
        }
        RpcCommands::GetTransform { id } => {
            crate::commands::specd_rpc::execute_transform_get(client, id).await?;
        }
        RpcCommands::ListTransforms => {
            crate::commands::specd_rpc::execute_transform_list(client).await?;
        }
        RpcCommands::VerifyTransformSoundness { id } => {
            crate::commands::specd_rpc::execute_transform_verify_soundness(client, id).await?;
        }
        RpcCommands::CreateAdmissibleSet { spec, constraint } => {
            crate::commands::specd_rpc::execute_admissible_set_create(client, spec, constraint).await?;
        }
        RpcCommands::GetAdmissibleSet { spec } => {
            crate::commands::specd_rpc::execute_admissible_set_get(client, spec).await?;
        }
        RpcCommands::ListAdmissibleSets => {
            crate::commands::specd_rpc::execute_admissible_set_list(client).await?;
        }
        RpcCommands::VerifyConsistency { spec_a, spec_b } => {
            crate::commands::specd_rpc::execute_admissible_set_verify_consistency(client, spec_a, spec_b).await?;
        }
        RpcCommands::VerifyImplication { antecedent, consequent } => {
            crate::commands::specd_rpc::execute_admissible_set_verify_implication(client, antecedent, consequent).await?;
        }
        RpcCommands::ConstructU0 { artifact } => {
            crate::commands::specd_rpc::execute_construct_u0(client, artifact).await?;
        }
        RpcCommands::SyncModel => {
            crate::commands::specd_rpc::execute_sync_model(client).await?;
        }
        RpcCommands::ValidateModel => {
            crate::commands::specd_rpc::execute_validate_model(client).await?;
        }

        // Node/Edge operations removed in v2.0.0
        // Use UDA/f operations instead
        RpcCommands::GenerateContract { id, language } => {
            let resp = client
                .generate_contract_template(Request::new(proto::GenerateContractTemplateRequest {
                    node_id: id,
                    language,
                }))
                .await?;
            let result = resp.into_inner();
            println!("Generated {} contract template:\n", result.node_kind);
            println!("{}", result.template);
        }
        RpcCommands::CheckCompliance { id, code } => {
            let resp = client
                .calculate_compliance(Request::new(proto::CalculateComplianceRequest {
                    node_id: id,
                    code,
                }))
                .await?;
            let result = resp.into_inner();
            println!("Compliance Score: {:.1}%", result.score * 100.0);
            println!("  Keyword overlap:   {:.1}%", result.keyword_overlap * 100.0);
            println!("  Structural match:  {:.1}%", result.structural_match * 100.0);
            println!("  {}", result.explanation);
        }
        RpcCommands::QueryAtTimestamp { timestamp } => {
            let resp = client
                .query_at_timestamp(Request::new(proto::QueryAtTimestampRequest { timestamp }))
                .await?;
            let result = resp.into_inner();
            println!("Graph at timestamp {}:", result.timestamp);
            println!("  Nodes: {}", result.node_count);
            println!("  Edges: {}", result.edge_count);
        }
        RpcCommands::DiffTimestamps { from, to } => {
            let resp = client
                .diff_timestamps(Request::new(proto::DiffTimestampsRequest {
                    from_timestamp: from,
                    to_timestamp: to,
                }))
                .await?;
            let result = resp.into_inner();
            println!("Diff {} -> {}:", result.from_timestamp, result.to_timestamp);
            println!("  Added nodes:    {}", result.added_nodes.len());
            println!("  Removed nodes:  {}", result.removed_nodes.len());
            println!("  Modified nodes: {}", result.modified_nodes.len());
            println!("  Added edges:    {}", result.added_edges.len());
            println!("  Removed edges:  {}", result.removed_edges.len());
        }
        RpcCommands::NodeHistory { id } => {
            let resp = client
                .get_node_history(Request::new(proto::GetNodeHistoryRequest { node_id: id }))
                .await?;
            let result = resp.into_inner();
            if let Some(ref node) = result.node {
                println!("History for [{}]: {}", &node.id[..8.min(node.id.len())], node.content);
            }
            for event in &result.events {
                println!("  [{}] {}: {}", event.timestamp, event.event_type, event.description);
            }
        }
        RpcCommands::ComplianceTrend { id } => {
            let resp = client
                .get_compliance_trend(Request::new(proto::GetComplianceTrendRequest { node_id: id }))
                .await?;
            let result = resp.into_inner();
            if let Some(ref node) = result.node {
                println!("Compliance trend for [{}]: {}", &node.id[..8.min(node.id.len())], node.content);
            }
            println!("  Direction: {}", result.trend_direction);
            for dp in &result.data_points {
                println!("  [{}] {:.1}%", dp.timestamp, dp.score * 100.0);
            }
        }
    }

    Ok(())
}
