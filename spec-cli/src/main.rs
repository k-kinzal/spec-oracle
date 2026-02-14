mod proto {
    tonic::include_proto!("spec_oracle");
}

use clap::{Parser, Subcommand};
use proto::spec_oracle_client::SpecOracleClient;
use proto::{SpecNodeKind, SpecEdgeKind};
use std::collections::HashMap;
use tonic::Request;
use tracing_subscriber::EnvFilter;

#[derive(Parser)]
#[command(name = "spec")]
#[command(about = "Specification Oracle CLI", long_about = None)]
struct Cli {
    #[arg(short, long, default_value = "http://[::1]:50051")]
    server: String,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Add a new specification node
    AddNode {
        /// Content of the specification
        content: String,
        /// Kind of node: assertion, constraint, scenario, definition, domain
        #[arg(short, long, default_value = "assertion")]
        kind: String,
    },
    /// Get a node by ID
    GetNode {
        /// Node ID
        id: String,
    },
    /// List all nodes (optionally filtered by kind)
    ListNodes {
        /// Filter by kind: assertion, constraint, scenario, definition, domain
        #[arg(short, long)]
        kind: Option<String>,
    },
    /// Remove a node
    RemoveNode {
        /// Node ID
        id: String,
    },
    /// Add an edge between nodes
    AddEdge {
        /// Source node ID
        source: String,
        /// Target node ID
        target: String,
        /// Edge kind: refines, depends_on, contradicts, derives_from, synonym, composes
        #[arg(short, long, default_value = "refines")]
        kind: String,
    },
    /// List edges (optionally for a specific node)
    ListEdges {
        /// Node ID to filter edges
        #[arg(short, long)]
        node: Option<String>,
    },
    /// Remove an edge
    RemoveEdge {
        /// Edge ID
        id: String,
    },
    /// Query specifications using natural language
    Query {
        /// Natural language query
        query: String,
        /// Use AI to enhance query (requires claude or codex CLI)
        #[arg(long)]
        ai: bool,
    },
    /// Detect contradictions in specifications
    DetectContradictions,
    /// Detect omissions in specifications
    DetectOmissions,
    /// Resolve terminology and find synonyms
    ResolveTerm {
        /// Term to resolve
        term: String,
    },
    /// Ask a question using AI (requires claude or codex CLI)
    Ask {
        /// Question in natural language
        question: String,
        /// AI command to use (claude or codex)
        #[arg(long, default_value = "claude")]
        ai_cmd: String,
    },
    /// Detect cross-layer inconsistencies in specifications
    DetectLayerInconsistencies,
    /// Filter nodes by formality layer
    FilterByLayer {
        /// Minimum formality layer (0=natural, 1=structured, 2=formal, 3=executable)
        #[arg(short, long, default_value = "0")]
        min: u32,
        /// Maximum formality layer
        #[arg(short = 'M', long, default_value = "3")]
        max: u32,
    },
    /// Find formalizations of a specification node
    FindFormalizations {
        /// Node ID
        id: String,
    },
    /// Find semantically related terms
    FindRelatedTerms {
        /// Term to search for
        term: String,
        /// Maximum number of results (0 = no limit)
        #[arg(long, default_value = "10")]
        max: u32,
    },
    /// Detect potential synonym pairs
    DetectPotentialSynonyms {
        /// Minimum similarity threshold (0.0-1.0)
        #[arg(long, default_value = "0.3")]
        min_similarity: f32,
    },
    /// Generate executable contract template from specification
    GenerateContract {
        /// Node ID
        id: String,
        /// Target language (rust, python, etc.)
        #[arg(long, default_value = "rust")]
        language: String,
    },
    /// Get test coverage report
    TestCoverage,
}

fn parse_node_kind(s: &str) -> SpecNodeKind {
    match s.to_lowercase().as_str() {
        "assertion" => SpecNodeKind::Assertion,
        "constraint" => SpecNodeKind::Constraint,
        "scenario" => SpecNodeKind::Scenario,
        "definition" => SpecNodeKind::Definition,
        "domain" => SpecNodeKind::Domain,
        _ => SpecNodeKind::Assertion,
    }
}

fn parse_edge_kind(s: &str) -> SpecEdgeKind {
    match s.to_lowercase().as_str() {
        "refines" => SpecEdgeKind::Refines,
        "depends_on" | "depends-on" => SpecEdgeKind::DependsOn,
        "contradicts" => SpecEdgeKind::Contradicts,
        "derives_from" | "derives-from" => SpecEdgeKind::DerivesFrom,
        "synonym" => SpecEdgeKind::Synonym,
        "composes" => SpecEdgeKind::Composes,
        _ => SpecEdgeKind::Refines,
    }
}

fn node_kind_name(k: i32) -> &'static str {
    match SpecNodeKind::try_from(k) {
        Ok(SpecNodeKind::Assertion) => "assertion",
        Ok(SpecNodeKind::Constraint) => "constraint",
        Ok(SpecNodeKind::Scenario) => "scenario",
        Ok(SpecNodeKind::Definition) => "definition",
        Ok(SpecNodeKind::Domain) => "domain",
        _ => "unknown",
    }
}

fn edge_kind_name(k: i32) -> &'static str {
    match SpecEdgeKind::try_from(k) {
        Ok(SpecEdgeKind::Refines) => "refines",
        Ok(SpecEdgeKind::DependsOn) => "depends_on",
        Ok(SpecEdgeKind::Contradicts) => "contradicts",
        Ok(SpecEdgeKind::DerivesFrom) => "derives_from",
        Ok(SpecEdgeKind::Synonym) => "synonym",
        Ok(SpecEdgeKind::Composes) => "composes",
        _ => "unknown",
    }
}

async fn handle_ai_query(question: &str, ai_cmd: &str) -> Result<String, Box<dyn std::error::Error>> {
    let prompt = format!(
        "You are assisting with a specification oracle system. \
         Answer this question based on software specifications:\n\n{question}"
    );

    let output = match ai_cmd {
        "claude" => {
            tokio::process::Command::new("claude")
                .arg("-p")
                .arg(&prompt)
                .output()
                .await?
        }
        "codex" => {
            tokio::process::Command::new("codex")
                .arg("exec")
                .arg(&prompt)
                .output()
                .await?
        }
        _ => {
            return Err(format!("Unknown AI command: {ai_cmd}").into());
        }
    };

    if !output.status.success() {
        return Err(format!(
            "AI command failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )
        .into());
    }

    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    let cli = Cli::parse();
    let mut client = SpecOracleClient::connect(cli.server).await?;

    match cli.command {
        Commands::AddNode { content, kind } => {
            let resp = client
                .add_node(Request::new(proto::AddNodeRequest {
                    content,
                    kind: parse_node_kind(&kind).into(),
                    metadata: HashMap::new(),
                }))
                .await?;
            let node = resp.into_inner().node.unwrap();
            println!("Added node: {}", node.id);
            println!("  Content: {}", node.content);
            println!("  Kind: {}", node_kind_name(node.kind));
        }
        Commands::GetNode { id } => {
            let resp = client
                .get_node(Request::new(proto::GetNodeRequest { id }))
                .await?;
            let node = resp.into_inner().node.unwrap();
            println!("Node: {}", node.id);
            println!("  Content: {}", node.content);
            println!("  Kind: {}", node_kind_name(node.kind));
            if !node.metadata.is_empty() {
                println!("  Metadata:");
                for (k, v) in &node.metadata {
                    println!("    {k}: {v}");
                }
            }
        }
        Commands::ListNodes { kind } => {
            let kind_filter = kind.as_ref().map(|k| parse_node_kind(k).into()).unwrap_or(0);
            let resp = client
                .list_nodes(Request::new(proto::ListNodesRequest { kind_filter }))
                .await?;
            let nodes = resp.into_inner().nodes;
            if nodes.is_empty() {
                println!("No nodes found.");
            } else {
                println!("Found {} node(s):", nodes.len());
                for node in nodes {
                    println!("  [{}] {} - {}", node.id, node_kind_name(node.kind), node.content);
                }
            }
        }
        Commands::RemoveNode { id } => {
            client
                .remove_node(Request::new(proto::RemoveNodeRequest { id: id.clone() }))
                .await?;
            println!("Removed node: {id}");
        }
        Commands::AddEdge { source, target, kind } => {
            let resp = client
                .add_edge(Request::new(proto::AddEdgeRequest {
                    source_id: source,
                    target_id: target,
                    kind: parse_edge_kind(&kind).into(),
                    metadata: HashMap::new(),
                }))
                .await?;
            let edge = resp.into_inner().edge.unwrap();
            println!("Added edge: {}", edge.id);
            println!("  {} --[{}]--> {}", edge.source_id, edge_kind_name(edge.kind), edge.target_id);
        }
        Commands::ListEdges { node } => {
            let resp = client
                .list_edges(Request::new(proto::ListEdgesRequest {
                    node_id: node.unwrap_or_default(),
                }))
                .await?;
            let edges = resp.into_inner().edges;
            if edges.is_empty() {
                println!("No edges found.");
            } else {
                println!("Found {} edge(s):", edges.len());
                for edge in edges {
                    println!("  [{}] {} --[{}]--> {}",
                        edge.id, edge.source_id, edge_kind_name(edge.kind), edge.target_id);
                }
            }
        }
        Commands::RemoveEdge { id } => {
            client
                .remove_edge(Request::new(proto::RemoveEdgeRequest { id: id.clone() }))
                .await?;
            println!("Removed edge: {id}");
        }
        Commands::Query { query, ai } => {
            let search_query = if ai {
                println!("Enhancing query with AI...");
                handle_ai_query(&query, "claude").await?
            } else {
                query
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
                    println!("  [{}] {} - {}", node.id, node_kind_name(node.kind), node.content);
                }
            }
        }
        Commands::DetectContradictions => {
            let resp = client
                .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
                .await?;
            let contradictions = resp.into_inner().contradictions;
            if contradictions.is_empty() {
                println!("No contradictions detected.");
            } else {
                println!("Found {} contradiction(s):", contradictions.len());
                for c in contradictions {
                    let a = c.node_a.unwrap();
                    let b = c.node_b.unwrap();
                    println!("\n  Contradiction:");
                    println!("    Node A [{}]: {}", a.id, a.content);
                    println!("    Node B [{}]: {}", b.id, b.content);
                    println!("    Reason: {}", c.explanation);
                }
            }
        }
        Commands::DetectOmissions => {
            let resp = client
                .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
                .await?;
            let omissions = resp.into_inner().omissions;
            if omissions.is_empty() {
                println!("No omissions detected.");
            } else {
                println!("Found {} omission(s):", omissions.len());
                for o in omissions {
                    println!("\n  {}", o.description);
                    if !o.related_nodes.is_empty() {
                        println!("    Related nodes:");
                        for node in o.related_nodes {
                            println!("      [{}] {}", node.id, node.content);
                        }
                    }
                }
            }
        }
        Commands::ResolveTerm { term } => {
            let resp = client
                .resolve_terminology(Request::new(proto::ResolveTerminologyRequest { term: term.clone() }))
                .await?;
            let result = resp.into_inner();
            println!("Resolving term: '{term}'");
            if !result.definitions.is_empty() {
                println!("\nDefinitions:");
                for def in &result.definitions {
                    println!("  [{}] {}", def.id, def.content);
                }
            }
            if !result.synonyms.is_empty() {
                println!("\nSynonyms:");
                for syn in &result.synonyms {
                    println!("  - {syn}");
                }
            }
            if result.definitions.is_empty() && result.synonyms.is_empty() {
                println!("No definitions or synonyms found.");
            }
        }
        Commands::Ask { question, ai_cmd } => {
            // First, get all relevant specs
            let resp = client
                .list_nodes(Request::new(proto::ListNodesRequest { kind_filter: 0 }))
                .await?;
            let nodes = resp.into_inner().nodes;

            let context = if nodes.is_empty() {
                "No specifications available.".to_string()
            } else {
                let mut ctx = String::from("Available specifications:\n");
                for node in &nodes {
                    ctx.push_str(&format!(
                        "- [{}] {}: {}\n",
                        node.id,
                        node_kind_name(node.kind),
                        node.content
                    ));
                }
                ctx
            };

            let full_prompt = format!(
                "{context}\n\nQuestion: {question}\n\n\
                 Please answer based on the specifications above."
            );

            println!("Asking AI...\n");
            let answer = handle_ai_query(&full_prompt, &ai_cmd).await?;
            println!("{answer}");
        }
        Commands::DetectLayerInconsistencies => {
            let resp = client
                .detect_layer_inconsistencies(Request::new(proto::DetectLayerInconsistenciesRequest {}))
                .await?;
            let inconsistencies = resp.into_inner().inconsistencies;
            if inconsistencies.is_empty() {
                println!("No layer inconsistencies detected.");
            } else {
                println!("Found {} layer inconsistenc(ies):", inconsistencies.len());
                for i in inconsistencies {
                    let src = i.source.unwrap();
                    let tgt = i.target.unwrap();
                    println!("\n  Layer Inconsistency:");
                    println!("    Source [{}] (layer {}): {}", src.id, src.formality_layer, src.content);
                    println!("    Target [{}] (layer {}): {}", tgt.id, tgt.formality_layer, tgt.content);
                    println!("    Reason: {}", i.explanation);
                }
            }
        }
        Commands::FilterByLayer { min, max } => {
            let resp = client
                .filter_by_layer(Request::new(proto::FilterByLayerRequest {
                    min_layer: min,
                    max_layer: max,
                }))
                .await?;
            let nodes = resp.into_inner().nodes;
            if nodes.is_empty() {
                println!("No nodes found in layer range {}-{}.", min, max);
            } else {
                println!("Found {} node(s) in layer range {}-{}:", nodes.len(), min, max);
                for node in nodes {
                    println!("  [{}] {} (layer {}) - {}",
                        node.id, node_kind_name(node.kind), node.formality_layer, node.content);
                }
            }
        }
        Commands::FindFormalizations { id } => {
            let resp = client
                .find_formalizations(Request::new(proto::FindFormalizationsRequest { node_id: id.clone() }))
                .await?;
            let result = resp.into_inner();

            println!("Formalizations for node '{id}':");
            if !result.formalizations.is_empty() {
                println!("\n  More formal versions:");
                for node in &result.formalizations {
                    println!("    [{}] {} (layer {}) - {}",
                        node.id, node_kind_name(node.kind), node.formality_layer, node.content);
                }
            }
            if !result.natural_sources.is_empty() {
                println!("\n  Natural language sources:");
                for node in &result.natural_sources {
                    println!("    [{}] {} (layer {}) - {}",
                        node.id, node_kind_name(node.kind), node.formality_layer, node.content);
                }
            }
            if result.formalizations.is_empty() && result.natural_sources.is_empty() {
                println!("  No formalizations or sources found.");
            }
        }
        Commands::FindRelatedTerms { term, max } => {
            let resp = client
                .find_related_terms(Request::new(proto::FindRelatedTermsRequest {
                    term: term.clone(),
                    max_results: max,
                }))
                .await?;
            let result = resp.into_inner();

            if result.nodes.is_empty() {
                println!("No related terms found for '{term}'.");
            } else {
                println!("Found {} semantically related node(s) for '{term}':", result.nodes.len());
                for scored in result.nodes {
                    if let Some(node) = scored.node {
                        println!("  [{}] {} (score: {:.2}) - {}",
                            node.id, node_kind_name(node.kind), scored.score, node.content);
                    }
                }
            }
        }
        Commands::DetectPotentialSynonyms { min_similarity } => {
            let resp = client
                .detect_potential_synonyms(Request::new(proto::DetectPotentialSynonymsRequest {
                    min_similarity,
                }))
                .await?;
            let result = resp.into_inner();

            if result.candidates.is_empty() {
                println!("No potential synonym pairs detected (threshold: {:.2}).", min_similarity);
            } else {
                println!("Found {} potential synonym pair(s):", result.candidates.len());
                for candidate in result.candidates {
                    let a = candidate.node_a.unwrap();
                    let b = candidate.node_b.unwrap();
                    println!("\n  Potential synonyms (similarity: {:.2}):", candidate.similarity);
                    println!("    [{}] {}", a.id, a.content);
                    println!("    [{}] {}", b.id, b.content);
                }
            }
        }
        Commands::GenerateContract { id, language } => {
            let resp = client
                .generate_contract_template(Request::new(proto::GenerateContractTemplateRequest {
                    node_id: id.clone(),
                    language: language.clone(),
                }))
                .await?;
            let result = resp.into_inner();

            println!("Generated {} contract template for node '{}':\n", result.node_kind, id);
            println!("{}", result.template);
        }
        Commands::TestCoverage => {
            let resp = client
                .get_test_coverage(Request::new(proto::GetTestCoverageRequest {}))
                .await?;
            let result = resp.into_inner();

            println!("Test Coverage Report:");
            println!("  Total testable specs: {}", result.total_testable);
            println!("  Specs with tests: {}", result.with_tests);
            println!("  Coverage: {:.1}%", result.coverage_ratio * 100.0);

            if !result.nodes_without_tests.is_empty() {
                println!("\n  Untested specifications ({}):", result.nodes_without_tests.len());
                for node in result.nodes_without_tests.iter().take(10) {
                    println!("    [{}] {} - {}", node.id, node_kind_name(node.kind), node.content);
                }
                if result.nodes_without_tests.len() > 10 {
                    println!("    ... and {} more", result.nodes_without_tests.len() - 10);
                }
            }

            if !result.nodes_with_tests.is_empty() {
                println!("\n  Tested specifications ({}):", result.nodes_with_tests.len());
                for node in result.nodes_with_tests.iter().take(5) {
                    let test_file = node.metadata.get("test_file").map(|s| s.as_str()).unwrap_or("N/A");
                    println!("    [{}] {} - {} (test: {})",
                        node.id, node_kind_name(node.kind), node.content, test_file);
                }
                if result.nodes_with_tests.len() > 5 {
                    println!("    ... and {} more", result.nodes_with_tests.len() - 5);
                }
            }
        }
    }

    Ok(())
}
