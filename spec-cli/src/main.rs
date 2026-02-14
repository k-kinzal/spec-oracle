mod proto {
    tonic::include_proto!("spec_oracle");
}

mod presentation;
mod persistence;
mod utils;
mod commands;

use clap::{Parser, Subcommand};
use proto::spec_oracle_client::SpecOracleClient;
use proto::{SpecNodeKind, SpecEdgeKind};
use std::collections::HashMap;
use std::path::PathBuf;
use tonic::Request;
use tracing_subscriber::EnvFilter;
use spec_core::{FileStore, NodeKind as CoreNodeKind};
use presentation::formatter::*;
use persistence::store_router::*;
use utils::*;

#[derive(Parser)]
#[command(name = "spec")]
#[command(about = "Specification Oracle CLI", long_about = None)]
struct Cli {
    #[arg(short, long, default_value = "http://[::1]:50051")]
    server: String,

    #[command(subcommand)]
    command: Commands,
}

/// Low-level graph API commands (advanced users)
#[derive(Subcommand)]
enum ApiCommands {
    /// Add a new specification node (direct graph operation)
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
    /// Set universe metadata for a node
    SetUniverse {
        /// Node ID
        id: String,
        /// Universe identifier (e.g., "ui", "api", "database")
        universe: String,
    },
    /// Filter nodes by formality layer
    FilterByLayer {
        /// Minimum formality layer (0=natural, 1=structured, 2=formal, 3=executable)
        #[arg(short, long, default_value = "0")]
        min: u32,
        /// Maximum formality layer
        #[arg(short = 'M', long, default_value = "3")]
        max: u32,
    },
    /// Generate executable contract template from specification
    GenerateContract {
        /// Node ID
        id: String,
        /// Target language (rust, python, etc.)
        #[arg(long, default_value = "rust")]
        language: String,
    },
    /// Calculate compliance score between specification and code
    CheckCompliance {
        /// Node ID
        id: String,
        /// Code snippet or file path (prefix with @ for file)
        code: String,
    },
    /// Query graph state at a specific timestamp
    QueryAtTimestamp {
        /// Unix timestamp (seconds since epoch)
        timestamp: i64,
    },
    /// Show changes between two timestamps
    DiffTimestamps {
        /// Start timestamp (unix seconds)
        from: i64,
        /// End timestamp (unix seconds)
        to: i64,
    },
    /// Show history of changes for a node
    NodeHistory {
        /// Node ID
        id: String,
    },
    /// Show compliance trend over time for a node
    ComplianceTrend {
        /// Node ID
        id: String,
    },
}

#[derive(Subcommand)]
enum Commands {
    /// Add a specification (high-level, auto-infers kind and relationships)
    Add {
        /// Specification content in natural language
        content: String,
        /// Skip automatic relationship inference
        #[arg(long)]
        no_infer: bool,
    },
    /// Low-level graph API operations (for advanced users)
    #[command(subcommand)]
    Api(ApiCommands),
    /// [DEPRECATED] Use 'spec api add-node' instead
    #[command(hide = true)]
    AddNode {
        /// Content of the specification
        content: String,
        /// Kind of node: assertion, constraint, scenario, definition, domain
        #[arg(short, long, default_value = "assertion")]
        kind: String,
    },
    /// [DEPRECATED] Use 'spec api get-node' instead
    #[command(hide = true)]
    GetNode {
        /// Node ID
        id: String,
    },
    /// [DEPRECATED] Use 'spec api list-nodes' instead
    #[command(hide = true)]
    ListNodes {
        /// Filter by kind: assertion, constraint, scenario, definition, domain
        #[arg(short, long)]
        kind: Option<String>,
    },
    /// [DEPRECATED] Use 'spec api remove-node' instead
    #[command(hide = true)]
    RemoveNode {
        /// Node ID
        id: String,
    },
    /// [DEPRECATED] Use 'spec api add-edge' instead
    #[command(hide = true)]
    AddEdge {
        /// Source node ID
        source: String,
        /// Target node ID
        target: String,
        /// Edge kind: refines, depends_on, contradicts, derives_from, synonym, composes
        #[arg(short, long, default_value = "refines")]
        kind: String,
    },
    /// [DEPRECATED] Use 'spec api list-edges' instead
    #[command(hide = true)]
    ListEdges {
        /// Node ID to filter edges
        #[arg(short, long)]
        node: Option<String>,
    },
    /// [DEPRECATED] Use 'spec api remove-edge' instead
    #[command(hide = true)]
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
    /// Check specifications for issues (contradictions and omissions)
    Check,
    /// Display summary statistics of specifications
    Summary,
    /// Find specifications by semantic search (high-level interface)
    Find {
        /// Search query in natural language
        query: String,
        /// Filter by formality layer (0-3)
        #[arg(short, long)]
        layer: Option<u32>,
        /// Maximum number of results
        #[arg(short, long, default_value = "10")]
        max: u32,
    },
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
    /// [DEPRECATED] Use 'spec api filter-by-layer' instead
    #[command(hide = true)]
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
    /// [DEPRECATED] Use 'spec api generate-contract' instead
    #[command(hide = true)]
    GenerateContract {
        /// Node ID
        id: String,
        /// Target language (rust, python, etc.)
        #[arg(long, default_value = "rust")]
        language: String,
    },
    /// Get test coverage report
    TestCoverage,
    /// [DEPRECATED] Use 'spec api check-compliance' instead
    #[command(hide = true)]
    CheckCompliance {
        /// Node ID
        id: String,
        /// Code snippet or file path (prefix with @ for file)
        code: String,
    },
    /// Get compliance report for all specifications
    ComplianceReport,
    /// [DEPRECATED] Use 'spec api query-at-timestamp' instead
    #[command(hide = true)]
    QueryAtTimestamp {
        /// Unix timestamp (seconds since epoch)
        timestamp: i64,
    },
    /// [DEPRECATED] Use 'spec api diff-timestamps' instead
    #[command(hide = true)]
    DiffTimestamps {
        /// Start timestamp (unix seconds)
        from: i64,
        /// End timestamp (unix seconds)
        to: i64,
    },
    /// [DEPRECATED] Use 'spec api node-history' instead
    #[command(hide = true)]
    NodeHistory {
        /// Node ID
        id: String,
    },
    /// [DEPRECATED] Use 'spec api compliance-trend' instead
    #[command(hide = true)]
    ComplianceTrend {
        /// Node ID
        id: String,
    },
    /// Extract specifications from source code
    Extract {
        /// Source directory or file path
        source: String,
        /// Programming language (rust, python, etc.)
        #[arg(long, default_value = "rust")]
        language: String,
        /// Minimum confidence threshold (0.0-1.0)
        #[arg(long, default_value = "0.7")]
        min_confidence: f32,
    },
    /// Detect inter-universe inconsistencies in multi-layered specifications
    DetectInterUniverseInconsistencies,
    /// [DEPRECATED] Use 'spec api set-universe' instead
    #[command(hide = true)]
    SetUniverse {
        /// Node ID
        id: String,
        /// Universe identifier (e.g., "ui", "api", "database")
        universe: String,
    },
    /// Infer relationships for all nodes in the graph
    InferRelationships,
    /// Infer relationships using AI-powered semantic matching (requires claude CLI)
    InferRelationshipsAi {
        /// Minimum confidence threshold (0.0-1.0)
        #[arg(long, default_value = "0.7")]
        min_confidence: f32,
    },
    /// Watch source files and maintain specification synchronization
    Watch {
        /// Source directory to watch
        source: String,
        /// Programming language (rust, python, etc.)
        #[arg(long, default_value = "rust")]
        language: String,
        /// Minimum confidence threshold (0.0-1.0)
        #[arg(long, default_value = "0.7")]
        min_confidence: f32,
        /// Check interval in seconds
        #[arg(long, default_value = "2")]
        interval: u64,
    },
    /// Trace specification relationships across layers (hierarchical display)
    Trace {
        /// Node ID to trace
        id: String,
        /// Maximum depth to traverse (0 = unlimited)
        #[arg(short, long, default_value = "0")]
        depth: usize,
    },
    /// Verify multi-layer specification consistency (formal verification)
    VerifyLayers,
    /// Prove consistency between two specifications (formal proof generation)
    ProveConsistency {
        /// First specification ID
        spec_a: String,
        /// Second specification ID
        spec_b: String,
    },
    /// Prove satisfiability of a specification (formal proof generation)
    ProveSatisfiability {
        /// Specification ID to prove satisfiable
        spec: String,
    },
    /// Inspect U/D/A/f model structure (display universes, domains, admissible sets, transforms)
    InspectModel {
        /// Show detailed information for each universe
        #[arg(long)]
        verbose: bool,
    },
    /// Construct U0 from projection universes via inverse transforms (demonstrate executable theory)
    ConstructU0 {
        /// Actually execute transform strategies
        #[arg(long)]
        execute: bool,
        /// Show detailed extraction results
        #[arg(long)]
        verbose: bool,
    },
    /// Initialize project-local specification management
    Init {
        /// Project root directory (defaults to current directory)
        #[arg(default_value = ".")]
        path: String,
    },
    /// Remove low-quality extracted specifications (cleanup isolated test artifacts)
    CleanupLowQuality {
        /// Actually remove specs (default: dry-run mode)
        #[arg(long)]
        execute: bool,
    },
}


/// Check if two specifications are semantically related using simple heuristics
fn is_semantically_related(content_a: &str, content_b: &str) -> bool {
    let a_lower = content_a.to_lowercase();
    let b_lower = content_b.to_lowercase();

    // Extract meaningful words (filter out common words)
    let stop_words = ["the", "a", "an", "is", "are", "was", "were", "be", "been", "being",
                      "have", "has", "had", "do", "does", "did", "will", "would", "should",
                      "could", "may", "might", "must", "can", "to", "of", "in", "for", "on",
                      "at", "by", "with", "from", "as", "and", "or", "but", "not"];

    let a_words: Vec<&str> = a_lower
        .split(|c: char| !c.is_alphanumeric())
        .filter(|w| w.len() > 3 && !stop_words.contains(w))
        .collect();

    let b_words: Vec<&str> = b_lower
        .split(|c: char| !c.is_alphanumeric())
        .filter(|w| w.len() > 3 && !stop_words.contains(w))
        .collect();

    if a_words.is_empty() || b_words.is_empty() {
        return false;
    }

    // Count common words
    let mut common_count = 0;
    for a_word in &a_words {
        for b_word in &b_words {
            if a_word == b_word {
                common_count += 1;
            } else {
                // Check for word stems (common prefix >= 5 chars)
                let prefix_len = a_word
                    .chars()
                    .zip(b_word.chars())
                    .take_while(|(a, b)| a == b)
                    .count();
                if prefix_len >= 5 {
                    common_count += 1;
                }
            }
        }
    }

    // Related if at least 2 significant words in common
    common_count >= 2
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

/// Run commands in standalone mode (direct file access, no server needed)
async fn run_standalone(command: Commands, spec_path: PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    let mut store = FileStore::new(&spec_path);

    match command {
        Commands::Init { path: _ } => {
            // Init command doesn't need existing spec file
            eprintln!("Error: Init command should not reach standalone mode");
            return Ok(());
        }
        Commands::Add { content, no_infer } => {
            commands::execute_add_standalone(&mut store, content, no_infer)?;
        }
        Commands::Api(api_cmd) => {
            // Low-level graph API operations in standalone mode
            use commands::api;
            match api_cmd {
                ApiCommands::AddNode { content, kind } => {
                    api::execute_add_node_standalone(&mut store, content, kind)?;
                }
                ApiCommands::GetNode { id } => {
                    api::execute_get_node_standalone(&store, id)?;
                }
                ApiCommands::ListNodes { kind } => {
                    api::execute_list_nodes_standalone(&store, kind)?;
                }
                ApiCommands::RemoveNode { id } => {
                    api::execute_remove_node_standalone(&mut store, id)?;
                }
                ApiCommands::AddEdge { source, target, kind } => {
                    api::execute_add_edge_standalone(&mut store, source, target, kind)?;
                }
                ApiCommands::ListEdges { node } => {
                    api::execute_list_edges_standalone(&store, node)?;
                }
                ApiCommands::RemoveEdge { id } => {
                    api::execute_remove_edge_standalone(&mut store, id)?;
                }
                ApiCommands::SetUniverse { id, universe } => {
                    api::execute_set_universe_standalone(&mut store, id, universe)?;
                }
                ApiCommands::FilterByLayer { min, max } => {
                    api::execute_filter_by_layer_standalone(&store, min, max)?;
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
        }
        Commands::ListNodes { kind } => {
            eprintln!("⚠️  WARNING: 'spec list-nodes' is deprecated. Use 'spec api list-nodes' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
            let graph = store.load()?;

            let kind_filter = kind.as_ref().map(|k| proto_to_core_kind(parse_node_kind(k)));
            let nodes = graph.list_nodes(kind_filter);

            println!("Found {} node(s):", nodes.len());
            for node in nodes {
                let kind_str = match node.kind {
                    CoreNodeKind::Assertion => "assertion",
                    CoreNodeKind::Constraint => "constraint",
                    CoreNodeKind::Scenario => "scenario",
                    CoreNodeKind::Definition => "definition",
                    CoreNodeKind::Domain => "domain",
                };
                let layer_label = format_formality_layer(node.formality_layer);
                println!("  [{}] [{}] {} - {}",
                    layer_label,
                    &node.id[..8],
                    kind_str,
                    node.content);
            }
        }
        Commands::DetectContradictions => {
            commands::execute_contradictions_standalone(&store)?;
        }
        Commands::DetectOmissions => {
            commands::execute_omissions_standalone(&store)?;
        }
        Commands::Check => {
            let exit_code = commands::execute_check_standalone(&store)?;
            std::process::exit(exit_code);
        }
        Commands::Summary => {
            commands::execute_summary_standalone(&store)?;
        }
        Commands::Find { query, layer, max } => {
            commands::execute_find_standalone(&store, &query, layer, max).await?;
        }
        Commands::GetNode { id } => {
            eprintln!("⚠️  WARNING: 'spec get-node' is deprecated. Use 'spec api get-node' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
            commands::api::execute_get_node_standalone(&store, id)?;
        }
        Commands::Trace { id, depth } => {
            commands::execute_trace_standalone(&store, &id, depth).await?;
        }
        Commands::VerifyLayers => {
            commands::execute_verify_layers_standalone(&store)?;
        }
        Commands::ProveConsistency { spec_a, spec_b } => {
            commands::execute_prove_consistency_standalone(&store, spec_a, spec_b)?;
        }
        Commands::ProveSatisfiability { spec } => {
            commands::execute_prove_satisfiability_standalone(&store, spec)?;
        }
        Commands::InspectModel { verbose } => {
            commands::execute_inspect_model_standalone(&store, verbose)?;
        }
        Commands::ConstructU0 { execute, verbose } => {
            commands::execute_construct_u0_standalone(&mut store, execute, verbose)?;
        }
        Commands::CleanupLowQuality { execute } => {
            commands::execute_cleanup_low_quality_standalone(&mut store, execute)?;
        }
        Commands::AddEdge { source, target, kind } => {
            eprintln!("⚠️  WARNING: 'spec add-edge' is deprecated. Use 'spec api add-edge' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
            commands::api::execute_add_edge_standalone(&mut store, source, target, kind)?;
        }
        Commands::Extract { source, language, min_confidence } => {
            commands::execute_extract_standalone(&mut store, source, language, min_confidence)?;
        }
        Commands::InferRelationshipsAi { min_confidence } => {
            commands::execute_infer_relationships_ai_standalone(&mut store, min_confidence)?;
        }
        _ => {
            eprintln!("Command not yet supported in standalone mode.");
            eprintln!("For advanced features, use server mode (start specd first).");
            return Err("Unsupported command in standalone mode".into());
        }
    }

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    let cli = Cli::parse();

    // Auto-detect project-local .spec/specs.json
    let spec_file_path = find_spec_file();

    // Use standalone mode if .spec/ directory is detected
    if let Some(spec_path) = spec_file_path {
        eprintln!("📁 Using project-local specifications: {}", spec_path.display());
        eprintln!("🚀 Running in standalone mode (no server required)");
        eprintln!();
        return run_standalone(cli.command, spec_path).await;
    }

    // Otherwise, connect to server
    let mut client = SpecOracleClient::connect(cli.server).await?;

    match cli.command {
        Commands::Add { content, no_infer } => {
            // High-level specification addition with auto-inference
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
                    println!("  Found {} potentially related specification(s):", matches.len());
                    for (i, match_node) in matches.iter().take(3).enumerate() {
                        if match_node.id != node_id {
                            println!("    {}. [{}] {}",
                                i + 1,
                                &match_node.id[..8],
                                match_node.content.chars().take(60).collect::<String>()
                            );

                            // Auto-create refines edge if semantically related
                            if is_semantically_related(&content, &match_node.content) {
                                let _ = client
                                    .add_edge(Request::new(proto::AddEdgeRequest {
                                        source_id: node_id.clone(),
                                        target_id: match_node.id.clone(),
                                        kind: SpecEdgeKind::Refines.into(),
                                        metadata: HashMap::new(),
                                    }))
                                    .await;
                                println!("       → Connected via 'refines' relationship");
                            }
                        }
                    }
                }
            }

            println!("\n✓ Specification added successfully");
            println!("  To view: spec get-node {}", node_id);
            println!("  To check for issues: spec detect-contradictions");
        }
        Commands::Api(api_cmd) => {
            // Low-level graph API operations
            match api_cmd {
                ApiCommands::AddNode { content, kind } => {
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
                ApiCommands::GetNode { id } => {
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
                ApiCommands::ListNodes { kind } => {
                    let kind_filter = kind.as_ref().map(|k| parse_node_kind(k).into()).unwrap_or(0);
                    let resp = client
                        .list_nodes(Request::new(proto::ListNodesRequest { kind_filter }))
                        .await?;
                    let nodes = resp.into_inner().nodes;
                    println!("Found {} node(s):", nodes.len());
                    for node in nodes {
                        println!("  [{}] {} - {}",
                            &node.id[..8],
                            node_kind_name(node.kind),
                            node.content.chars().take(80).collect::<String>()
                        );
                    }
                }
                ApiCommands::RemoveNode { id } => {
                    client
                        .remove_node(Request::new(proto::RemoveNodeRequest { id: id.clone() }))
                        .await?;
                    println!("Removed node: {}", id);
                }
                ApiCommands::AddEdge { source, target, kind } => {
                    let edge_kind = match kind.to_lowercase().as_str() {
                        "refines" => SpecEdgeKind::Refines,
                        "depends_on" => SpecEdgeKind::DependsOn,
                        "contradicts" => SpecEdgeKind::Contradicts,
                        "derives_from" => SpecEdgeKind::DerivesFrom,
                        "synonym" => SpecEdgeKind::Synonym,
                        "composes" => SpecEdgeKind::Composes,
                        "formalizes" => SpecEdgeKind::Formalizes,
                        _ => SpecEdgeKind::Refines,
                    };
                    let resp = client
                        .add_edge(Request::new(proto::AddEdgeRequest {
                            source_id: source,
                            target_id: target,
                            kind: edge_kind.into(),
                            metadata: HashMap::new(),
                        }))
                        .await?;
                    let edge = resp.into_inner().edge.unwrap();
                    println!("Added edge: {}", edge.id);
                }
                ApiCommands::ListEdges { node } => {
                    let resp = client
                        .list_edges(Request::new(proto::ListEdgesRequest {
                            node_id: node.unwrap_or_default(),
                        }))
                        .await?;
                    let edges = resp.into_inner().edges;
                    println!("Found {} edge(s):", edges.len());
                    for edge in edges {
                        println!("  {} --[{}]--> {}",
                            &edge.source_id[..8],
                            edge_kind_name(edge.kind),
                            &edge.target_id[..8]
                        );
                    }
                }
                ApiCommands::RemoveEdge { id } => {
                    client
                        .remove_edge(Request::new(proto::RemoveEdgeRequest { id: id.clone() }))
                        .await?;
                    println!("Removed edge: {}", id);
                }
                ApiCommands::SetUniverse { id, universe } => {
                    let mut metadata = HashMap::new();
                    metadata.insert("universe".to_string(), universe.clone());
                    client
                        .add_node(Request::new(proto::AddNodeRequest {
                            content: String::new(),
                            kind: SpecNodeKind::Assertion.into(),
                            metadata,
                        }))
                        .await?;
                    println!("Set universe for node {}: {}", id, universe);
                }
                ApiCommands::FilterByLayer { min, max } => {
                    println!("Filtering nodes by formality layer {} to {}", min, max);
                    // This requires server support - for now, just list all and filter client-side
                    let resp = client
                        .list_nodes(Request::new(proto::ListNodesRequest { kind_filter: 0 }))
                        .await?;
                    let nodes = resp.into_inner().nodes;
                    let filtered: Vec<_> = nodes.iter()
                        .filter(|n| {
                            let layer = parse_formality_layer(n.formality_layer as u8);
                            layer >= min && layer <= max
                        })
                        .collect();
                    println!("Found {} node(s) in layers {}-{}:", filtered.len(), min, max);
                    for node in filtered {
                        println!("  [L{}] [{}] {}",
                            parse_formality_layer(node.formality_layer as u8),
                            &node.id[..8],
                            node.content.chars().take(80).collect::<String>()
                        );
                    }
                }
                ApiCommands::GenerateContract { id, language } => {
                    println!("Generating {} contract for specification {}", language, id);
                    println!("Contract generation not yet implemented");
                }
                ApiCommands::CheckCompliance { id, code } => {
                    println!("Checking compliance for specification {}", id);
                    println!("Compliance checking not yet implemented");
                }
                ApiCommands::QueryAtTimestamp { timestamp } => {
                    println!("Querying graph at timestamp {}", timestamp);
                    println!("Temporal queries not yet implemented");
                }
                ApiCommands::DiffTimestamps { from, to } => {
                    println!("Diffing graph from {} to {}", from, to);
                    println!("Temporal diff not yet implemented");
                }
                ApiCommands::NodeHistory { id } => {
                    println!("History for node {}", id);
                    println!("Node history not yet implemented");
                }
                ApiCommands::ComplianceTrend { id } => {
                    println!("Compliance trend for node {}", id);
                    println!("Compliance trend not yet implemented");
                }
            }
        }
        Commands::AddNode { content, kind } => {
            eprintln!("⚠️  WARNING: 'spec add-node' is deprecated. Use 'spec api add-node' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
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
            eprintln!("⚠️  WARNING: 'spec get-node' is deprecated. Use 'spec api get-node' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
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
            eprintln!("⚠️  WARNING: 'spec list-nodes' is deprecated. Use 'spec api list-nodes' instead.");
            eprintln!("   The command will still work but may be removed in a future version.\n");
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
                    let layer_label = format_formality_layer(node.formality_layer as u8);
                    println!("  [{}] [{}] {} - {}",
                        layer_label,
                        node.id,
                        node_kind_name(node.kind),
                        node.content);
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
            commands::execute_query_server(&mut client, &query, ai).await?;
        }
        Commands::DetectContradictions => {
            commands::execute_contradictions_server(&mut client).await?;
        }
        Commands::DetectOmissions => {
            commands::execute_omissions_server(&mut client).await?;
        }
        Commands::Check => {
            println!("🔍 Checking specifications...\n");

            // Check contradictions
            println!("  Checking for contradictions...");
            let contra_resp = client
                .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
                .await?;
            let contradictions = contra_resp.into_inner().contradictions;
            if contradictions.is_empty() {
                println!("  ✓ No contradictions found");
            } else {
                println!("  ⚠️  {} contradiction(s) found", contradictions.len());
            }

            // Check omissions
            println!("  Checking for omissions...");
            let omit_resp = client
                .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
                .await?;
            let omissions = omit_resp.into_inner().omissions;
            if omissions.is_empty() {
                println!("  ✓ No isolated specifications");
            } else {
                println!("  ⚠️  {} isolated specification(s)", omissions.len());
            }

            // Summary
            println!("\n📊 Summary:");
            println!("  Contradictions: {}", contradictions.len());
            println!("  Isolated specs: {}", omissions.len());

            let total_issues = contradictions.len() + omissions.len();
            if total_issues == 0 {
                println!("\n✅ All checks passed! No issues found.");
            } else if contradictions.is_empty() {
                println!("\n⚠️  Minor issues found (isolated specifications may need relationships)");

                // Show first few omissions as examples
                if !omissions.is_empty() {
                    println!("\nExamples of isolated specifications:");
                    for (i, o) in omissions.iter().take(3).enumerate() {
                        println!("  {}. {}", i + 1, o.description);
                        if !o.related_nodes.is_empty() {
                            for n in &o.related_nodes {
                                println!("     - [{}] {}", n.id, n.content);
                            }
                        }
                    }
                    if omissions.len() > 3 {
                        println!("  ... and {} more", omissions.len() - 3);
                    }
                }
            } else {
                println!("\n❌ Critical issues found!");

                // Show contradictions
                println!("\nContradictions:");
                for (i, c) in contradictions.iter().enumerate() {
                    let a = c.node_a.as_ref().unwrap();
                    let b = c.node_b.as_ref().unwrap();
                    println!("  {}. {}", i + 1, c.explanation);
                    println!("     A: [{}] {}", a.id, a.content);
                    println!("     B: [{}] {}", b.id, b.content);
                }
            }
        }
        Commands::Summary => {
            // Get all nodes
            let nodes_resp = client
                .list_nodes(Request::new(proto::ListNodesRequest {
                    kind_filter: 0, // 0 means no filter
                }))
                .await?;
            let nodes = nodes_resp.into_inner().nodes;
            let total = nodes.len();

            // Count by kind
            let mut by_kind = HashMap::new();
            for node in &nodes {
                let kind = SpecNodeKind::try_from(node.kind).unwrap_or(SpecNodeKind::Assertion);
                *by_kind.entry(kind).or_insert(0) += 1;
            }

            // Count by layer
            let mut by_layer = HashMap::new();
            for node in &nodes {
                let layer = parse_formality_layer(node.formality_layer as u8);
                *by_layer.entry(layer).or_insert(0) += 1;
            }

            // Count edges
            let edges_resp = client
                .list_edges(Request::new(proto::ListEdgesRequest {
                    node_id: String::new(), // Empty string to get all edges
                }))
                .await?;
            let total_edges = edges_resp.into_inner().edges.len();

            // Health metrics
            let contra_resp = client
                .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
                .await?;
            let contradictions = contra_resp.into_inner().contradictions;

            let omit_resp = client
                .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
                .await?;
            let isolated = omit_resp.into_inner().omissions;

            // Display summary
            println!("📊 Specification Summary\n");
            println!("Total Specifications: {}", total);
            println!();

            println!("By Kind:");
            for (kind, count) in &by_kind {
                let kind_str = match kind {
                    SpecNodeKind::Assertion => "  Assertions",
                    SpecNodeKind::Constraint => "  Constraints",
                    SpecNodeKind::Scenario => "  Scenarios",
                    SpecNodeKind::Definition => "  Definitions",
                    SpecNodeKind::Domain => "  Domains",
                    SpecNodeKind::Unspecified => "  Unspecified",
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
        }
        Commands::Find { query, layer, max } => {
            commands::execute_find_server(&mut client, &query, layer, max).await?;
        }
        Commands::Trace { id, depth } => {
            commands::execute_trace_server(&mut client, &id, depth).await?;
        }
        Commands::VerifyLayers => {
            println!("🔍 Verifying multi-layer specification consistency...\n");

            // Get all nodes
            let list_resp = client
                .list_nodes(Request::new(proto::ListNodesRequest { kind_filter: 0 }))
                .await?;
            let all_nodes = list_resp.into_inner().nodes;

            // Categorize by layer
            let mut u0_nodes = Vec::new();
            let mut u1_nodes = Vec::new();
            let mut u2_nodes = Vec::new();
            let mut u3_nodes = Vec::new();

            for node in &all_nodes {
                let layer = parse_formality_layer(node.formality_layer as u8);

                match layer {
                    0 => u0_nodes.push(node),
                    1 => u1_nodes.push(node),
                    2 => u2_nodes.push(node),
                    3 => u3_nodes.push(node),
                    _ => {}
                }
            }

            println!("📊 Layer Distribution:");
            println!("   U0 (Requirements):     {} specs", u0_nodes.len());
            println!("   U1 (Formal):           {} specs", u1_nodes.len());
            println!("   U2 (Interface):        {} specs", u2_nodes.len());
            println!("   U3 (Implementation):   {} specs", u3_nodes.len());
            println!();

            // Get all edges to build adjacency information
            let edges_resp = client
                .list_edges(Request::new(proto::ListEdgesRequest { node_id: String::new() }))
                .await?;
            let all_edges = edges_resp.into_inner().edges;

            // Build forward and backward maps for Formalizes edges
            let mut formalizes_forward: HashMap<String, Vec<String>> = HashMap::new();
            let mut formalizes_backward: HashMap<String, Vec<String>> = HashMap::new();

            for edge in &all_edges {
                if edge.kind == proto::SpecEdgeKind::Formalizes as i32 {
                    formalizes_forward.entry(edge.source_id.clone())
                        .or_insert_with(Vec::new)
                        .push(edge.target_id.clone());
                    formalizes_backward.entry(edge.target_id.clone())
                        .or_insert_with(Vec::new)
                        .push(edge.source_id.clone());
                }
            }

            // Check U0 → U3 completeness
            println!("🔬 Checking Completeness (U0 → U3):");
            let mut incomplete_count = 0;

            for u0_node in &u0_nodes {
                // Traverse forward via Formalizes edges to find U3 nodes
                let mut visited = std::collections::HashSet::new();
                let mut u3_found = false;
                let mut queue = vec![u0_node.id.clone()];

                while let Some(current_id) = queue.pop() {
                    if visited.contains(&current_id) {
                        continue;
                    }
                    visited.insert(current_id.clone());

                    if let Some(targets) = formalizes_forward.get(&current_id) {
                        for target_id in targets {
                            // Check if target is U3
                            if let Some(target_node) = all_nodes.iter().find(|n| &n.id == target_id) {
                                let target_layer = target_node.metadata.get("formality_layer")
                                    .and_then(|s| s.parse::<u32>().ok())
                                    .unwrap_or(target_node.formality_layer);

                                if target_layer == 3 {
                                    u3_found = true;
                                    break;
                                }
                                queue.push(target_id.clone());
                            }
                        }
                    }

                    if u3_found {
                        break;
                    }
                }

                if !u3_found {
                    incomplete_count += 1;
                    println!("   ⚠️  [{}] {} (no U3 implementation)", u0_node.id, u0_node.content);
                }
            }

            if incomplete_count == 0 {
                println!("   ✅ All {} U0 requirements have U3 implementations", u0_nodes.len());
            } else {
                println!("   ⚠️  {} of {} U0 requirements lack U3 implementations", incomplete_count, u0_nodes.len());
            }
            println!();

            // Check U3 → U0 soundness
            println!("🔬 Checking Soundness (U3 → U0):");
            let mut unsound_count = 0;

            for u3_node in &u3_nodes {
                // Traverse backward via Formalizes edges to find U0 nodes
                let mut visited = std::collections::HashSet::new();
                let mut u0_found = false;
                let mut queue = vec![u3_node.id.clone()];

                while let Some(current_id) = queue.pop() {
                    if visited.contains(&current_id) {
                        continue;
                    }
                    visited.insert(current_id.clone());

                    if let Some(sources) = formalizes_backward.get(&current_id) {
                        for source_id in sources {
                            // Check if source is U0
                            if let Some(source_node) = all_nodes.iter().find(|n| &n.id == source_id) {
                                let source_layer = source_node.metadata.get("formality_layer")
                                    .and_then(|s| s.parse::<u32>().ok())
                                    .unwrap_or(source_node.formality_layer);

                                if source_layer == 0 {
                                    u0_found = true;
                                    break;
                                }
                                queue.push(source_id.clone());
                            }
                        }
                    }

                    if u0_found {
                        break;
                    }
                }

                if !u0_found {
                    unsound_count += 1;
                    println!("   ⚠️  [{}] {} (no U0 requirement)", u3_node.id, u3_node.content);
                }
            }

            if unsound_count == 0 {
                println!("   ✅ All {} U3 implementations trace to U0 requirements", u3_nodes.len());
            } else {
                println!("   ⚠️  {} of {} U3 implementations lack U0 requirements", unsound_count, u3_nodes.len());
            }
            println!();

            // Summary
            println!("📊 Verification Summary:");

            let completeness_ratio = if u0_nodes.is_empty() {
                100.0
            } else {
                (u0_nodes.len() - incomplete_count) as f64 / u0_nodes.len() as f64 * 100.0
            };

            let soundness_ratio = if u3_nodes.is_empty() {
                100.0
            } else {
                (u3_nodes.len() - unsound_count) as f64 / u3_nodes.len() as f64 * 100.0
            };

            println!("   Completeness (U0→U3): {:.1}%", completeness_ratio);
            println!("   Soundness (U3→U0):    {:.1}%", soundness_ratio);
            println!();

            if incomplete_count == 0 && unsound_count == 0 {
                println!("✅ Multi-layer verification PASSED");
                println!("   All requirements have implementations.");
                println!("   All implementations trace to requirements.");
            } else {
                println!("⚠️  Multi-layer verification found issues:");
                if incomplete_count > 0 {
                    println!("   {} incomplete requirements (U0 without U3)", incomplete_count);
                }
                if unsound_count > 0 {
                    println!("   {} unsound implementations (U3 without U0)", unsound_count);
                }
            }
        }
        Commands::ProveConsistency { spec_a: _, spec_b: _ } => {
            println!("🔬 Proving Consistency\n");
            println!("ProveConsistency command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
            println!("\nReason: Prover integration with U/D/A/f model requires direct file access.");
        }
        Commands::ProveSatisfiability { spec: _ } => {
            println!("🔬 Proving Satisfiability\n");
            println!("ProveSatisfiability command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
            println!("\nReason: Prover integration with U/D/A/f model requires direct file access.");
        }
        Commands::InspectModel { verbose } => {
            println!("🔍 Inspecting U/D/A/f Model Structure\n");
            println!("═══════════════════════════════════════════════════════════════\n");

            // Get all nodes
            let list_resp = client
                .list_nodes(Request::new(proto::ListNodesRequest { kind_filter: 0 }))
                .await?;
            let all_nodes = list_resp.into_inner().nodes;

            // Analyze Universes (U)
            println!("📦 Universes (U):");
            println!("   The specification space is stratified into formality layers:\n");

            let mut layer_stats = std::collections::HashMap::new();
            let mut universe_metadata = std::collections::HashMap::new();

            for node in &all_nodes {
                let layer = parse_formality_layer(node.formality_layer as u8);
                *layer_stats.entry(layer).or_insert(0) += 1;

                if let Some(universe) = node.metadata.get("universe") {
                    *universe_metadata.entry(universe.clone()).or_insert(0) += 1;
                }
            }

            for layer in 0..=3 {
                let count = layer_stats.get(&layer).unwrap_or(&0);
                let layer_name = match layer {
                    0 => "U0 (Root Requirements)",
                    1 => "U1 (Formal Specifications)",
                    2 => "U2 (Interface Definitions)",
                    3 => "U3 (Executable Implementations)",
                    _ => "U? (Unknown)",
                };
                println!("   • {}: {} specifications", layer_name, count);
            }
            println!();

            if !universe_metadata.is_empty() {
                println!("   Distinct universe tags:");
                for (universe, count) in &universe_metadata {
                    println!("     - \"{}\": {} nodes", universe, count);
                }
                println!();
            }

            // Analyze Domains (D)
            println!("🌐 Domains (D):");
            println!("   The target scope of specifications:\n");

            let domain_nodes: Vec<_> = all_nodes.iter()
                .filter(|n| n.kind == proto::SpecNodeKind::Domain as i32)
                .collect();

            if domain_nodes.is_empty() {
                println!("   ⚠️  No explicit domain boundaries defined");
                println!("      (Domain definitions help prevent specification leakage)\n");
            } else {
                for node in &domain_nodes {
                    println!("   • [{}] {}", &node.id[..8], node.content);
                }
                println!();
            }

            // Analyze Admissible Sets (A)
            println!("✓ Admissible Sets (A):");
            println!("   The set of permitted implementations for each specification:\n");

            let constraint_count = all_nodes.iter()
                .filter(|n| n.kind == proto::SpecNodeKind::Constraint as i32)
                .count();
            let assertion_count = all_nodes.iter()
                .filter(|n| n.kind == proto::SpecNodeKind::Assertion as i32)
                .count();
            let scenario_count = all_nodes.iter()
                .filter(|n| n.kind == proto::SpecNodeKind::Scenario as i32)
                .count();

            println!("   • Constraints (∀): {} universal invariants", constraint_count);
            println!("   • Assertions:      {} concrete claims", assertion_count);
            println!("   • Scenarios (∃):   {} existential requirements", scenario_count);
            println!();
            println!("   Note: Each specification implicitly defines A = {{impl | impl satisfies spec}}");
            println!("         Explicit A computation is not yet implemented.\n");

            // Analyze Transform Functions (f)
            println!("🔗 Transform Functions (f):");
            println!("   Mappings between universes that preserve specification semantics:\n");

            let edges_resp = client
                .list_edges(Request::new(proto::ListEdgesRequest { node_id: String::new() }))
                .await?;
            let all_edges = edges_resp.into_inner().edges;

            let mut transform_counts = std::collections::HashMap::new();

            for edge in &all_edges {
                *transform_counts.entry(edge.kind).or_insert(0) += 1;
            }

            let edge_descriptions = [
                (proto::SpecEdgeKind::Formalizes as i32, "f: Ui → Uj (formalization)"),
                (proto::SpecEdgeKind::Transform as i32, "f: Ui → Uj (transformation)"),
                (proto::SpecEdgeKind::Refines as i32, "refinement (within-layer)"),
                (proto::SpecEdgeKind::DerivesFrom as i32, "derivation (provenance)"),
                (proto::SpecEdgeKind::DependsOn as i32, "dependency"),
                (proto::SpecEdgeKind::Contradicts as i32, "contradiction (⊥)"),
                (proto::SpecEdgeKind::Synonym as i32, "equivalence (≡)"),
                (proto::SpecEdgeKind::Composes as i32, "composition"),
            ];

            for (kind, description) in &edge_descriptions {
                if let Some(count) = transform_counts.get(kind) {
                    println!("   • {:20}: {} edges", description, count);
                }
            }
            println!();

            // Theory alignment
            println!("📐 Theoretical Model Status:");
            println!("   From conversation.md and motivation.md:\n");

            println!("   ✅ U (Universe):       Implemented via formality_layer (0-3)");
            println!("   ⚠️  D (Domain):         Partially implemented (NodeKind::Domain exists)");
            println!("   ✅ A (Admissible Set): Populated from graph nodes");
            println!("   ✅ f (Transform):      Transform functions NOW EXECUTABLE via RustExtractor");
            println!();

            println!("   Key insight from motivation.md:");
            println!("   U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ f₀₃⁻¹(U3)");
            println!("   (Root specs are the union of inverse mappings from all layers)\n");

            // Verification metrics
            println!("📊 Model Consistency:");
            let complete_ratio = if let Some(&u0_count) = layer_stats.get(&0) {
                let complete = layer_stats.get(&3).unwrap_or(&0);
                (complete * 100) / u0_count.max(1)
            } else {
                0
            };

            println!("   Completeness estimate:  ~{}%", complete_ratio);
            println!("   (Percentage of U0 requirements with U3 implementations)");
            println!("   Run 'spec verify-layers' for precise multi-layer verification.\n");

            if verbose {
                println!("═══════════════════════════════════════════════════════════════");
                println!("Verbose Mode: Detailed Node Distribution\n");

                for layer in 0..=3 {
                    let layer_name = match layer {
                        0 => "U0",
                        1 => "U1",
                        2 => "U2",
                        3 => "U3",
                        _ => "U?",
                    };

                    let layer_nodes: Vec<_> = all_nodes.iter()
                        .filter(|n| parse_formality_layer(n.formality_layer as u8) == layer)
                        .collect();

                    if !layer_nodes.is_empty() {
                        println!("{} Specifications ({}):", layer_name, layer_nodes.len());
                        for node in layer_nodes.iter().take(5) {
                            let preview = if node.content.len() > 60 {
                                format!("{}...", &node.content[..57])
                            } else {
                                node.content.clone()
                            };
                            println!("  • [{}] {}", &node.id[..8], preview);
                        }
                        if layer_nodes.len() > 5 {
                            println!("  ... and {} more", layer_nodes.len() - 5);
                        }
                        println!();
                    }
                }
            }

            println!("═══════════════════════════════════════════════════════════════");
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
            commands::execute_detect_layer_inconsistencies_server(&mut client).await?;
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
        Commands::CheckCompliance { id, code } => {
            let code_content = if code.starts_with('@') {
                let file_path = &code[1..];
                std::fs::read_to_string(file_path)
                    .map_err(|e| format!("Failed to read file {}: {}", file_path, e))?
            } else {
                code
            };

            let resp = client
                .calculate_compliance(Request::new(proto::CalculateComplianceRequest {
                    node_id: id.clone(),
                    code: code_content,
                }))
                .await?;
            let result = resp.into_inner();

            println!("Compliance Analysis for node '{}':", id);
            println!("  Overall Score: {:.1}% ({}/100)", result.score * 100.0,
                (result.score * 100.0) as u32);
            println!("  Keyword Overlap: {:.1}%", result.keyword_overlap * 100.0);
            println!("  Structural Match: {:.1}%", result.structural_match * 100.0);
            println!("  Assessment: {}", result.explanation);

            // Visual indicator
            let bar_length = (result.score * 40.0) as usize;
            let bar = "█".repeat(bar_length) + &"░".repeat(40 - bar_length);
            println!("\n  [{}]", bar);
        }
        Commands::ComplianceReport => {
            let resp = client
                .get_compliance_report(Request::new(proto::GetComplianceReportRequest {}))
                .await?;
            let result = resp.into_inner();

            if result.entries.is_empty() {
                println!("No specifications with linked code found.");
                println!("Link code using metadata: 'impl_code' or 'test_code'");
            } else {
                println!("Compliance Report ({} specifications):\n", result.entries.len());

                // Calculate statistics
                let total_score: f32 = result.entries.iter().map(|e| e.score).sum();
                let avg_score = total_score / result.entries.len() as f32;
                let high_compliance = result.entries.iter().filter(|e| e.score > 0.8).count();
                let low_compliance = result.entries.iter().filter(|e| e.score < 0.5).count();

                println!("  Average Compliance: {:.1}%", avg_score * 100.0);
                println!("  High Compliance (>80%): {}", high_compliance);
                println!("  Low Compliance (<50%): {}", low_compliance);

                println!("\n  Individual Scores:");
                for entry in result.entries {
                    let node = entry.node.unwrap();
                    let score_pct = (entry.score * 100.0) as u32;
                    let indicator = if entry.score > 0.8 { "✓" } else if entry.score < 0.5 { "✗" } else { "~" };
                    println!("    {} {:3}% [{}] {} - {}",
                        indicator, score_pct, node.id, node_kind_name(node.kind),
                        node.content.chars().take(60).collect::<String>());
                }
            }
        }
        Commands::QueryAtTimestamp { timestamp } => {
            let resp = client
                .query_at_timestamp(Request::new(proto::QueryAtTimestampRequest {
                    timestamp,
                }))
                .await?;
            let result = resp.into_inner();

            let dt = chrono::DateTime::from_timestamp(result.timestamp, 0)
                .map(|d| d.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                .unwrap_or_else(|| format!("timestamp {}", result.timestamp));

            println!("Graph State at {}:\n", dt);
            println!("  Nodes: {}", result.node_count);
            println!("  Edges: {}", result.edge_count);

            if !result.nodes.is_empty() {
                println!("\n  Nodes:");
                for node in result.nodes.iter().take(10) {
                    println!("    [{}] {} - {}",
                        node.id, node_kind_name(node.kind),
                        node.content.chars().take(60).collect::<String>());
                }
                if result.nodes.len() > 10 {
                    println!("    ... and {} more", result.nodes.len() - 10);
                }
            }
        }
        Commands::DiffTimestamps { from, to } => {
            let resp = client
                .diff_timestamps(Request::new(proto::DiffTimestampsRequest {
                    from_timestamp: from,
                    to_timestamp: to,
                }))
                .await?;
            let result = resp.into_inner();

            let from_dt = chrono::DateTime::from_timestamp(result.from_timestamp, 0)
                .map(|d| d.format("%Y-%m-%d %H:%M:%S").to_string())
                .unwrap_or_else(|| format!("{}", result.from_timestamp));
            let to_dt = chrono::DateTime::from_timestamp(result.to_timestamp, 0)
                .map(|d| d.format("%Y-%m-%d %H:%M:%S").to_string())
                .unwrap_or_else(|| format!("{}", result.to_timestamp));

            println!("Changes from {} to {}:\n", from_dt, to_dt);

            if !result.added_nodes.is_empty() {
                println!("  Added Nodes ({}):", result.added_nodes.len());
                for node in result.added_nodes.iter().take(5) {
                    println!("    + [{}] {} - {}",
                        node.id, node_kind_name(node.kind),
                        node.content.chars().take(60).collect::<String>());
                }
                if result.added_nodes.len() > 5 {
                    println!("    ... and {} more", result.added_nodes.len() - 5);
                }
            }

            if !result.removed_nodes.is_empty() {
                println!("\n  Removed Nodes ({}):", result.removed_nodes.len());
                for node in result.removed_nodes.iter().take(5) {
                    println!("    - [{}] {} - {}",
                        node.id, node_kind_name(node.kind),
                        node.content.chars().take(60).collect::<String>());
                }
                if result.removed_nodes.len() > 5 {
                    println!("    ... and {} more", result.removed_nodes.len() - 5);
                }
            }

            if !result.modified_nodes.is_empty() {
                println!("\n  Modified Nodes ({}):", result.modified_nodes.len());
                for change in result.modified_nodes.iter().take(5) {
                    if let (Some(from), Some(to)) = (&change.from_node, &change.to_node) {
                        println!("    ~ [{}] {} -> {}",
                            from.id,
                            from.content.chars().take(30).collect::<String>(),
                            to.content.chars().take(30).collect::<String>());
                    }
                }
                if result.modified_nodes.len() > 5 {
                    println!("    ... and {} more", result.modified_nodes.len() - 5);
                }
            }

            if result.added_nodes.is_empty() && result.removed_nodes.is_empty() && result.modified_nodes.is_empty() {
                println!("  No changes detected in this time range.");
            }
        }
        Commands::NodeHistory { id } => {
            let resp = client
                .get_node_history(Request::new(proto::GetNodeHistoryRequest {
                    node_id: id.clone(),
                }))
                .await?;
            let result = resp.into_inner();

            if let Some(node) = result.node {
                println!("History for node '{}':", id);
                println!("  Content: {}\n", node.content);

                if result.events.is_empty() {
                    println!("  No history events recorded.");
                } else {
                    println!("  Timeline ({} events):", result.events.len());
                    for event in result.events {
                        let dt = chrono::DateTime::from_timestamp(event.timestamp, 0)
                            .map(|d| d.format("%Y-%m-%d %H:%M:%S").to_string())
                            .unwrap_or_else(|| format!("{}", event.timestamp));
                        println!("    {} - {} - {}", dt, event.event_type, event.description);
                    }
                }
            } else {
                println!("Node '{}' not found.", id);
            }
        }
        Commands::ComplianceTrend { id } => {
            let resp = client
                .get_compliance_trend(Request::new(proto::GetComplianceTrendRequest {
                    node_id: id.clone(),
                }))
                .await?;
            let result = resp.into_inner();

            if let Some(node) = result.node {
                println!("Compliance Trend for node '{}':", id);
                println!("  Content: {}\n", node.content);

                if result.data_points.is_empty() {
                    println!("  No compliance data available.");
                    println!("  Store compliance scores in metadata as 'compliance_<timestamp>'");
                } else {
                    println!("  Trend Direction: {}", result.trend_direction);
                    println!("  Data Points ({}):", result.data_points.len());
                    for point in result.data_points {
                        let dt = chrono::DateTime::from_timestamp(point.timestamp, 0)
                            .map(|d| d.format("%Y-%m-%d %H:%M:%S").to_string())
                            .unwrap_or_else(|| format!("{}", point.timestamp));
                        let score_pct = (point.score * 100.0) as u32;
                        let bar_length = (point.score * 20.0) as usize;
                        let bar = "█".repeat(bar_length) + &"░".repeat(20 - bar_length);
                        println!("    {} - {:3}% [{}]", dt, score_pct, bar);
                    }
                }
            } else {
                println!("Node '{}' not found or no compliance data.", id);
            }
        }
        Commands::Extract { source, language, min_confidence } => {
            // Extract specifications locally (doesn't need server for extraction)
            use spec_core::{RustExtractor, ProtoExtractor, DocExtractor, InferredSpecification};
            use std::path::Path;

            let path = Path::new(&source);

            println!("🔍 Extracting specifications from: {}\n", source);

            // Detect language from file extension if not specified
            let detected_language = if path.is_file() {
                match path.extension().and_then(|s| s.to_str()) {
                    Some("rs") => "rust",
                    Some("proto") => "proto",
                    _ => &language,
                }
            } else {
                &language
            };

            let specs: Vec<InferredSpecification> = if path.is_file() {
                match detected_language {
                    "rust" => RustExtractor::extract(path).map_err(|e| {
                        tonic::Status::internal(format!("Extraction failed: {}", e))
                    })?,
                    "proto" => ProtoExtractor::extract(path).map_err(|e| {
                        tonic::Status::internal(format!("Extraction failed: {}", e))
                    })?,
                    _ => {
                        eprintln!("❌ Unsupported language: {}. Supported: rust, proto", language);
                        return Ok(());
                    }
                }
            } else if path.is_dir() {
                // Extract from all supported files in directory
                use std::fs;
                let mut all_specs = Vec::new();
                for entry in fs::read_dir(path).map_err(|e| {
                    tonic::Status::internal(format!("Failed to read directory: {}", e))
                })? {
                    let entry = entry.map_err(|e| {
                        tonic::Status::internal(format!("Failed to read entry: {}", e))
                    })?;
                    let entry_path = entry.path();
                    match entry_path.extension().and_then(|s| s.to_str()) {
                        Some("rs") if detected_language == "rust" || detected_language == "auto" => {
                            match RustExtractor::extract(&entry_path) {
                                Ok(specs) => all_specs.extend(specs),
                                Err(e) => eprintln!("⚠️  Failed to extract from {:?}: {}", entry_path, e),
                            }
                        }
                        Some("proto") if detected_language == "proto" || detected_language == "auto" => {
                            match ProtoExtractor::extract(&entry_path) {
                                Ok(specs) => all_specs.extend(specs),
                                Err(e) => eprintln!("⚠️  Failed to extract from {:?}: {}", entry_path, e),
                            }
                        }
                        Some("md") if detected_language == "markdown" || detected_language == "auto" => {
                            match DocExtractor::extract(&entry_path) {
                                Ok(specs) => all_specs.extend(specs),
                                Err(e) => eprintln!("⚠️  Failed to extract from {:?}: {}", entry_path, e),
                            }
                        }
                        _ => {}
                    }
                }
                all_specs
            } else {
                eprintln!("❌ Source path not found: {}", source);
                return Ok(());
            };

            // Filter by confidence
            let filtered: Vec<_> = specs.into_iter()
                .filter(|s| s.confidence >= min_confidence)
                .collect();

            println!("Extracted {} specifications (confidence >= {}):\n", filtered.len(), min_confidence);

            // Create nodes via server
            for spec in &filtered {
                let kind = match spec.kind {
                    spec_core::NodeKind::Assertion => SpecNodeKind::Assertion,
                    spec_core::NodeKind::Constraint => SpecNodeKind::Constraint,
                    spec_core::NodeKind::Scenario => SpecNodeKind::Scenario,
                    spec_core::NodeKind::Definition => SpecNodeKind::Definition,
                    spec_core::NodeKind::Domain => SpecNodeKind::Domain,
                };

                let mut metadata = spec.metadata.clone();
                metadata.insert("confidence".to_string(), spec.confidence.to_string());
                metadata.insert("extracted".to_string(), "true".to_string());
                metadata.insert("formality_layer".to_string(), spec.formality_layer.to_string());

                let resp = client
                    .add_node(Request::new(proto::AddNodeRequest {
                        content: spec.content.clone(),
                        kind: kind as i32,
                        metadata,
                    }))
                    .await?;

                if let Some(node) = resp.into_inner().node {
                    println!("  [{}] {} ({}:{})",
                        node.id[..8].to_string(),
                        spec.content,
                        spec.source_file,
                        spec.source_line
                    );
                }
            }

            println!("\n✓ Extracted and ingested {} specifications", filtered.len());
        }
        Commands::DetectInterUniverseInconsistencies => {
            let resp = client
                .detect_inter_universe_inconsistencies(Request::new(
                    proto::DetectInterUniverseInconsistenciesRequest {},
                ))
                .await?;
            let inconsistencies = resp.into_inner().inconsistencies;
            if inconsistencies.is_empty() {
                println!("No inter-universe inconsistencies detected.");
            } else {
                println!(
                    "Found {} inter-universe inconsistenc(ies):",
                    inconsistencies.len()
                );
                for i in inconsistencies {
                    let spec_a = i.spec_a.unwrap();
                    let spec_b = i.spec_b.unwrap();
                    println!("\n  Inter-Universe Inconsistency:");
                    println!("    Universe A: '{}'", i.universe_a);
                    println!(
                        "      Spec [{}]: {}",
                        spec_a.id, spec_a.content
                    );
                    println!("    Universe B: '{}'", i.universe_b);
                    println!(
                        "      Spec [{}]: {}",
                        spec_b.id, spec_b.content
                    );
                    if !i.transform_path.is_empty() {
                        println!("    Transform path: {:?}", i.transform_path);
                    }
                    println!("    Reason: {}", i.explanation);
                }
            }
        }
        Commands::SetUniverse { id, universe } => {
            let resp = client
                .set_node_universe(Request::new(proto::SetNodeUniverseRequest {
                    node_id: id.clone(),
                    universe: universe.clone(),
                }))
                .await?;
            if let Some(node) = resp.into_inner().node {
                println!(
                    "✓ Set universe '{}' for node [{}]: {}",
                    universe, id, node.content
                );
            } else {
                println!("Failed to set universe for node '{}'", id);
            }
        }
        Commands::InferRelationships => {
            println!("Inferring relationships for all nodes...");
            let resp = client
                .infer_all_relationships(Request::new(proto::InferAllRelationshipsRequest {}))
                .await?;
            let result = resp.into_inner();

            println!("✓ Created {} new edges automatically", result.edges_created);

            if result.suggestions_count > 0 {
                println!("\nSuggestions for human review ({} total):", result.suggestions_count);
                for (i, suggestion) in result.suggestions.iter().take(10).enumerate() {
                    println!("  {}. {}", i + 1, suggestion);
                }
                if result.suggestions.len() > 10 {
                    println!("  ... and {} more", result.suggestions.len() - 10);
                }
            }
        }
        Commands::InferRelationshipsAi { min_confidence } => {
            println!("🤖 Inferring relationships with AI-powered semantic matching...");
            println!("   Minimum confidence: {:.2}", min_confidence);
            println!("   This may take a while for large specification sets.\n");

            let resp = client
                .infer_all_relationships_with_ai(Request::new(proto::InferAllRelationshipsWithAiRequest {
                    min_confidence,
                }))
                .await?;
            let result = resp.into_inner();

            println!("\n✓ Created {} new edges automatically", result.edges_created);

            if result.suggestions_count > 0 {
                println!("\nSuggestions for human review ({} total):", result.suggestions_count);
                for (i, suggestion) in result.suggestions.iter().take(10).enumerate() {
                    println!("  {}. {}", i + 1, suggestion);
                }
                if result.suggestions.len() > 10 {
                    println!("  ... and {} more", result.suggestions.len() - 10);
                }
            }
        }
        Commands::Watch { source, language, min_confidence, interval } => {
            commands::execute_watch_server(&mut client, source, language, min_confidence, interval).await?;
        }
        Commands::Init { path } => {
            commands::execute_init(path)?;
        }
        Commands::ConstructU0 { execute: _, verbose: _ } => {
            println!("ConstructU0 command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
        }
        Commands::CleanupLowQuality { execute: _ } => {
            println!("CleanupLowQuality command requires standalone mode (project-local .spec/ directory)");
            println!("Run 'spec init' to initialize project-local specification management.");
            println!("\nReason: This command directly modifies the specification database.");
        }
    }

    Ok(())
}

