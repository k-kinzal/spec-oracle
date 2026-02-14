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
        /// Preview edges without creating them (dry-run mode)
        #[arg(long)]
        dry_run: bool,
        /// Maximum number of edges to create (0 = unlimited)
        #[arg(long, default_value = "0")]
        limit: usize,
        /// Interactive review mode (confirm each edge before creation)
        #[arg(long)]
        interactive: bool,
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
    /// Migrate specifications from JSON file to directory format
    Migrate {
        /// Source JSON file (defaults to .spec/specs.json)
        #[arg(long)]
        source: Option<String>,
        /// Target directory (defaults to .spec/)
        #[arg(long)]
        target: Option<String>,
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

/// Handle AI query using claude or codex CLI
pub async fn handle_ai_query(question: &str, ai_cmd: &str) -> Result<String, Box<dyn std::error::Error>> {
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

    // Auto-detect project-local storage (.spec/nodes/ or .spec/specs.json)
    let storage_type = persistence::detect_storage_type();

    // Standalone mode is the recommended and default mode
    if let Some(storage) = storage_type {
        let (store, display_msg) = match storage {
            persistence::StorageType::Directory(spec_dir) => {
                let msg = format!("📁 Using directory-based storage: {}/nodes/", spec_dir.display());
                (spec_core::Store::from_directory(&spec_dir), msg)
            }
            persistence::StorageType::File(spec_file) => {
                let msg = format!("📁 Using file-based storage: {}", spec_file.display());
                (spec_core::Store::from_file(&spec_file), msg)
            }
        };
        eprintln!("{}", display_msg);
        eprintln!("🚀 Running in standalone mode (no server required)");
        eprintln!();
        return commands::dispatch_standalone(cli.command, store).await;
    }

    // No .spec/ directory found - guide user
    eprintln!("❌ No specification directory found (.spec/)");
    eprintln!();
    eprintln!("To get started:");
    eprintln!("  1. Initialize specifications: spec init");
    eprintln!("  2. Add a specification: spec add \"Your specification here\"");
    eprintln!("  3. Check for issues: spec check");
    eprintln!();
    eprintln!("For more information, see the README or run 'spec init --help'");
    
    std::process::exit(1);
}
