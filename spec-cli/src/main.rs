mod proto {
    tonic::include_proto!("spec_oracle");
}

mod presentation;
mod utils;
mod commands;

use clap::{Parser, Subcommand};
use proto::spec_oracle_client::SpecOracleClient;
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

/// Low-level RPC commands for advanced users
///
/// These commands provide direct access to specd's UDA/f operations.
/// For most use cases, prefer high-level commands like `spec add`, `spec summary`, etc.
#[derive(Subcommand)]
enum RpcCommands {
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

    // === specd RPC Operations (managing UDA/f model) ===
    /// Create a new universe
    CreateUniverse {
        /// Universe layer (1 for U1, 2 for U2, 3 for U3, etc.)
        #[arg(short, long)]
        layer: u32,
        /// Universe name (e.g., "TLA+", "gRPC", "Rust")
        #[arg(short, long)]
        name: String,
        /// Universe description
        #[arg(short, long, default_value = "")]
        description: String,
    },
    /// Get universe details
    GetUniverse {
        /// Universe ID
        id: String,
    },
    /// List all universes
    ListUniverses,
    /// Delete a universe
    DeleteUniverse {
        /// Universe ID
        id: String,
    },

    /// Create a new domain
    CreateDomain {
        /// Universe ID
        #[arg(short, long)]
        universe: String,
        /// Domain name
        #[arg(short, long)]
        name: String,
        /// Domain description
        #[arg(short, long, default_value = "")]
        description: String,
    },
    /// Get domain details
    GetDomain {
        /// Domain ID
        id: String,
    },
    /// List all domains
    ListDomains {
        /// Filter by universe ID
        #[arg(short, long)]
        universe: Option<String>,
    },
    /// Update domain constraints
    UpdateDomainConstraints {
        /// Domain ID
        #[arg(short, long)]
        domain: String,
        /// Constraints to add (can be specified multiple times)
        #[arg(short, long)]
        constraint: Vec<String>,
    },

    /// Create a new transform
    CreateTransform {
        /// Source universe ID
        #[arg(short, long)]
        source: String,
        /// Target universe ID
        #[arg(short, long)]
        target: String,
        /// Transform kind (forward, inverse, parallel)
        #[arg(short, long, default_value = "forward")]
        kind: String,
    },
    /// Get transform details
    GetTransform {
        /// Transform ID
        id: String,
    },
    /// List all transforms
    ListTransforms,
    /// Verify transform soundness
    VerifyTransformSoundness {
        /// Transform ID
        id: String,
    },

    /// Create a new admissible set
    CreateAdmissibleSet {
        /// Specification ID
        #[arg(short, long)]
        spec: String,
        /// Constraints (can be specified multiple times)
        #[arg(short, long)]
        constraint: Vec<String>,
    },
    /// Get admissible set details
    GetAdmissibleSet {
        /// Specification ID
        spec: String,
    },
    /// List all admissible sets
    ListAdmissibleSets,
    /// Verify consistency between two admissible sets
    VerifyConsistency {
        /// First specification ID
        #[arg(short = 'a', long)]
        spec_a: String,
        /// Second specification ID
        #[arg(short = 'b', long)]
        spec_b: String,
    },
    /// Verify implication between two admissible sets
    VerifyImplication {
        /// Antecedent specification ID (implies)
        #[arg(short, long)]
        antecedent: String,
        /// Consequent specification ID (is implied)
        #[arg(short, long)]
        consequent: String,
    },

    /// Construct U0 from artifacts (reverse mapping)
    ConstructU0 {
        /// Artifact paths (can be specified multiple times)
        #[arg(short, long)]
        artifact: Vec<String>,
    },
    /// Sync model from repository (specd operation)
    SyncModel,
    /// Validate model consistency (specd operation)
    ValidateModel,
}

/// Project management subcommands
#[derive(Subcommand)]
enum ProjectCommands {
    /// Create a new project
    Create {
        /// Project name
        name: String,
        /// Project description
        #[arg(short, long, default_value = "")]
        description: String,
    },
    /// List all projects
    List,
    /// Switch to a project
    Use {
        /// Project name to switch to
        name: String,
    },
    /// Delete a project
    Delete {
        /// Project name to delete
        name: String,
    },
    /// Show the current active project
    Current,
    /// Import a project from legacy .spec/ directory
    Import {
        /// Project name to create
        name: String,
        /// Project description
        #[arg(short, long, default_value = "")]
        description: String,
        /// Path to .spec/ directory
        #[arg(short, long)]
        path: String,
    },
}

#[derive(Subcommand)]
enum Commands {
    /// Manage projects (create, list, switch, delete)
    #[command(subcommand)]
    Project(ProjectCommands),

    /// Add a specification (high-level, auto-infers kind and relationships)
    Add {
        /// Specification content in natural language
        content: String,
        /// Skip automatic relationship inference
        #[arg(long)]
        no_infer: bool,
    },
    /// Low-level specd RPC operations (for advanced users)
    #[command(subcommand)]
    Rpc(RpcCommands),
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
        /// Filter by lifecycle status (active, deprecated, archived)
        #[arg(short, long)]
        status: Option<String>,
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
    /// Get test coverage report
    TestCoverage,
    /// Get compliance report for all specifications
    ComplianceReport,
    /// Detect inter-universe inconsistencies in multi-layered specifications
    DetectInterUniverseInconsistencies,
    /// Infer relationships for all nodes in the graph
    InferRelationships,
    /// Trace specification relationships across layers (hierarchical display)
    Trace {
        /// Node ID to trace
        id: String,
        /// Maximum depth to traverse (0 = unlimited)
        #[arg(short, long, default_value = "0")]
        depth: usize,
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
    /// Export specification graph in DOT format for visualization
    ExportDot {
        /// Output file path (defaults to stdout if not specified)
        #[arg(short, long)]
        output: Option<String>,
        /// Filter by formality layer (0-3)
        #[arg(short, long)]
        layer: Option<u32>,
        /// Include metadata in node labels
        #[arg(short, long)]
        metadata: bool,
    },
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

    // Always connect to specd
    let client = match SpecOracleClient::connect(cli.server.clone()).await {
        Ok(c) => c,
        Err(_) => {
            eprintln!("Cannot connect to specd at {}", cli.server);
            eprintln!();
            eprintln!("Make sure specd is running:");
            eprintln!("  cargo run --bin specd");
            eprintln!();
            eprintln!("Or specify a custom address:");
            eprintln!("  spec --server http://localhost:50051 <command>");
            std::process::exit(1);
        }
    };

    commands::dispatch(cli.command, client).await
}
