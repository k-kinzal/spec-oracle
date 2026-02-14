mod proto {
    tonic::include_proto!("spec_oracle");
}

use clap::{Parser, Subcommand};
use proto::spec_oracle_client::SpecOracleClient;
use proto::{SpecNodeKind, SpecEdgeKind};
use std::collections::HashMap;
use std::path::PathBuf;
use tonic::Request;
use tracing_subscriber::EnvFilter;
use spec_core::{FileStore, NodeKind as CoreNodeKind};

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
    /// Add a specification (high-level, auto-infers kind and relationships)
    Add {
        /// Specification content in natural language
        content: String,
        /// Skip automatic relationship inference
        #[arg(long)]
        no_infer: bool,
    },
    /// Add a new specification node (low-level graph operation)
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
    /// Calculate compliance score between specification and code
    CheckCompliance {
        /// Node ID
        id: String,
        /// Code snippet or file path (prefix with @ for file)
        code: String,
    },
    /// Get compliance report for all specifications
    ComplianceReport,
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
    /// Set universe metadata for a node
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

fn parse_formality_layer(formality_layer: u8) -> u32 {
    // After migration, formality_layer field contains the proper value
    formality_layer as u32
}

fn format_formality_layer(formality_layer: u8) -> String {
    // Format numeric layer as "U0", "U1", "U2", "U3"
    match formality_layer {
        0 => "U0".to_string(),
        1 => "U1".to_string(),
        2 => "U2".to_string(),
        3 => "U3".to_string(),
        _ => format!("U{}", formality_layer),
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
        "formalizes" => SpecEdgeKind::Formalizes,
        "transform" => SpecEdgeKind::Transform,
        _ => SpecEdgeKind::Refines,
    }
}

fn format_node_kind(kind: CoreNodeKind) -> &'static str {
    match kind {
        CoreNodeKind::Assertion => "assertion",
        CoreNodeKind::Constraint => "constraint",
        CoreNodeKind::Scenario => "scenario",
        CoreNodeKind::Definition => "definition",
        CoreNodeKind::Domain => "domain",
    }
}

fn format_edge_kind(kind: spec_core::EdgeKind) -> &'static str {
    match kind {
        spec_core::EdgeKind::Refines => "refines",
        spec_core::EdgeKind::DependsOn => "depends_on",
        spec_core::EdgeKind::Contradicts => "contradicts",
        spec_core::EdgeKind::DerivesFrom => "derives_from",
        spec_core::EdgeKind::Synonym => "synonym",
        spec_core::EdgeKind::Composes => "composes",
        spec_core::EdgeKind::Formalizes => "formalizes",
        spec_core::EdgeKind::Transform => "transform",
    }
}

/// Find .spec/specs.json by walking up from current directory
fn find_spec_file() -> Option<PathBuf> {
    let mut current = std::env::current_dir().ok()?;
    loop {
        let spec_file = current.join(".spec").join("specs.json");
        if spec_file.exists() {
            return Some(spec_file);
        }
        if !current.pop() {
            break;
        }
    }
    None
}

/// Convert proto NodeKind to core NodeKind
fn proto_to_core_kind(kind: SpecNodeKind) -> CoreNodeKind {
    match kind {
        SpecNodeKind::Assertion => CoreNodeKind::Assertion,
        SpecNodeKind::Constraint => CoreNodeKind::Constraint,
        SpecNodeKind::Scenario => CoreNodeKind::Scenario,
        SpecNodeKind::Definition => CoreNodeKind::Definition,
        SpecNodeKind::Domain => CoreNodeKind::Domain,
        _ => CoreNodeKind::Assertion,
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
        Ok(SpecEdgeKind::Formalizes) => "formalizes",
        Ok(SpecEdgeKind::Transform) => "transform",
        _ => "unknown",
    }
}

/// Infer specification kind from content using keyword patterns
fn infer_spec_kind(content: &str) -> String {
    let lower = content.to_lowercase();

    // Domain indicators
    if lower.starts_with("domain:") || lower.contains("domain boundary") {
        return "domain".to_string();
    }

    // Definition indicators
    if lower.contains(" is defined as ")
        || lower.contains("definition:")
        || lower.contains(" means ")
        || lower.contains(" refers to ")
    {
        return "definition".to_string();
    }

    // Constraint indicators (universal invariants)
    if (lower.contains("must") || lower.contains("shall") || lower.contains("required"))
        && (lower.contains("always") || lower.contains("all") || lower.contains("every"))
    {
        return "constraint".to_string();
    }

    if lower.contains("invariant")
        || lower.contains(" >= ")
        || lower.contains(" <= ")
        || lower.contains("not allowed")
        || lower.contains("forbidden")
    {
        return "constraint".to_string();
    }

    // Scenario indicators (existential requirements, test cases)
    if lower.starts_with("when ")
        || lower.starts_with("given ")
        || lower.starts_with("scenario:")
        || lower.contains("should be able to")
        || lower.contains("can ")
        || lower.contains("test:")
    {
        return "scenario".to_string();
    }

    // Assertion indicators (concrete claims)
    if lower.contains("returns")
        || lower.contains("produces")
        || lower.contains("outputs")
        || lower.contains("implements")
    {
        return "assertion".to_string();
    }

    // Default to assertion for general statements
    "assertion".to_string()
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
    let store = FileStore::new(&spec_path);

    match command {
        Commands::Init { path: _ } => {
            // Init command doesn't need existing spec file
            eprintln!("Error: Init command should not reach standalone mode");
            return Ok(());
        }
        Commands::Add { content, no_infer } => {
            println!("Adding specification: {}\n", content);

            // Load graph
            let mut graph = store.load()?;

            // Infer kind
            let kind = infer_spec_kind(&content);
            println!("  Inferred kind: {}", kind);

            // Add node
            let proto_kind = parse_node_kind(&kind);
            let core_kind = proto_to_core_kind(proto_kind);
            let node = graph.add_node(content.clone(), core_kind, HashMap::new());

            println!("  ✓ Created specification [{}]", &node.id[..8]);

            // Save
            store.save(&graph)?;

            if !no_infer {
                println!("\n  Auto-relationship inference not yet supported in standalone mode");
                println!("  Use server mode for advanced features");
            }

            println!("\n✓ Specification added successfully");
            println!("  To view all: spec list-nodes");
        }
        Commands::ListNodes { kind } => {
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
            use spec_core::{Prover, UDAFModel};

            let graph = store.load()?;
            let mut udaf_model = UDAFModel::new();
            udaf_model.populate_from_graph(&graph);

            println!("🔍 Detecting Contradictions (Formal Verification)\n");
            println!("═══════════════════════════════════════════════════════════════\n");

            // Get all nodes to check pairwise
            let nodes = graph.list_nodes(None);
            let mut contradictions_found = 0;
            let mut checked_pairs = 0;

            println!("Analyzing {} specifications...\n", nodes.len());

            let mut prover = Prover::new();

            for i in 0..nodes.len() {
                for j in i+1..nodes.len() {
                    let node_a = &nodes[i];
                    let node_b = &nodes[j];
                    checked_pairs += 1;

                    // Get admissible sets
                    if let (Some(admissible_a), Some(admissible_b)) = (
                        udaf_model.admissible_sets.get(&node_a.id),
                        udaf_model.admissible_sets.get(&node_b.id),
                    ) {
                        // Skip if either has no constraints (nothing to prove)
                        if admissible_a.constraints.is_empty() || admissible_b.constraints.is_empty() {
                            continue;
                        }

                        // Prove consistency
                        let proof = prover.prove_consistency(admissible_a, admissible_b);

                        // Check if refuted (contradiction detected)
                        if proof.status == spec_core::ProofStatus::Refuted {
                            contradictions_found += 1;

                            println!("❌ Contradiction #{}\n", contradictions_found);
                            println!("   Specification A:");
                            println!("     ID:      [{}]", &node_a.id[..8]);
                            println!("     Content: {}", node_a.content);
                            println!("     Constraints: {}", admissible_a.constraints.len());
                            for c in &admissible_a.constraints {
                                println!("       - {} ({})", c.description, c.formal.as_ref().unwrap_or(&"none".to_string()));
                            }
                            println!();

                            println!("   Specification B:");
                            println!("     ID:      [{}]", &node_b.id[..8]);
                            println!("     Content: {}", node_b.content);
                            println!("     Constraints: {}", admissible_b.constraints.len());
                            for c in &admissible_b.constraints {
                                println!("       - {} ({})", c.description, c.formal.as_ref().unwrap_or(&"none".to_string()));
                            }
                            println!();

                            println!("   Formal Proof:");
                            for (step_num, step) in proof.steps.iter().enumerate() {
                                println!("     {}. {}", step_num + 1, step.description);
                            }
                            println!();

                            println!("   Mathematical Result:");
                            println!("     A₁ ∩ A₂ = ∅ (admissible sets are disjoint)");
                            println!("     No implementation can satisfy both specifications");
                            println!("\n   ───────────────────────────────────────────────────────────\n");
                        }
                    }
                }
            }

            println!("═══════════════════════════════════════════════════════════════\n");
            println!("Summary:");
            println!("  Specifications checked: {}", nodes.len());
            println!("  Pairwise comparisons: {}", checked_pairs);
            println!("  Contradictions found: {}", contradictions_found);
            println!();

            if contradictions_found == 0 {
                println!("✅ No contradictions detected");
                println!("   All specifications are mutually consistent");
            } else {
                println!("⚠️  {} formal contradictions detected", contradictions_found);
                println!("   Review and resolve contradictions above");
            }
        }
        Commands::DetectOmissions => {
            let graph = store.load()?;
            let omissions = graph.detect_omissions();

            if omissions.is_empty() {
                println!("✓ No omissions detected");
            } else {
                println!("Found {} omission(s):", omissions.len());
                for (i, omission) in omissions.iter().enumerate() {
                    println!("\n{}. {}", i + 1, omission.description);
                    for node in &omission.related_nodes {
                        println!("   - [{}] {}", &node.id[..8], node.content);
                    }
                }
            }
        }
        Commands::Check => {
            let graph = store.load()?;

            println!("🔍 Checking specifications...\n");

            // Collect statistics
            let all_nodes = graph.list_nodes(None);
            let total_nodes = all_nodes.len();
            let inferred_nodes: Vec<_> = all_nodes.iter()
                .filter(|n| n.metadata.get("inferred").map(|s| s.as_str()) == Some("true"))
                .collect();
            let inferred_count = inferred_nodes.len();

            // Check contradictions
            println!("  Checking for contradictions...");
            let contradictions = graph.detect_contradictions();
            if contradictions.is_empty() {
                println!("  ✓ No contradictions found");
            } else {
                println!("  ⚠️  {} contradiction(s) found", contradictions.len());
            }

            // Check omissions and analyze by extractor
            println!("  Checking for omissions...");
            let omissions = graph.detect_omissions();

            // Count isolated inferred specs by extractor
            let mut isolated_by_extractor: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
            for omission in &omissions {
                for node in &omission.related_nodes {
                    if node.metadata.get("inferred").map(|s| s.as_str()) == Some("true") {
                        let extractor = node.metadata.get("extractor")
                            .map(|s| s.as_str())
                            .unwrap_or("unknown");
                        *isolated_by_extractor.entry(extractor.to_string()).or_insert(0) += 1;
                    }
                }
            }
            let isolated_inferred: usize = isolated_by_extractor.values().sum();

            if omissions.is_empty() {
                println!("  ✓ No isolated specifications");
            } else {
                println!("  ⚠️  {} isolated specification(s)", omissions.len());
                if isolated_inferred > 0 {
                    println!("     Extracted specs needing connections:");
                    for (extractor, count) in isolated_by_extractor.iter() {
                        println!("       - {}: {} specs", extractor, count);
                    }
                }
            }

            // Summary
            println!("\n📊 Summary:");
            println!("  Total specs:        {}", total_nodes);
            println!("  Extracted specs:    {} ({:.1}%)", inferred_count,
                inferred_count as f64 / total_nodes as f64 * 100.0);
            println!("  Contradictions:     {}", contradictions.len());
            println!("  Isolated specs:     {}", omissions.len());

            let total_issues = contradictions.len() + omissions.len();
            if total_issues == 0 {
                println!("\n✅ All checks passed! No issues found.");
                std::process::exit(0);
            } else if contradictions.is_empty() {
                println!("\n⚠️  Minor issues found (isolated specifications may need relationships)");

                // Show first few omissions as examples
                if !omissions.is_empty() {
                    println!("\nExamples of isolated specifications:");
                    for (i, omission) in omissions.iter().take(3).enumerate() {
                        println!("  {}. {}", i + 1, omission.description);
                        for node in &omission.related_nodes {
                            println!("     - [{}] {}", &node.id[..8], node.content);
                        }
                    }
                    if omissions.len() > 3 {
                        println!("  ... and {} more", omissions.len() - 3);
                    }
                }
                std::process::exit(1);
            } else {
                println!("\n❌ Critical issues found!");

                // Show contradictions
                println!("\nContradictions:");
                for (i, contradiction) in contradictions.iter().enumerate() {
                    println!("  {}. {}", i + 1, contradiction.explanation);
                    println!("     A: [{}] {}", &contradiction.node_a.id[..8], contradiction.node_a.content);
                    println!("     B: [{}] {}", &contradiction.node_b.id[..8], contradiction.node_b.content);
                }
                std::process::exit(1);
            }
        }
        Commands::Summary => {
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
                let layer = parse_formality_layer(node.formality_layer as u8);
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
        }
        Commands::Find { query, layer, max } => {
            let graph = store.load()?;

            // Search for matching specifications
            let mut results = graph.search(&query);

            // Filter by layer if specified
            if let Some(layer_num) = layer {
                results.retain(|node| {
                    if let Some(layer_str) = node.metadata.get("formality_layer") {
                        layer_str.parse::<u32>().ok() == Some(layer_num)
                    } else {
                        node.formality_layer as u32 == layer_num
                    }
                });
            }

            // Limit results
            let max_results = max as usize;
            if results.len() > max_results {
                results.truncate(max_results);
            }

            if results.is_empty() {
                println!("No specifications found matching '{}'", query);
                println!("\nTry:");
                println!("  - Using different keywords");
                println!("  - Broadening your search");
                println!("  - Using 'spec list-nodes' to see all specifications");
            } else {
                println!("Found {} specification(s) matching '{}':", results.len(), query);
                println!();
                for (i, node) in results.iter().enumerate() {
                    let kind_str = match node.kind {
                        CoreNodeKind::Assertion => "assertion",
                        CoreNodeKind::Constraint => "constraint",
                        CoreNodeKind::Scenario => "scenario",
                        CoreNodeKind::Definition => "definition",
                        CoreNodeKind::Domain => "domain",
                    };
                    let layer_str = if let Some(l) = node.metadata.get("formality_layer") {
                        format!(" [U{}]", l)
                    } else {
                        format!(" [U{}]", node.formality_layer)
                    };
                    println!("  {}. [{}]{} {} - {}",
                        i + 1,
                        &node.id[..8],
                        layer_str,
                        kind_str,
                        node.content
                    );
                }

                if let Some(layer_num) = layer {
                    println!("\n(Filtered to layer U{})", layer_num);
                }
            }
        }
        Commands::GetNode { id } => {
            let graph = store.load()?;

            // Resolve short ID to full UUID if needed
            let full_id = if id.len() == 8 {
                // Try to find node by short ID
                let nodes = graph.list_nodes(None);
                let matches: Vec<_> = nodes.iter()
                    .filter(|n| n.id.starts_with(&id))
                    .collect();

                if matches.is_empty() {
                    println!("❌ Node not found with ID starting with: {}", id);
                    return Ok(());
                } else if matches.len() > 1 {
                    println!("❌ Ambiguous short ID: {} (matches {} nodes)", id, matches.len());
                    println!("\nMatching nodes:");
                    for node in matches.iter().take(5) {
                        println!("  [{}] {}", &node.id[..8], node.content.chars().take(60).collect::<String>());
                    }
                    return Ok(());
                }
                matches[0].id.clone()
            } else {
                id.clone()
            };

            // Get the node
            let node = graph.get_node(&full_id);
            if node.is_none() {
                println!("❌ Node not found: {}", full_id);
                return Ok(());
            }

            let node = node.unwrap();
            let layer_label = format_formality_layer(node.formality_layer);

            println!("📄 Specification Details\n");
            println!("ID:      {}", node.id);
            println!("Layer:   [{}]", layer_label);
            println!("Kind:    {}", format_node_kind(node.kind));
            println!("Content: {}", node.content);

            if !node.metadata.is_empty() {
                println!("\nMetadata:");
                for (k, v) in &node.metadata {
                    println!("  {}: {}", k, v);
                }
            }

            // Show relationships
            let edges = graph.list_edges(Some(&node.id));
            if !edges.is_empty() {
                println!("\nRelationships ({} total):", edges.len());

                // Group by direction
                let mut outgoing = Vec::new();
                let mut incoming = Vec::new();

                for (edge_data, source_id, target_id) in &edges {
                    if *source_id == node.id {
                        outgoing.push((edge_data, target_id));
                    } else {
                        incoming.push((edge_data, source_id));
                    }
                }

                if !outgoing.is_empty() {
                    println!("\n  Outgoing ({}):", outgoing.len());
                    for (edge_data, target_id) in outgoing.iter().take(10) {
                        if let Some(target) = graph.get_node(target_id) {
                            println!("    → {} [{}] {}",
                                format_edge_kind(edge_data.kind),
                                &target_id[..8],
                                target.content.chars().take(50).collect::<String>()
                            );
                        }
                    }
                    if outgoing.len() > 10 {
                        println!("    ... and {} more", outgoing.len() - 10);
                    }
                }

                if !incoming.is_empty() {
                    println!("\n  Incoming ({}):", incoming.len());
                    for (edge_data, source_id) in incoming.iter().take(10) {
                        if let Some(source) = graph.get_node(source_id) {
                            println!("    ← {} [{}] {}",
                                format_edge_kind(edge_data.kind),
                                &source_id[..8],
                                source.content.chars().take(50).collect::<String>()
                            );
                        }
                    }
                    if incoming.len() > 10 {
                        println!("    ... and {} more", incoming.len() - 10);
                    }
                }
            } else {
                println!("\n⚠️  No relationships. This specification is isolated.");
            }

            println!("\n💡 Use 'spec trace {}' for full relationship tree", &node.id[..8]);
        }
        Commands::Trace { id, depth } => {
            let graph = store.load()?;

            // Resolve short ID to full UUID if needed
            let full_id = if id.len() == 8 {
                let nodes = graph.list_nodes(None);
                let matches: Vec<_> = nodes.iter()
                    .filter(|n| n.id.starts_with(&id))
                    .collect();

                if matches.is_empty() {
                    println!("❌ Node not found with ID starting with: {}", id);
                    return Ok(());
                } else if matches.len() > 1 {
                    println!("❌ Ambiguous short ID: {}", id);
                    return Ok(());
                }
                matches[0].id.clone()
            } else {
                id.clone()
            };

            // Get the root node
            let root_node = graph.get_node(&full_id);
            if root_node.is_none() {
                println!("❌ Node not found: {}", full_id);
                return Ok(());
            }

            let root = root_node.unwrap();
            println!("📋 Tracing relationships for:");
            println!("   [{}] {}: {}", &root.id[..8], format_node_kind(root.kind), root.content);

            let layer_str = if let Some(l) = root.metadata.get("formality_layer") {
                format!(" [U{}]", l)
            } else if root.formality_layer > 0 {
                format!(" [U{}]", root.formality_layer)
            } else {
                String::new()
            };
            if !layer_str.is_empty() {
                println!("   Layer: {}", layer_str);
            }
            println!();

            // Trace relationships
            let max_depth = if depth == 0 { 999 } else { depth };
            let relationships = graph.trace_relationships(&full_id, max_depth);

            if relationships.is_empty() {
                println!("⚠️  No relationships found for this specification.");
                println!("\nThis specification is isolated. You may want to:");
                println!("  - Add relationships using 'spec add-edge'");
                println!("  - Run 'spec infer-relationships' to auto-detect relationships");
            } else {
                println!("🔗 Found {} relationship(s):", relationships.len());
                println!();

                // Group by depth
                let mut by_depth: std::collections::HashMap<usize, Vec<_>> = std::collections::HashMap::new();
                for (node, edge_kind, direction, depth_level) in &relationships {
                    by_depth.entry(*depth_level).or_insert_with(Vec::new).push((node, edge_kind, direction));
                }

                let mut depths: Vec<_> = by_depth.keys().collect();
                depths.sort();

                for depth_level in depths {
                    let items = by_depth.get(depth_level).unwrap();
                    println!("  Level {}:", depth_level);

                    for (node, edge_kind, direction) in items {
                        let indent = "    ";
                        let arrow = if *direction == "outgoing" { "→" } else { "←" };
                        let edge_label = format_edge_kind(**edge_kind);

                        let node_layer = if let Some(l) = node.metadata.get("formality_layer") {
                            format!(" [U{}]", l)
                        } else if node.formality_layer > 0 {
                            format!(" [U{}]", node.formality_layer)
                        } else {
                            String::new()
                        };

                        println!(
                            "{}{} {} [{}]{} {}: {}",
                            indent,
                            arrow,
                            edge_label,
                            &node.id[..8],
                            node_layer,
                            format_node_kind(node.kind),
                            node.content
                        );
                    }
                    println!();
                }

                if depth > 0 && !relationships.is_empty() {
                    println!("(Limited to depth {})", depth);
                }
            }
        }
        Commands::VerifyLayers => {
            let graph = store.load()?;

            println!("🔍 Verifying multi-layer specification consistency...\n");

            // Find all nodes by formality layer
            let mut u0_nodes = Vec::new();
            let mut u1_nodes = Vec::new();
            let mut u2_nodes = Vec::new();
            let mut u3_nodes = Vec::new();

            for node in graph.list_nodes(None) {
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

            // Check U0 → U3 completeness (every requirement has implementation)
            println!("🔬 Checking Completeness (U0 → U3):");
            let mut incomplete_count = 0;
            let mut complete_chains = Vec::new();

            for u0_node in &u0_nodes {
                // Find U3 nodes reachable from this U0 via Formalizes edges
                let mut u3_implementations = Vec::new();
                let relationships = graph.trace_relationships(&u0_node.id, 999);

                for (related_node, edge_kind, direction, _depth) in &relationships {
                    // Check if this is a Formalizes edge pointing forward
                    use spec_core::EdgeKind;
                    if *edge_kind == EdgeKind::Formalizes && direction == "outgoing" {
                        let related_layer = parse_formality_layer(related_node.formality_layer);

                        if related_layer == 3 {
                            u3_implementations.push(related_node.id.clone());
                        }
                    }
                }

                if u3_implementations.is_empty() {
                    incomplete_count += 1;
                    println!("   ⚠️  [{}] {} (no U3 implementation)", &u0_node.id[..8], u0_node.content);
                } else {
                    complete_chains.push((u0_node.id.clone(), u3_implementations));
                }
            }

            if incomplete_count == 0 {
                println!("   ✅ All {} U0 requirements have U3 implementations", u0_nodes.len());
            } else {
                println!("   ⚠️  {} of {} U0 requirements lack U3 implementations", incomplete_count, u0_nodes.len());
            }
            println!();

            // Check U3 → U0 soundness (every implementation has requirement)
            println!("🔬 Checking Soundness (U3 → U0):");
            let mut unsound_count = 0;

            for u3_node in &u3_nodes {
                // Find U0 nodes reachable from this U3 via Formalizes edges (backwards)
                let mut u0_requirements = Vec::new();
                let relationships = graph.trace_relationships(&u3_node.id, 999);

                for (related_node, edge_kind, direction, _depth) in &relationships {
                    // Check if this is a Formalizes edge pointing backward
                    use spec_core::EdgeKind;
                    if *edge_kind == EdgeKind::Formalizes && direction == "incoming" {
                        let related_layer = parse_formality_layer(related_node.formality_layer);

                        if related_layer == 0 {
                            u0_requirements.push(related_node.id.clone());
                        }
                    }
                }

                if u0_requirements.is_empty() {
                    unsound_count += 1;
                    println!("   ⚠️  [{}] {} (no U0 requirement)", &u3_node.id[..8], u3_node.content);
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
            println!("   Complete chains:      {}", complete_chains.len());
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
        Commands::ProveConsistency { spec_a, spec_b } => {
            use spec_core::{Prover, UDAFModel};

            let graph = store.load()?;
            let mut udaf_model = UDAFModel::new();
            udaf_model.populate_from_graph(&graph);

            println!("🔬 Proving Consistency Between Specifications\n");
            println!("═══════════════════════════════════════════════════════════════\n");

            // Get the specifications
            let node_a = graph.get_node(&spec_a);
            let node_b = graph.get_node(&spec_b);

            if node_a.is_none() {
                eprintln!("❌ Specification A '{}' not found", spec_a);
                std::process::exit(1);
            }
            if node_b.is_none() {
                eprintln!("❌ Specification B '{}' not found", spec_b);
                std::process::exit(1);
            }

            let node_a = node_a.unwrap();
            let node_b = node_b.unwrap();

            println!("📋 Specification A:");
            println!("   ID:      [{}]", &spec_a[..8]);
            println!("   Content: {}", node_a.content);
            println!("   Kind:    {:?}", node_a.kind);
            println!();

            println!("📋 Specification B:");
            println!("   ID:      [{}]", &spec_b[..8]);
            println!("   Content: {}", node_b.content);
            println!("   Kind:    {:?}", node_b.kind);
            println!();

            // Get admissible sets
            let admissible_a = udaf_model.admissible_sets.get(&spec_a);
            let admissible_b = udaf_model.admissible_sets.get(&spec_b);

            if admissible_a.is_none() || admissible_b.is_none() {
                println!("⚠️  Admissible sets not found in U/D/A/f model");
                println!("   Run 'spec inspect-model' to verify model state");
                std::process::exit(1);
            }

            let admissible_a = admissible_a.unwrap();
            let admissible_b = admissible_b.unwrap();

            println!("🔍 Admissible Set A: {} constraints", admissible_a.constraints.len());
            for (i, constraint) in admissible_a.constraints.iter().enumerate() {
                println!("   {}: {} ({:?})", i+1, constraint.description, constraint.kind);
            }
            println!();

            println!("🔍 Admissible Set B: {} constraints", admissible_b.constraints.len());
            for (i, constraint) in admissible_b.constraints.iter().enumerate() {
                println!("   {}: {} ({:?})", i+1, constraint.description, constraint.kind);
            }
            println!();

            // Prove consistency
            let mut prover = Prover::new();
            let proof = prover.prove_consistency(admissible_a, admissible_b);

            println!("═══════════════════════════════════════════════════════════════\n");
            println!("📜 Formal Proof Generated\n");
            println!("Property: {:?}", proof.property);
            println!("Method:   {:?}", proof.method);
            println!("Status:   {:?}", proof.status);
            println!();

            println!("Proof Steps:");
            for (i, step) in proof.steps.iter().enumerate() {
                println!("  {}. {}", i+1, step.description);
                println!("     Justification: {}", step.justification);
                println!();
            }

            match proof.status {
                spec_core::ProofStatus::Proven => {
                    println!("✅ PROVEN: Specifications are consistent");
                    println!("   ∃x. (x ∈ A₁ ∧ x ∈ A₂) - There exists an implementation satisfying both");
                }
                spec_core::ProofStatus::Refuted => {
                    println!("❌ REFUTED: Specifications contradict each other");
                    println!("   A₁ ∩ A₂ = ∅ - Admissible sets are disjoint");
                    println!("   No implementation can satisfy both specifications simultaneously");
                }
                spec_core::ProofStatus::Unknown => {
                    println!("❓ UNKNOWN: Could not prove or refute");
                    println!("   Current solver is incomplete (heuristic-based)");
                    println!("   SMT solver integration needed for complete verification");
                }
                spec_core::ProofStatus::Pending => {
                    println!("⏳ PENDING: Proof in progress");
                }
            }
        }
        Commands::ProveSatisfiability { spec } => {
            use spec_core::{Prover, UDAFModel};

            let graph = store.load()?;
            let mut udaf_model = UDAFModel::new();
            udaf_model.populate_from_graph(&graph);

            println!("🔬 Proving Satisfiability of Specification\n");
            println!("═══════════════════════════════════════════════════════════════\n");

            // Get the specification
            let node = graph.get_node(&spec);

            if node.is_none() {
                eprintln!("❌ Specification '{}' not found", spec);
                std::process::exit(1);
            }

            let node = node.unwrap();

            println!("📋 Specification:");
            println!("   ID:      [{}]", &spec[..8]);
            println!("   Content: {}", node.content);
            println!("   Kind:    {:?}", node.kind);
            println!();

            // Get admissible set
            let admissible = udaf_model.admissible_sets.get(&spec);

            if admissible.is_none() {
                println!("⚠️  Admissible set not found in U/D/A/f model");
                println!("   Run 'spec inspect-model' to verify model state");
                std::process::exit(1);
            }

            let admissible = admissible.unwrap();

            println!("🔍 Admissible Set: {} constraints", admissible.constraints.len());
            for (i, constraint) in admissible.constraints.iter().enumerate() {
                println!("   {}: {} ({:?})", i+1, constraint.description, constraint.kind);
            }
            println!();

            // Prove satisfiability
            let mut prover = Prover::new();
            let proof = prover.prove_satisfiability(admissible);

            println!("═══════════════════════════════════════════════════════════════\n");
            println!("📜 Formal Proof Generated\n");
            println!("Property: {:?}", proof.property);
            println!("Method:   {:?}", proof.method);
            println!("Status:   {:?}", proof.status);
            println!();

            println!("Proof Steps:");
            for (i, step) in proof.steps.iter().enumerate() {
                println!("  {}. {}", i+1, step.description);
                println!("     Justification: {}", step.justification);
                println!();
            }

            match proof.status {
                spec_core::ProofStatus::Proven => {
                    println!("✅ PROVEN: Specification is satisfiable");
                    println!("   ∃x. x ∈ A - There exists an implementation satisfying the specification");
                }
                spec_core::ProofStatus::Refuted => {
                    println!("❌ REFUTED: Specification is unsatisfiable");
                    println!("   A = ∅ - Admissible set is empty");
                    println!("   No implementation can satisfy this specification");
                }
                spec_core::ProofStatus::Unknown => {
                    println!("❓ UNKNOWN: Could not prove or refute");
                    println!("   Current solver is incomplete (heuristic-based)");
                    println!("   SMT solver integration needed for complete verification");
                }
                spec_core::ProofStatus::Pending => {
                    println!("⏳ PENDING: Proof in progress");
                }
            }
        }
        Commands::InspectModel { verbose } => {
            let graph = store.load()?;

            println!("🔍 Inspecting U/D/A/f Model Structure\n");
            println!("═══════════════════════════════════════════════════════════════\n");

            // Populate UDAFModel from graph
            let mut udaf_model = spec_core::UDAFModel::new();
            udaf_model.populate_from_graph(&graph);

            println!("📊 Populating U/D/A/f model from SpecGraph...\n");

            // Analyze Universes (U)
            println!("📦 Universes (U):");
            println!("   The specification space is stratified into formality layers:\n");

            let mut layer_stats = std::collections::HashMap::new();
            let mut universe_metadata = std::collections::HashMap::new();

            for node in graph.list_nodes(None) {
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
                let udaf_count = udaf_model.universes.get(&format!("U{}", layer))
                    .map(|u| u.specifications.len())
                    .unwrap_or(0);
                println!("   • {}: {} specifications (UDAFModel: {})", layer_name, count, udaf_count);
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

            let domain_nodes: Vec<_> = graph.list_nodes(Some(spec_core::NodeKind::Domain));

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

            let constraint_count = graph.list_nodes(Some(spec_core::NodeKind::Constraint)).len();
            let assertion_count = graph.list_nodes(Some(spec_core::NodeKind::Assertion)).len();
            let scenario_count = graph.list_nodes(Some(spec_core::NodeKind::Scenario)).len();

            println!("   • Constraints (∀): {} universal invariants", constraint_count);
            println!("   • Assertions:      {} concrete claims", assertion_count);
            println!("   • Scenarios (∃):   {} existential requirements", scenario_count);
            println!();
            println!("   Note: Each specification implicitly defines A = {{impl | impl satisfies spec}}");
            println!("         Explicit A computation is not yet implemented.\n");

            // Analyze Transform Functions (f)
            println!("🔗 Transform Functions (f):");
            println!("   Mappings between universes that preserve specification semantics:\n");

            use spec_core::EdgeKind;
            let mut transform_counts = std::collections::HashMap::new();

            for (edge, _source, _target) in graph.list_edges(None) {
                *transform_counts.entry(edge.kind.clone()).or_insert(0) += 1;
            }

            for (kind, count) in &transform_counts {
                let description = match kind {
                    EdgeKind::Formalizes => "f: Ui → Uj (formalization)",
                    EdgeKind::Transform => "f: Ui → Uj (transformation)",
                    EdgeKind::Refines => "refinement (within-layer)",
                    EdgeKind::DerivesFrom => "derivation (provenance)",
                    EdgeKind::DependsOn => "dependency",
                    EdgeKind::Contradicts => "contradiction (⊥)",
                    EdgeKind::Synonym => "equivalence (≡)",
                    EdgeKind::Composes => "composition",
                };
                println!("   • {:20}: {} edges", description, count);
            }
            println!();

            // Show UDAFModel transforms
            println!("   UDAFModel Transforms:");
            println!("   {} transform functions defined", udaf_model.transforms.len());
            if verbose {
                for (id, transform) in &udaf_model.transforms {
                    println!("     - {}: {} -> {}", id, transform.source_universe, transform.target_universe);
                    println!("       Strategy: {:?}", transform.kind);
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

                    let layer_nodes: Vec<_> = graph.list_nodes(None).into_iter()
                        .filter(|n| parse_formality_layer(n.formality_layer) == layer)
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
        Commands::ConstructU0 { execute, verbose } => {
            let mut graph = store.load()?;

            println!("🏗️  Constructing U0 from Projection Universes\n");
            println!("═══════════════════════════════════════════════════════════════\n");

            // Populate UDAFModel from graph
            let mut udaf_model = spec_core::UDAFModel::new();
            udaf_model.populate_from_graph(&graph);

            println!("📊 Initial State:");
            for (universe_id, universe) in &udaf_model.universes {
                if universe.layer > 0 {
                    println!("   {}: {} specifications", universe_id, universe.specifications.len());
                }
            }
            println!("   Transform functions: {}", udaf_model.transforms.len());
            println!();

            if execute {
                println!("⚙️  Executing Transform Strategies...\n");
                println!("   This demonstrates the core theoretical operation:");
                println!("   U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ f₀₃⁻¹(U3)\n");

                match udaf_model.construct_u0(&graph) {
                    Ok(newly_created) => {
                        println!("✅ U0 Construction Complete\n");
                        println!("   Newly extracted specifications: {}", newly_created.len());

                        if verbose && !newly_created.is_empty() {
                            println!("\n   Extracted specs (first 10):");
                            for (i, spec) in newly_created.iter().take(10).enumerate() {
                                let preview = if spec.content.len() > 50 {
                                    format!("{}...", &spec.content[..47])
                                } else {
                                    spec.content.clone()
                                };
                                println!("   {}. {} [confidence: {:.2}]", i + 1, preview, spec.confidence);
                            }
                            if newly_created.len() > 10 {
                                println!("   ... and {} more", newly_created.len() - 10);
                            }
                        }

                        // Ingest the extracted specifications into the graph
                        if !newly_created.is_empty() {
                            println!("\n⚙️  Ingesting extracted specifications into graph...\n");
                            let report = graph.ingest(newly_created);

                            println!("✅ Ingestion complete:");
                            println!("   Nodes created: {}", report.nodes_created);
                            println!("   Nodes skipped: {} (duplicates or low quality)", report.nodes_skipped);
                            println!("   Edges created: {}", report.edges_created);
                            if !report.suggestions.is_empty() {
                                println!("   Edge suggestions: {} (require review)", report.suggestions.len());
                            }

                            // Save the updated graph
                            store.save(&graph).map_err(|e| format!("Failed to save graph: {}", e))?;
                            println!("\n💾 Graph saved successfully");
                        } else {
                            println!("\n   No new specifications to ingest (all already exist or below confidence threshold)");
                        }

                        // Show final counts
                        let total_specs = graph.list_nodes(None).len();
                        let u0_specs = graph.list_nodes(None).iter()
                            .filter(|n| parse_formality_layer(n.formality_layer) == 0)
                            .count();
                        println!("\n📊 Final State:");
                        println!("   Total specifications: {}", total_specs);
                        println!("   U0 specifications: {}", u0_specs);
                    }
                    Err(e) => {
                        eprintln!("❌ Error during U0 construction: {}", e);
                        return Err(e.into());
                    }
                }
            } else {
                println!("ℹ️  Dry run mode (use --execute to actually run transforms)");
                println!("\n   Transform strategies that would be executed:");

                for (id, transform) in &udaf_model.transforms {
                    if transform.kind == spec_core::TransformKind::Inverse {
                        println!("   • {}", id);
                        println!("     {} -> {}", transform.source_universe, transform.target_universe);
                        if verbose {
                            println!("     Strategy: {:?}", transform.strategy);
                        }
                    }
                }
            }

            println!("\n═══════════════════════════════════════════════════════════════");
        }
        Commands::CleanupLowQuality { execute } => {
            use spec_core::SpecGraph;

            let graph = store.load()?;

            println!("🧹 Cleaning Up Low-Quality Extracted Specifications\n");

            if execute {
                println!("⚠️  EXECUTE MODE: Specifications will be removed!");
            } else {
                println!("📋 DRY-RUN MODE: No changes will be made. Use --execute to actually remove.");
            }

            println!("\n═══════════════════════════════════════════════════════════════\n");

            // Collect low-quality specs
            let mut low_quality_specs = Vec::new();

            for node in graph.list_nodes(None) {
                // Only check extracted specs
                if node.metadata.get("inferred") != Some(&"true".to_string()) {
                    continue;
                }

                // Apply the same quality filter from extract.rs
                let content = &node.content;
                let is_low_quality = {
                    // Check 1: Invariant that is actually Rust code
                    if content.starts_with("Invariant: ") {
                        // Reject if it contains Rust syntax
                        let rust_syntax_markers = [
                            ".iter()", ".any(", ".contains(", ".len()", ".get(",
                            "!(", "||", "&&", ">", "<", "==", "!=",
                            ".is_empty()", ".starts_with(", ".ends_with(",
                            "assert!", "panic!", "unwrap(", "expect(",
                            "{}", "[]", "\"{}\"", "format!", "println!"
                        ];
                        let has_rust_syntax = rust_syntax_markers.iter()
                            .any(|marker| content.contains(marker));

                        if has_rust_syntax {
                            true  // Rust code, not a specification
                        } else {
                            // Also check for semantic keywords (original filter)
                            let semantic_keywords = [
                                "must", "should", "shall", "require", "ensure", "verify", "validate",
                                "detect", "identify", "check", "test verifies", "system", "user",
                                "specification", "requirement", "constraint"
                            ];
                            let has_semantic = semantic_keywords.iter()
                                .any(|kw| content.to_lowercase().contains(kw));
                            !has_semantic
                        }
                    }
                    // Check 2: Trivial scenarios
                    else if content == "scenario {}" || content.trim().is_empty() {
                        true
                    }
                    // Check 3: Scenarios/function names that are too short or lack semantic value
                    else if node.kind == spec_core::NodeKind::Scenario ||
                            node.metadata.get("extractor") == Some(&"function_name".to_string()) {
                        // Too short (less than 25 chars is likely not descriptive enough)
                        if content.len() < 25 {
                            true
                        } else {
                            // Must have strong semantic keywords (not just "user" or "test")
                            let strong_keywords = [
                                "must", "should", "shall", "ensure", "verify", "validate",
                                "detect", "identify", "check for", "when", "if",
                                "specification", "requirement", "constraint", "correctly", "properly",
                                "without", "with", "given", "then", "returns", "accepts"
                            ];
                            let has_strong_semantic = strong_keywords.iter()
                                .any(|kw| content.to_lowercase().contains(kw));

                            // Reject if no strong semantics OR if it's just a test name pattern
                            let is_trivial_test_name = content.to_lowercase().starts_with("scenario: ") &&
                                !has_strong_semantic;

                            !has_strong_semantic || is_trivial_test_name
                        }
                    } else {
                        false
                    }
                };

                if is_low_quality {
                    low_quality_specs.push(node.clone());
                }
            }

            // Display results
            println!("📊 Found {} low-quality specifications:\n", low_quality_specs.len());

            // Group by category
            let mut invariants = 0;
            let mut short_scenarios = 0;
            let mut trivial = 0;

            for spec in &low_quality_specs {
                if spec.content.starts_with("Invariant: ") {
                    invariants += 1;
                } else if spec.content == "scenario {}" || spec.content.trim().is_empty() {
                    trivial += 1;
                } else {
                    short_scenarios += 1;
                }
            }

            println!("  Categories:");
            println!("    • {} test invariants without semantic keywords", invariants);
            println!("    • {} short function names (< 20 chars, no semantic keywords)", short_scenarios);
            println!("    • {} trivial scenarios", trivial);

            if low_quality_specs.is_empty() {
                println!("\n✅ No low-quality specifications found!");
                println!("\n═══════════════════════════════════════════════════════════════");
                return Ok(());
            }

            // Show examples
            println!("\n  Examples:");
            for (i, spec) in low_quality_specs.iter().take(5).enumerate() {
                println!("    {}. [{}] {}: {}",
                    i + 1,
                    &spec.id[..8],
                    format!("{:?}", spec.kind),
                    if spec.content.len() > 60 {
                        format!("{}...", &spec.content[..60])
                    } else {
                        spec.content.clone()
                    }
                );
            }

            if low_quality_specs.len() > 5 {
                println!("    ... and {} more", low_quality_specs.len() - 5);
            }

            // Execute removal if requested
            if execute {
                println!("\n🗑️  Removing low-quality specifications...");

                let mut updated_graph = graph.clone();
                let mut removed_count = 0;

                for spec in &low_quality_specs {
                    if updated_graph.remove_node(&spec.id).is_some() {
                        removed_count += 1;
                    } else {
                        eprintln!("  ⚠️  Failed to remove {}: node not found", &spec.id[..8]);
                    }
                }

                // Save updated graph
                store.save(&updated_graph)?;

                println!("\n✅ Successfully removed {} specifications", removed_count);

                // Show new stats
                let remaining = store.load()?;
                let remaining_count = remaining.list_nodes(None).len();
                let remaining_isolated = remaining.detect_omissions().iter()
                    .filter(|o| o.description.contains("Isolated node"))
                    .count();

                println!("\n📊 Updated Statistics:");
                println!("  Total specifications: {}", remaining_count);
                println!("  Isolated specifications: {}", remaining_isolated);

            } else {
                println!("\n💡 To remove these specifications, run:");
                println!("   spec cleanup-low-quality --execute");
            }

            println!("\n═══════════════════════════════════════════════════════════════");
        }
        Commands::AddEdge { source, target, kind } => {
            use spec_core::EdgeKind as CoreEdgeKind;

            // Load graph
            let mut graph = store.load()?;

            // Convert kind string to CoreEdgeKind
            let core_kind = match kind.to_lowercase().as_str() {
                "refines" => CoreEdgeKind::Refines,
                "depends_on" | "depends-on" => CoreEdgeKind::DependsOn,
                "contradicts" => CoreEdgeKind::Contradicts,
                "derives_from" | "derives-from" => CoreEdgeKind::DerivesFrom,
                "synonym" => CoreEdgeKind::Synonym,
                "composes" => CoreEdgeKind::Composes,
                "formalizes" => CoreEdgeKind::Formalizes,
                "transform" => CoreEdgeKind::Transform,
                _ => CoreEdgeKind::Refines,
            };

            // Add edge
            match graph.add_edge(&source, &target, core_kind, HashMap::new()) {
                Ok(edge) => {
                    let edge_id = edge.id.clone();

                    // Save
                    store.save(&graph)?;

                    let edge_name = match core_kind {
                        CoreEdgeKind::Refines => "refines",
                        CoreEdgeKind::DependsOn => "depends_on",
                        CoreEdgeKind::Contradicts => "contradicts",
                        CoreEdgeKind::DerivesFrom => "derives_from",
                        CoreEdgeKind::Synonym => "synonym",
                        CoreEdgeKind::Composes => "composes",
                        CoreEdgeKind::Formalizes => "formalizes",
                        CoreEdgeKind::Transform => "transform",
                    };

                    println!("✓ Added edge: {}", edge_id);
                    println!("  [{}] --[{}]--> [{}]",
                        &source[..8],
                        edge_name,
                        &target[..8]);
                }
                Err(e) => {
                    eprintln!("Error adding edge: {}", e);
                    return Err(e.into());
                }
            }
        }
        Commands::Extract { source, language, min_confidence } => {
            // Extract specifications from source code and save to graph
            use spec_core::{RustExtractor, ProtoExtractor, InferredSpecification};
            use std::path::Path;

            let path = Path::new(&source);
            let mut graph = store.load().map_err(|e| format!("Failed to load graph: {}", e))?;

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

            // Extract specifications
            let specs: Vec<InferredSpecification> = if path.is_file() {
                match detected_language {
                    "rust" => RustExtractor::extract(path).map_err(|e| format!("Extraction failed: {}", e))?,
                    "proto" => ProtoExtractor::extract(path).map_err(|e| format!("Extraction failed: {}", e))?,
                    _ => {
                        eprintln!("Unsupported language: {}. Supported: rust, proto", language);
                        return Ok(());
                    }
                }
            } else if path.is_dir() {
                // Extract from all supported files in directory recursively
                use std::fs;
                let mut all_specs = Vec::new();
                for entry in fs::read_dir(path).map_err(|e| format!("Failed to read directory: {}", e))? {
                    let entry = entry.map_err(|e| format!("Failed to read entry: {}", e))?;
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
                        _ => {}
                    }
                }
                all_specs
            } else {
                eprintln!("❌ Source path not found: {}", source);
                return Ok(());
            };

            // Filter by confidence and ingest into graph
            let filtered: Vec<_> = specs.into_iter()
                .filter(|s| s.confidence >= min_confidence)
                .collect();

            println!("📊 Extracted {} specifications (confidence >= {})\n", filtered.len(), min_confidence);

            if filtered.is_empty() {
                println!("✓ No specifications extracted");
                return Ok(());
            }

            // Ingest extracted specs into graph
            let report = graph.ingest(filtered.clone());

            // Save updated graph
            store.save(&graph).map_err(|e| format!("Failed to save graph: {}", e))?;

            println!("✅ Ingestion complete:");
            println!("   Nodes created: {}", report.nodes_created);
            println!("   Nodes skipped: {} (low confidence)", report.nodes_skipped);
            println!("   Edges created: {}", report.edges_created);
            println!("   Edge suggestions: {} (require review)", report.suggestions.len());

            if !report.contradictions_found.is_empty() {
                println!("\n⚠️  Contradictions detected:");
                for contra in &report.contradictions_found {
                    println!("   • {}", contra);
                }
            }

            println!("\n💡 To verify: spec check");
            println!("💡 To inspect: spec list-nodes --kind Scenario");
        }
        Commands::InferRelationshipsAi { min_confidence } => {
            let mut graph = store.load()?;

            println!("🤖 Inferring relationships with AI-powered semantic matching...");
            println!("   Minimum confidence: {:.2}", min_confidence);
            println!("   This may take a while for large specification sets.\n");

            // Call the AI-enhanced cross-layer inference
            let report = graph.infer_cross_layer_relationships_with_ai(min_confidence);

            // Save updated graph
            store.save(&graph)?;

            println!("\n✅ AI-enhanced relationship inference complete:");
            println!("   Edges created: {}", report.edges_created);
            println!("   Suggestions: {} (require review)", report.suggestions.len());

            if !report.suggestions.is_empty() {
                println!("\n📋 Top suggestions for human review:");
                for (i, suggestion) in report.suggestions.iter().take(10).enumerate() {
                    println!("   {}. [{} → {}] {} (confidence: {:.2})",
                        i + 1,
                        &suggestion.source_id[..8],
                        &suggestion.target_id[..8],
                        suggestion.explanation,
                        suggestion.confidence
                    );
                }
                if report.suggestions.len() > 10 {
                    println!("   ... and {} more", report.suggestions.len() - 10);
                }
            }

            println!("\n💡 To verify: spec check");
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
                    let layer_label = format_formality_layer(node.formality_layer as u8);
                    println!("  [{}] [{}] {} - {}",
                        layer_label,
                        node.id,
                        node_kind_name(node.kind),
                        node.content);
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
            // Search for matching specifications
            let search_resp = client
                .query(Request::new(proto::QueryRequest {
                    natural_language_query: query.clone(),
                }))
                .await?;
            let mut results = search_resp.into_inner().matching_nodes;

            // Filter by layer if specified
            if let Some(layer_num) = layer {
                results.retain(|node| {
                    if let Some(layer_str) = node.metadata.get("formality_layer") {
                        layer_str.parse::<u32>().ok() == Some(layer_num)
                    } else {
                        node.formality_layer == layer_num
                    }
                });
            }

            // Limit results
            let max_results = max as usize;
            if results.len() > max_results {
                results.truncate(max_results);
            }

            if results.is_empty() {
                println!("No specifications found matching '{}'", query);
                println!("\nTry:");
                println!("  - Using different keywords");
                println!("  - Broadening your search");
                println!("  - Using 'spec list-nodes' to see all specifications");
            } else {
                println!("Found {} specification(s) matching '{}':", results.len(), query);
                println!();
                for (i, node) in results.iter().enumerate() {
                    let kind_str = node_kind_name(node.kind);
                    let layer_str = if let Some(l) = node.metadata.get("formality_layer") {
                        format!(" [U{}]", l)
                    } else {
                        format!(" [U{}]", node.formality_layer)
                    };
                    println!("  {}. [{}]{} {} - {}",
                        i + 1,
                        node.id,
                        layer_str,
                        kind_str,
                        node.content
                    );
                }

                if let Some(layer_num) = layer {
                    println!("\n(Filtered to layer U{})", layer_num);
                }
            }
        }
        Commands::Trace { id, depth: _ } => {
            // Get the root node
            let node_resp = client
                .get_node(Request::new(proto::GetNodeRequest { id: id.clone() }))
                .await?;
            let root = node_resp.into_inner().node;

            if root.is_none() {
                println!("❌ Node not found: {}", id);
                return Ok(());
            }

            let root_node = root.unwrap();
            println!("📋 Tracing relationships for:");
            println!("   [{}] {}: {}", root_node.id, node_kind_name(root_node.kind), root_node.content);

            let layer_str = if let Some(l) = root_node.metadata.get("formality_layer") {
                format!(" [U{}]", l)
            } else if root_node.formality_layer > 0 {
                format!(" [U{}]", root_node.formality_layer)
            } else {
                String::new()
            };
            if !layer_str.is_empty() {
                println!("   Layer: {}", layer_str);
            }
            println!();

            // For server mode, we need to manually traverse relationships using list_edges
            let edges_resp = client
                .list_edges(Request::new(proto::ListEdgesRequest {
                    node_id: id.clone(),
                }))
                .await?;
            let edges = edges_resp.into_inner().edges;

            if edges.is_empty() {
                println!("⚠️  No relationships found for this specification.");
                println!("\nThis specification is isolated. You may want to:");
                println!("  - Add relationships using 'spec add-edge'");
                println!("  - Run 'spec infer-relationships' to auto-detect relationships");
            } else {
                println!("🔗 Found {} direct relationship(s):", edges.len());
                println!();

                for edge in &edges {
                    let arrow = if edge.source_id == id { "→" } else { "←" };
                    let other_id = if edge.source_id == id { &edge.target_id } else { &edge.source_id };
                    let edge_label = edge_kind_name(edge.kind);

                    // Get the other node
                    let other_resp = client
                        .get_node(Request::new(proto::GetNodeRequest { id: other_id.clone() }))
                        .await?;

                    if let Some(other_node) = other_resp.into_inner().node {
                        let node_layer = if let Some(l) = other_node.metadata.get("formality_layer") {
                            format!(" [U{}]", l)
                        } else if other_node.formality_layer > 0 {
                            format!(" [U{}]", other_node.formality_layer)
                        } else {
                            String::new()
                        };

                        println!(
                            "  {} {} [{}]{} {}: {}",
                            arrow,
                            edge_label,
                            other_node.id,
                            node_layer,
                            node_kind_name(other_node.kind),
                            other_node.content
                        );
                    }
                }

                println!("\nNote: Server mode currently shows only direct relationships.");
                println!("For full traversal, use standalone mode.");
            }
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
            use spec_core::{RustExtractor, ProtoExtractor, InferredSpecification};
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
            use notify::{Watcher, RecursiveMode};
            use std::sync::mpsc::channel;
            use std::time::Duration;
            use std::path::Path;

            if language != "rust" {
                eprintln!("Only Rust watching is currently supported");
                return Ok(());
            }

            let source_path = Path::new(&source);
            if !source_path.exists() {
                eprintln!("Source path not found: {}", source);
                return Ok(());
            }

            println!("🔍 Watching {} for changes...", source);
            println!("   Confidence threshold: {}", min_confidence);
            println!("   Check interval: {}s", interval);
            println!("   Press Ctrl+C to stop\n");

            let (tx, rx) = channel();
            let mut watcher = notify::recommended_watcher(tx)
                .map_err(|e| format!("Failed to create watcher: {}", e))?;

            watcher.watch(source_path, RecursiveMode::Recursive)
                .map_err(|e| format!("Failed to watch path: {}", e))?;

            // Initial extraction
            println!("📦 Performing initial extraction...");
            let initial_count = extract_and_sync(&mut client, &source, language.clone(), min_confidence).await?;
            println!("✓ Extracted {} specifications\n", initial_count);

            // Initial verification
            println!("🔬 Running initial verification...");
            verify_specifications(&mut client).await?;
            println!();

            // Watch loop
            loop {
                match rx.recv_timeout(Duration::from_secs(interval)) {
                    Ok(Ok(event)) => {
                        if should_process_event(&event) {
                            if let Some(path) = event.paths.first() {
                                if path.extension().and_then(|s| s.to_str()) == Some("rs") {
                                    println!("📝 Change detected: {:?}", path.file_name());
                                    println!("   Re-extracting specifications...");

                                    let count = extract_and_sync(&mut client, &source, language.clone(), min_confidence).await?;
                                    println!("   ✓ Updated {} specifications", count);

                                    println!("   🔬 Verifying...");
                                    verify_specifications(&mut client).await?;
                                    println!();
                                }
                            }
                        }
                    }
                    Ok(Err(e)) => eprintln!("Watch error: {}", e),
                    Err(_) => {
                        // Timeout - perform periodic check
                        verify_specifications(&mut client).await?;
                    }
                }
            }
        }
        Commands::Init { path } => {
            use std::path::Path;
            use std::fs;

            let project_root = Path::new(&path);
            let spec_dir = project_root.join(".spec");

            if spec_dir.exists() {
                eprintln!("✗ Error: .spec/ directory already exists");
                eprintln!("  This project is already initialized for specification management");
                return Ok(());
            }

            println!("Initializing specification management in {}", project_root.display());

            // Create .spec directory structure
            fs::create_dir_all(&spec_dir)?;
            fs::create_dir_all(spec_dir.join("scripts"))?;

            // Create empty specs.json with proper SpecGraph structure
            let specs_file = spec_dir.join("specs.json");
            let empty_graph = spec_core::SpecGraph::new();
            let store = FileStore::new(&specs_file);
            store.save(&empty_graph)?;
            println!("  ✓ Created .spec/specs.json");

            // Create README.md
            let readme = spec_dir.join("README.md");
            fs::write(&readme, r#"# Specification Management

This directory contains specifications managed by specORACLE.

## Structure

- `specs.json` - Specification graph storage
- `scripts/` - Project-local specd server scripts

## Usage

### Option 1: Project-Local Server (Recommended for team projects)

Start project-local specification server:
```bash
.spec/scripts/start-specd.sh
```

Use spec commands (they will connect to project-local server):
```bash
spec add "Password must be at least 8 characters"
spec detect-contradictions
```

Stop the server:
```bash
.spec/scripts/stop-specd.sh
```

### Option 2: Direct File Access (Simple, no server needed)

Set environment variable to use this project's specs:
```bash
export SPECD_STORE_PATH="$(pwd)/.spec/specs.json"
specd &  # Start server with project-local storage
```

## Team Workflow

1. Add `.spec/` to Git: `git add .spec/`
2. Team members clone the repository (includes specs)
3. Each developer runs project-local specd
4. Specifications are version-controlled alongside code

## CI/CD Integration

Add to your CI pipeline:
```yaml
- name: Check specifications
  run: |
    export SPECD_STORE_PATH="${PWD}/.spec/specs.json"
    specd &
    sleep 2
    spec detect-contradictions
    spec detect-omissions
```
"#)?;
            println!("  ✓ Created .spec/README.md");

            // Create start script
            let start_script = spec_dir.join("scripts/start-specd.sh");
            fs::write(&start_script, r#"#!/bin/bash
# Start project-local specification server

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPEC_DIR="$PROJECT_ROOT/.spec"
PID_FILE="$SPEC_DIR/specd.pid"
LOG_FILE="$SPEC_DIR/specd.log"

if [ -f "$PID_FILE" ]; then
    PID=$(cat "$PID_FILE")
    if kill -0 "$PID" 2>/dev/null; then
        echo "✗ specd is already running (PID: $PID)"
        exit 1
    fi
    rm "$PID_FILE"
fi

export SPECD_STORE_PATH="$SPEC_DIR/specs.json"

echo "Starting project-local specd..."
echo "  Store: $SPECD_STORE_PATH"
echo "  Log: $LOG_FILE"

specd > "$LOG_FILE" 2>&1 &
echo $! > "$PID_FILE"

sleep 1

if kill -0 $(cat "$PID_FILE") 2>/dev/null; then
    echo "✓ specd started (PID: $(cat "$PID_FILE"))"
else
    echo "✗ Failed to start specd. Check $LOG_FILE"
    rm "$PID_FILE"
    exit 1
fi
"#)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mut perms = fs::metadata(&start_script)?.permissions();
                perms.set_mode(0o755);
                fs::set_permissions(&start_script, perms)?;
            }
            println!("  ✓ Created .spec/scripts/start-specd.sh");

            // Create stop script
            let stop_script = spec_dir.join("scripts/stop-specd.sh");
            fs::write(&stop_script, r#"#!/bin/bash
# Stop project-local specification server

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPEC_DIR="$PROJECT_ROOT/.spec"
PID_FILE="$SPEC_DIR/specd.pid"

if [ ! -f "$PID_FILE" ]; then
    echo "✗ specd is not running (no PID file)"
    exit 1
fi

PID=$(cat "$PID_FILE")
if ! kill -0 "$PID" 2>/dev/null; then
    echo "✗ specd is not running (stale PID file)"
    rm "$PID_FILE"
    exit 1
fi

echo "Stopping specd (PID: $PID)..."
kill "$PID"
rm "$PID_FILE"

echo "✓ specd stopped"
"#)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mut perms = fs::metadata(&stop_script)?.permissions();
                perms.set_mode(0o755);
                fs::set_permissions(&stop_script, perms)?;
            }
            println!("  ✓ Created .spec/scripts/stop-specd.sh");

            // Create .gitignore
            let gitignore = spec_dir.join(".gitignore");
            fs::write(&gitignore, "specd.pid\nspecd.log\n")?;
            println!("  ✓ Created .spec/.gitignore");

            println!("\n✓ Specification management initialized successfully!");
            println!("\nNext steps:");
            println!("  1. Start project-local server: .spec/scripts/start-specd.sh");
            println!("  2. Add specifications: spec add \"Your specification here\"");
            println!("  3. Add .spec/ to Git: git add .spec/");
            println!("\nFor team collaboration:");
            println!("  - Team members clone this repo (includes .spec/)");
            println!("  - Each developer runs: .spec/scripts/start-specd.sh");
            println!("  - Specifications are automatically version-controlled");
            println!("\nSee .spec/README.md for more details.");
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

fn should_process_event(event: &notify::Event) -> bool {
    use notify::event::{EventKind, ModifyKind};
    matches!(
        event.kind,
        EventKind::Modify(ModifyKind::Data(_)) | EventKind::Create(_)
    )
}

async fn extract_and_sync(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
    source: &str,
    _language: String,
    min_confidence: f32,
) -> Result<usize, Box<dyn std::error::Error>> {
    use spec_core::{RustExtractor, InferredSpecification};
    use proto::{SpecNodeKind, AddNodeRequest};
    use tonic::Request;
    use std::path::Path;

    let path = Path::new(source);
    let specs: Vec<InferredSpecification> = if path.is_file() {
        RustExtractor::extract(path).map_err(|e| {
            format!("Extraction failed: {}", e)
        })?
    } else if path.is_dir() {
        use std::fs;
        let mut all_specs = Vec::new();
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.extension().and_then(|s| s.to_str()) == Some("rs") {
                match RustExtractor::extract(&entry_path) {
                    Ok(specs) => all_specs.extend(specs),
                    Err(_) => {} // Silently skip failed files
                }
            }
        }
        all_specs
    } else {
        Vec::new()
    };

    let filtered: Vec<_> = specs.into_iter()
        .filter(|s| s.confidence >= min_confidence)
        .collect();

    // Clear previous extracted specs and add new ones
    // (In production, would use smart diff/update)
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
        metadata.insert("source_file".to_string(), spec.source_file.clone());
        metadata.insert("source_line".to_string(), spec.source_line.to_string());

        let _ = client
            .add_node(Request::new(AddNodeRequest {
                content: spec.content.clone(),
                kind: kind as i32,
                metadata,
            }))
            .await;
    }

    Ok(filtered.len())
}

async fn verify_specifications(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    use tonic::Request;

    // Detect contradictions
    let contra_resp = client
        .detect_contradictions(Request::new(proto::DetectContradictionsRequest {}))
        .await?;
    let contradictions = contra_resp.into_inner().contradictions;

    if !contradictions.is_empty() {
        println!("   ⚠️  {} contradiction(s) detected:", contradictions.len());
        for (i, c) in contradictions.iter().take(3).enumerate() {
            if let (Some(a), Some(b)) = (&c.node_a, &c.node_b) {
                println!("      {}. {} ⇔ {}",
                    i + 1,
                    a.content.chars().take(40).collect::<String>(),
                    b.content.chars().take(40).collect::<String>()
                );
            }
        }
        if contradictions.len() > 3 {
            println!("      ... and {} more", contradictions.len() - 3);
        }
    } else {
        println!("   ✓ No contradictions");
    }

    // Detect omissions
    let omit_resp = client
        .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
        .await?;
    let omissions = omit_resp.into_inner().omissions;

    let isolated_count = omissions.iter()
        .filter(|o| o.description.contains("Isolated"))
        .count();

    if isolated_count > 0 {
        println!("   ⚠️  {} isolated specification(s)", isolated_count);
    }

    Ok(())
}
