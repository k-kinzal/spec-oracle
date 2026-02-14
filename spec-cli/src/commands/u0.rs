/// U0 construction and cleanup commands
///
/// This module implements commands related to U0 (root specification) construction
/// and quality management of extracted specifications.

use spec_core::{FileStore, UDAFModel, NodeKind};
use crate::utils::parse_formality_layer;

/// Execute ConstructU0 command in standalone mode
pub fn execute_construct_u0_standalone(
    store: &mut FileStore,
    execute: bool,
    verbose: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut graph = store.load()?;

    println!("🏗️  Constructing U0 from Projection Universes\n");
    println!("═══════════════════════════════════════════════════════════════\n");

    // Populate UDAFModel from graph
    let mut udaf_model = UDAFModel::new();
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

    Ok(())
}

/// Execute CleanupLowQuality command in standalone mode
pub fn execute_cleanup_low_quality_standalone(
    store: &mut FileStore,
    execute: bool,
) -> Result<(), Box<dyn std::error::Error>> {
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
            else if node.kind == NodeKind::Scenario ||
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

    Ok(())
}
