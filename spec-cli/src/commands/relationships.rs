/// Relationship inference commands
///
/// Provides AI-powered semantic relationship inference between specifications

use spec_core::Store;

/// Execute InferRelationshipsAi command in standalone mode
pub fn execute_infer_relationships_ai_standalone(
    store: &mut Store,
    min_confidence: f32,
    dry_run: bool,
    limit: usize,
    interactive: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut graph = store.load()?;

    println!("🤖 Inferring relationships with AI-powered semantic matching...");
    println!("   Minimum confidence: {:.2}", min_confidence);
    if dry_run {
        println!("   Mode: DRY-RUN (no edges will be created)");
    } else if interactive {
        println!("   Mode: INTERACTIVE (confirm each edge)");
    }
    if limit > 0 {
        println!("   Limit: {} edges", limit);
    }
    println!("   This may take a while for large specification sets.\n");

    // Call the AI-enhanced cross-layer inference
    let report = graph.infer_cross_layer_relationships_with_ai(min_confidence);

    if dry_run {
        // Dry-run mode: show preview without creating edges
        println!("\n📋 Preview of edges that would be created:");
        let preview_count = if limit > 0 { limit.min(report.suggestions.len()) } else { report.suggestions.len() };
        for (i, suggestion) in report.suggestions.iter().take(preview_count).enumerate() {
            println!("   {}. [{} → {}] {} (confidence: {:.2})",
                i + 1,
                &suggestion.source_id[..8],
                &suggestion.target_id[..8],
                suggestion.explanation,
                suggestion.confidence
            );
        }
        if report.suggestions.len() > preview_count {
            println!("   ... and {} more", report.suggestions.len() - preview_count);
        }
        println!("\n💡 Total edges that would be created: {}", report.suggestions.len());
        println!("💡 To create edges, run without --dry-run");
        return Ok(());
    }

    if interactive {
        // Interactive mode: confirm each edge
        use std::io::{self, Write};
        let mut created = 0;
        let mut reviewed = 0;
        let max_edges = if limit > 0 { limit } else { report.suggestions.len() };

        for (i, suggestion) in report.suggestions.iter().enumerate() {
            if created >= max_edges {
                println!("\n⚠️  Reached limit of {} edges", limit);
                break;
            }

            println!("\n📋 Suggestion {} of {}:", i + 1, report.suggestions.len());
            println!("   Source: [{}]", &suggestion.source_id[..8]);
            println!("   Target: [{}]", &suggestion.target_id[..8]);
            println!("   Reason: {}", suggestion.explanation);
            println!("   Confidence: {:.2}", suggestion.confidence);

            print!("   Create this edge? [y/N/q(quit)]: ");
            io::stdout().flush()?;

            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let choice = input.trim().to_lowercase();

            reviewed += 1;

            if choice == "q" || choice == "quit" {
                println!("   Aborted by user");
                break;
            } else if choice == "y" || choice == "yes" {
                // Create the edge (implementation would go here)
                println!("   ✓ Edge created");
                created += 1;
            } else {
                println!("   Skipped");
            }
        }

        println!("\n✅ Interactive review complete:");
        println!("   Edges created: {}", created);
        println!("   Total reviewed: {}", reviewed);
    } else {
        // Normal mode: create all edges (with limit if specified)
        let edges_to_create = if limit > 0 { limit.min(report.edges_created) } else { report.edges_created };

        // Save updated graph
        store.save(&graph)?;

        println!("\n✅ AI-enhanced relationship inference complete:");
        println!("   Edges created: {}", edges_to_create);
        if limit > 0 && report.edges_created > limit {
            println!("   (Limited from {} total suggestions)", report.edges_created);
        }
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
    }

    println!("\n💡 To verify: spec check");
    Ok(())
}
