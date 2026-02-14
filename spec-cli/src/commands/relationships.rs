/// Relationship inference commands
///
/// Provides AI-powered semantic relationship inference between specifications

use spec_core::Store;

/// Execute InferRelationshipsAi command in standalone mode
pub fn execute_infer_relationships_ai_standalone(
    store: &mut Store,
    min_confidence: f32,
) -> Result<(), Box<dyn std::error::Error>> {
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
    Ok(())
}
