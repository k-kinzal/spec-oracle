/// Extract command: Extract specifications from source code
///
/// This command implements the reverse mapping engine (f₀ᵢ⁻¹),
/// extracting specifications from code, proto, and documentation.

use spec_core::{FileStore, RustExtractor, ProtoExtractor, DocExtractor, ArchitectureExtractor, PHPTestExtractor, InferredSpecification};
use std::path::Path;

/// Execute the Extract command in standalone mode
pub fn execute_extract_standalone(
    store: &mut FileStore,
    source: String,
    language: String,
    min_confidence: f32,
) -> Result<(), Box<dyn std::error::Error>> {
    let path = Path::new(&source);
    let mut graph = store.load().map_err(|e| format!("Failed to load graph: {}", e))?;

    println!("🔍 Extracting specifications from: {}\n", source);

    // Detect language from file extension if not specified
    let detected_language = if path.is_file() {
        match path.extension().and_then(|s| s.to_str()) {
            Some("rs") => if language == "architecture" { "architecture" } else { "rust" },
            Some("proto") => "proto",
            Some("md") => "markdown",
            Some("php") => "php",
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
            "markdown" => DocExtractor::extract(path).map_err(|e| format!("Extraction failed: {}", e))?,
            "php" => PHPTestExtractor::extract(path).map_err(|e| format!("Extraction failed: {}", e))?,
            "architecture" => ArchitectureExtractor::extract(path).map_err(|e| format!("Extraction failed: {}", e))?,
            _ => {
                eprintln!("Unsupported language: {}. Supported: rust, proto, markdown, php, architecture", language);
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
                Some("md") if detected_language == "markdown" || detected_language == "auto" => {
                    match DocExtractor::extract(&entry_path) {
                        Ok(specs) => all_specs.extend(specs),
                        Err(e) => eprintln!("⚠️  Failed to extract from {:?}: {}", entry_path, e),
                    }
                }
                Some("php") if detected_language == "php" || detected_language == "auto" => {
                    match PHPTestExtractor::extract(&entry_path) {
                        Ok(specs) => all_specs.extend(specs),
                        Err(e) => eprintln!("⚠️  Failed to extract from {:?}: {}", entry_path, e),
                    }
                }
                Some("rs") if detected_language == "architecture" => {
                    match ArchitectureExtractor::extract(&entry_path) {
                        Ok(specs) => all_specs.extend(specs),
                        Err(e) => eprintln!("⚠️  Failed to extract architecture from {:?}: {}", entry_path, e),
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
    Ok(())
}
