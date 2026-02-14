/// File watching and synchronization commands
///
/// Continuously monitors source files and automatically extracts/verifies specifications

use crate::proto::spec_oracle_client::SpecOracleClient;
use notify::{Event, Watcher, RecursiveMode};
use std::sync::mpsc::channel;
use std::time::Duration;
use std::path::Path;
use tonic::Request;

/// Execute Watch command in server mode
pub async fn execute_watch_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    source: String,
    language: String,
    min_confidence: f32,
    interval: u64,
) -> Result<(), Box<dyn std::error::Error>> {
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
    let initial_count = extract_and_sync(client, &source, language.clone(), min_confidence).await?;
    println!("✓ Extracted {} specifications\n", initial_count);

    // Initial verification
    println!("🔬 Running initial verification...");
    verify_specifications(client).await?;
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

                            let count = extract_and_sync(client, &source, language.clone(), min_confidence).await?;
                            println!("   ✓ Updated {} specifications", count);

                            println!("   🔬 Verifying...");
                            verify_specifications(client).await?;
                            println!();
                        }
                    }
                }
            }
            Ok(Err(e)) => eprintln!("Watch error: {}", e),
            Err(_) => {
                // Timeout - perform periodic check
                verify_specifications(client).await?;
            }
        }
    }
}

/// Helper: Extract specifications and sync with server
async fn extract_and_sync(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    source: &str,
    _language: String,
    min_confidence: f32,
) -> Result<usize, Box<dyn std::error::Error>> {
    use spec_core::RustExtractor;
    use std::path::Path;

    // Extract from source
    let path = Path::new(source);
    let specs = if path.is_file() {
        RustExtractor::extract(path)?
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

    // Filter by confidence
    let filtered: Vec<_> = specs.into_iter()
        .filter(|s| s.confidence >= min_confidence)
        .collect();

    let count = filtered.len();

    // Ingest into server
    for spec in filtered {
        use spec_core::NodeKind;
        let kind = match spec.kind {
            NodeKind::Assertion => crate::proto::SpecNodeKind::Assertion,
            NodeKind::Constraint => crate::proto::SpecNodeKind::Constraint,
            NodeKind::Scenario => crate::proto::SpecNodeKind::Scenario,
            NodeKind::Definition => crate::proto::SpecNodeKind::Definition,
            NodeKind::Domain => crate::proto::SpecNodeKind::Domain,
        };

        let mut metadata = spec.metadata.clone();
        metadata.insert("confidence".to_string(), spec.confidence.to_string());
        metadata.insert("extracted".to_string(), "true".to_string());
        metadata.insert("source_file".to_string(), spec.source_file.clone());
        metadata.insert("source_line".to_string(), spec.source_line.to_string());

        let _ = client.add_node(Request::new(crate::proto::AddNodeRequest {
            content: spec.content,
            kind: kind as i32,
            metadata,
        })).await;
    }

    Ok(count)
}

/// Helper: Verify specifications
async fn verify_specifications(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Run contradiction detection
    let resp = client.detect_contradictions(Request::new(crate::proto::DetectContradictionsRequest {})).await?;
    let contradictions = resp.into_inner().contradictions;

    if contradictions.is_empty() {
        println!("   ✓ No contradictions");
    } else {
        println!("   ⚠️  {} contradiction(s) detected", contradictions.len());
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
    }

    // Detect omissions
    let omit_resp = client
        .detect_omissions(Request::new(crate::proto::DetectOmissionsRequest {}))
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

/// Helper: Determine if file event should trigger re-extraction
fn should_process_event(event: &Event) -> bool {
    use notify::EventKind;
    matches!(event.kind, EventKind::Modify(_) | EventKind::Create(_))
}
