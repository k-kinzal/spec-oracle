/// File watching and synchronization commands (gRPC only)
///
/// Continuously monitors source files and automatically extracts/verifies specifications.
/// Extraction is delegated to specd via gRPC.

use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use notify::{Event, Watcher, RecursiveMode};
use std::sync::mpsc::channel;
use std::time::Duration;
use std::path::Path;
use tonic::Request;

/// Execute Watch command via gRPC
pub async fn execute_watch_server(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    source: String,
    language: String,
    _min_confidence: f32,
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

    println!("Watching {} for changes...", source);
    println!("   Check interval: {}s", interval);
    println!("   Press Ctrl+C to stop\n");

    let (tx, rx) = channel();
    let mut watcher = notify::recommended_watcher(tx)
        .map_err(|e| format!("Failed to create watcher: {}", e))?;

    watcher.watch(source_path, RecursiveMode::Recursive)
        .map_err(|e| format!("Failed to watch path: {}", e))?;

    // Initial verification
    println!("Running initial verification...");
    verify_specifications(client).await?;
    println!();

    // Watch loop
    loop {
        match rx.recv_timeout(Duration::from_secs(interval)) {
            Ok(Ok(event)) => {
                if should_process_event(&event) {
                    if let Some(path) = event.paths.first() {
                        if path.extension().and_then(|s| s.to_str()) == Some("rs") {
                            println!("Change detected: {:?}", path.file_name());
                            println!("   Verifying...");
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

/// Helper: Verify specifications via gRPC
async fn verify_specifications(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Run contradiction detection
    let resp = client.detect_contradictions(Request::new(proto::DetectContradictionsRequest {})).await?;
    let contradictions = resp.into_inner().contradictions;

    if contradictions.is_empty() {
        println!("   No contradictions");
    } else {
        println!("   {} contradiction(s) detected", contradictions.len());
        for (i, c) in contradictions.iter().take(3).enumerate() {
            if let (Some(a), Some(b)) = (&c.node_a, &c.node_b) {
                println!("      {}. {} <-> {}",
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
        .detect_omissions(Request::new(proto::DetectOmissionsRequest {}))
        .await?;
    let omissions = omit_resp.into_inner().omissions;

    let isolated_count = omissions.iter()
        .filter(|o| o.description.contains("Isolated"))
        .count();

    if isolated_count > 0 {
        println!("   {} isolated specification(s)", isolated_count);
    }

    Ok(())
}

/// Helper: Determine if file event should trigger re-verification
fn should_process_event(event: &Event) -> bool {
    use notify::EventKind;
    matches!(event.kind, EventKind::Modify(_) | EventKind::Create(_))
}
