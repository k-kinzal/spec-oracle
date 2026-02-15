/// Check command: Detect contradictions and omissions in specifications
///
/// This command runs both contradiction and omission detection,
/// providing unified results to the user.

use crate::proto;
use spec_core::Store;
use tonic::Request;

/// Execute the Check command in standalone mode
pub fn execute_check_standalone(
    store: &Store,
) -> Result<i32, Box<dyn std::error::Error>> {
    let graph = store.load()?;

    println!("🔍 Checking specifications...\n");

    // Collect statistics and filter by lifecycle status
    let all_nodes = graph.list_nodes(None);
    let total_nodes = all_nodes.len();

    // Count by lifecycle status
    let archived_nodes: Vec<_> = all_nodes.iter()
        .filter(|n| n.metadata.get("status").map(|s| s.as_str()) == Some("archived"))
        .collect();
    let deprecated_nodes: Vec<_> = all_nodes.iter()
        .filter(|n| n.metadata.get("status").map(|s| s.as_str()) == Some("deprecated"))
        .collect();
    let active_nodes: Vec<_> = all_nodes.iter()
        .filter(|n| {
            let status = n.metadata.get("status").map(|s| s.as_str());
            status.is_none() || status == Some("active")
        })
        .collect();

    let inferred_nodes: Vec<_> = active_nodes.iter()
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
    println!("  Active specs:       {}", active_nodes.len());
    if !deprecated_nodes.is_empty() {
        println!("  Deprecated specs:   ⚠️  {}", deprecated_nodes.len());
    }
    if !archived_nodes.is_empty() {
        println!("  Archived specs:     {} (excluded from checks)", archived_nodes.len());
    }
    println!("  Extracted specs:    {} ({:.1}%)", inferred_count,
        (inferred_count as f64 / active_nodes.len().max(1) as f64) * 100.0);
    println!("  Contradictions:     {}", contradictions.len());
    println!("  Isolated specs:     {}", omissions.len());

    // Show deprecated specs warning
    if !deprecated_nodes.is_empty() {
        println!("\n⚠️  Deprecated specifications:");
        for (i, node) in deprecated_nodes.iter().take(5).enumerate() {
            println!("  {}. [{}] {}", i + 1, &node.id[..8],
                node.content.chars().take(60).collect::<String>());
        }
        if deprecated_nodes.len() > 5 {
            println!("  ... and {} more", deprecated_nodes.len() - 5);
        }
        println!("  💡 Consider updating or archiving these specifications");
    }

    let total_issues = contradictions.len() + omissions.len();
    let exit_code = if total_issues == 0 {
        println!("\n✅ All checks passed! No issues found.");
        0
    } else {
        println!("\n❌ Critical issues found!");

        // Show contradictions
        if !contradictions.is_empty() {
            println!("\nContradictions:");
            for (i, c) in contradictions.iter().enumerate() {
                println!("  {}. {}", i + 1, c.explanation);
                println!("     A: [{}] {}", &c.node_a.id[..8], c.node_a.content);
                println!("     B: [{}] {}", &c.node_b.id[..8], c.node_b.content);
            }
        }

        // Show omissions summary
        if !omissions.is_empty() {
            println!("\nIsolated specifications:");
            for (i, o) in omissions.iter().take(5).enumerate() {
                println!("  {}. {}", i + 1, o.description);
            }
            if omissions.len() > 5 {
                println!("  ... and {} more", omissions.len() - 5);
            }
        }

        1 // Exit code 1 for issues found
    };

    Ok(exit_code)
}

/// Execute the Check command in server mode
pub async fn execute_check_server(
    client: &mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>,
) -> Result<i32, Box<dyn std::error::Error>> {
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
    let exit_code = if total_issues == 0 {
        println!("\n✅ All checks passed! No issues found.");
        0
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
        1
    } else {
        println!("\n❌ Critical issues found!");

        // Show contradictions
        println!("\nContradictions:");
        for (i, c) in contradictions.iter().enumerate() {
            println!("  {}. {}", i + 1, c.explanation);
            if let (Some(node_a), Some(node_b)) = (&c.node_a, &c.node_b) {
                println!("     A: [{}] {}", node_a.id, node_a.content);
                println!("     B: [{}] {}", node_b.id, node_b.content);
            }
        }

        1
    };

    Ok(exit_code)
}

/// Unified entry point for the Check command
pub fn execute_check(
    standalone_mode: bool,
    store: Option<&Store>,
    client: Option<&mut proto::spec_oracle_client::SpecOracleClient<tonic::transport::Channel>>,
    runtime: Option<&tokio::runtime::Runtime>,
) -> Result<i32, Box<dyn std::error::Error>> {
    if standalone_mode {
        if let Some(store) = store {
            execute_check_standalone(store)
        } else {
            Err("Standalone mode requires a FileStore".into())
        }
    } else {
        if let (Some(client), Some(rt)) = (client, runtime) {
            rt.block_on(execute_check_server(client))
        } else {
            Err("Server mode requires a client and runtime".into())
        }
    }
}
