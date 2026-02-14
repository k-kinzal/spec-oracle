use spec_core::graph::{EdgeKind, NodeKind as CoreNodeKind};

/// Format formality layer as "U0", "U1", "U2", "U3"
pub fn format_formality_layer(formality_layer: u8) -> String {
    match formality_layer {
        0 => "U0".to_string(),
        1 => "U1".to_string(),
        2 => "U2".to_string(),
        3 => "U3".to_string(),
        _ => format!("U{}", formality_layer),
    }
}

/// Format node kind for display
pub fn format_node_kind(kind: CoreNodeKind) -> &'static str {
    match kind {
        CoreNodeKind::Assertion => "assertion",
        CoreNodeKind::Constraint => "constraint",
        CoreNodeKind::Scenario => "scenario",
        CoreNodeKind::Definition => "definition",
        CoreNodeKind::Domain => "domain",
    }
}

/// Format edge kind for display
pub fn format_edge_kind(kind: EdgeKind) -> &'static str {
    match kind {
        EdgeKind::Refines => "refines",
        EdgeKind::DependsOn => "depends_on",
        EdgeKind::Contradicts => "contradicts",
        EdgeKind::DerivesFrom => "derives_from",
        EdgeKind::Synonym => "synonym",
        EdgeKind::Composes => "composes",
        EdgeKind::Formalizes => "formalizes",
        EdgeKind::Transform => "transform",
    }
}

/// Format a node summary line with layer, ID, kind, and content
pub fn format_node_summary(
    layer: u8,
    id_short: &str,
    kind: CoreNodeKind,
    content: &str,
    max_content_len: usize,
) -> String {
    let layer_label = format_formality_layer(layer);
    let kind_str = format_node_kind(kind);

    let truncated_content = if content.len() > max_content_len {
        format!("{}...", &content[..max_content_len])
    } else {
        content.to_string()
    };

    format!(
        "[{}] [{}] {} - {}",
        layer_label, id_short, kind_str, truncated_content
    )
}

/// Format a contradiction report
pub fn format_contradiction(
    index: usize,
    description: &str,
    spec_a_id: &str,
    spec_a_content: &str,
    spec_b_id: &str,
    spec_b_content: &str,
) -> String {
    format!(
        "  {}. {}\n     A: [{}] {}\n     B: [{}] {}",
        index, description, spec_a_id, spec_a_content, spec_b_id, spec_b_content
    )
}

/// Format an omission report
pub fn format_omission(index: usize, description: &str) -> String {
    format!("  {}. {}", index, description)
}

/// Format a summary line (e.g., "Total specs: 225")
pub fn format_summary_line(label: &str, value: impl std::fmt::Display) -> String {
    format!("  {:<20} {}", label, value)
}

/// Format a percentage
pub fn format_percentage(numerator: usize, denominator: usize) -> String {
    if denominator == 0 {
        "0.0%".to_string()
    } else {
        format!("{:.1}%", (numerator as f64 / denominator as f64) * 100.0)
    }
}
