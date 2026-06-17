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
