use crate::proto::{SpecEdgeKind, SpecNodeKind};
use spec_core::NodeKind as CoreNodeKind;

/// Parse node kind string to proto SpecNodeKind
pub fn parse_node_kind(s: &str) -> SpecNodeKind {
    match s.to_lowercase().as_str() {
        "assertion" => SpecNodeKind::Assertion,
        "constraint" => SpecNodeKind::Constraint,
        "scenario" => SpecNodeKind::Scenario,
        "definition" => SpecNodeKind::Definition,
        "domain" => SpecNodeKind::Domain,
        _ => SpecNodeKind::Assertion,
    }
}

/// Parse edge kind string to proto SpecEdgeKind
pub fn parse_edge_kind(s: &str) -> SpecEdgeKind {
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

/// Parse formality layer (after migration, just convert u8 to u32)
pub fn parse_formality_layer(formality_layer: u8) -> u32 {
    formality_layer as u32
}

/// Convert proto NodeKind to core NodeKind
pub fn proto_to_core_kind(kind: SpecNodeKind) -> CoreNodeKind {
    match kind {
        SpecNodeKind::Assertion => CoreNodeKind::Assertion,
        SpecNodeKind::Constraint => CoreNodeKind::Constraint,
        SpecNodeKind::Scenario => CoreNodeKind::Scenario,
        SpecNodeKind::Definition => CoreNodeKind::Definition,
        SpecNodeKind::Domain => CoreNodeKind::Domain,
        _ => CoreNodeKind::Assertion,
    }
}

/// Convert proto node kind i32 to name string
pub fn node_kind_name(k: i32) -> &'static str {
    match SpecNodeKind::try_from(k) {
        Ok(SpecNodeKind::Assertion) => "assertion",
        Ok(SpecNodeKind::Constraint) => "constraint",
        Ok(SpecNodeKind::Scenario) => "scenario",
        Ok(SpecNodeKind::Definition) => "definition",
        Ok(SpecNodeKind::Domain) => "domain",
        _ => "unknown",
    }
}

/// Convert proto edge kind i32 to name string
pub fn edge_kind_name(k: i32) -> &'static str {
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
pub fn infer_spec_kind(content: &str) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer_spec_kind_constraint() {
        assert_eq!(infer_spec_kind("Password must always be 8 characters"), "constraint");
        assert_eq!(infer_spec_kind("System shall never allow unauthorized access"), "constraint");
    }

    #[test]
    fn test_infer_spec_kind_scenario() {
        assert_eq!(infer_spec_kind("When user logs in, they should see dashboard"), "scenario");
        assert_eq!(infer_spec_kind("User can reset password"), "scenario");
    }

    #[test]
    fn test_infer_spec_kind_definition() {
        assert_eq!(infer_spec_kind("Authentication is defined as verifying identity"), "definition");
    }

    #[test]
    fn test_infer_spec_kind_assertion() {
        assert_eq!(infer_spec_kind("The API returns JSON"), "assertion");
        assert_eq!(infer_spec_kind("General statement"), "assertion");
    }
}
