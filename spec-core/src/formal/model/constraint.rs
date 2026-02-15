/// Constraint extraction: Consolidate all constraint extraction logic
///
/// This module provides the authoritative implementation for extracting constraints
/// from natural language specifications.
use crate::formal::{Constraint, ConstraintKind, ConstraintMetadata, MetadataKey};
use std::collections::HashMap;

/// Extract constraints from natural language text
///
/// Parses specification text to identify implicit constraints like:
/// - "at least N" → minimum constraint
/// - "at most N" → maximum constraint
/// - "must be" / "must not be" → boolean constraints
/// - "between X and Y" → range constraints
///
/// This is the consolidated implementation that replaces duplicates in
/// graph.rs and model.rs.
pub fn extract_constraints_from_text(text: &str) -> Vec<Constraint> {
    let mut constraints = Vec::new();
    let lower_text = text.to_lowercase();

    // Pattern 1: "at least N"
    if let Some(min_value) = extract_numeric_value(&lower_text, "at least") {
        let mut meta = ConstraintMetadata::new();
        meta.set_pattern("at_least".to_string());
        meta.set_value(min_value.to_string());
        meta.set_source(text.to_string());

        // Context-aware variable extraction
        let variable = extract_variable_context(&lower_text, "at least");
        if let Some(var) = &variable {
            meta.insert(MetadataKey::Custom("variable".to_string()), var.clone());
        }

        let description_text = if let Some(var) = variable {
            format!("{} must be at least {}", var, min_value)
        } else {
            format!("Minimum value: {}", min_value)
        };

        let mut meta_with_desc = meta.clone();
        meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

        let formal = if let Some(var) = extract_variable_context(&lower_text, "at least") {
            format!("(>= {} {})", var, min_value)
        } else {
            format!(">= {}", min_value)
        };

        constraints.push(Constraint {
            formal: Some(formal),
            kind: ConstraintKind::Universal,
            description: Some(description_text),
            metadata: Some(meta),
            meta: Some(meta_with_desc),
        });
    }

    // Pattern 2: "at most N"
    if let Some(max_value) = extract_numeric_value(&lower_text, "at most") {
        let mut meta = ConstraintMetadata::new();
        meta.set_pattern("at_most".to_string());
        meta.set_value(max_value.to_string());
        meta.set_source(text.to_string());

        let variable = extract_variable_context(&lower_text, "at most");
        if let Some(var) = &variable {
            meta.insert(MetadataKey::Custom("variable".to_string()), var.clone());
        }

        let description_text = if let Some(var) = variable {
            format!("{} must be at most {}", var, max_value)
        } else {
            format!("Maximum value: {}", max_value)
        };

        let mut meta_with_desc = meta.clone();
        meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

        let formal = if let Some(var) = extract_variable_context(&lower_text, "at most") {
            format!("(<= {} {})", var, max_value)
        } else {
            format!("<= {}", max_value)
        };

        constraints.push(Constraint {
            formal: Some(formal),
            kind: ConstraintKind::Universal,
            description: Some(description_text),
            metadata: Some(meta),
            meta: Some(meta_with_desc),
        });
    }

    // Pattern 3: "minimum N" / "minimum of N"
    if let Some(min_value) = extract_minimum_value(&lower_text) {
        // Avoid duplicates with "at least N"
        if !lower_text.contains("at least") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("minimum".to_string());
            meta.set_value(min_value.to_string());
            meta.set_source(text.to_string());

            let variable = extract_variable_context(&lower_text, "minimum");
            if let Some(var) = &variable {
                meta.insert(MetadataKey::Custom("variable".to_string()), var.clone());
            }

            let description_text = if let Some(var) = variable {
                format!("{} must be at least {}", var, min_value)
            } else {
                format!("Minimum value: {}", min_value)
            };

            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            let formal = if let Some(var) = extract_variable_context(&lower_text, "minimum") {
                format!("(>= {} {})", var, min_value)
            } else {
                format!(">= {}", min_value)
            };

            constraints.push(Constraint {
                formal: Some(formal),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }
    }

    // Pattern 4: "maximum N" / "maximum of N"
    if let Some(max_value) = extract_maximum_value(&lower_text) {
        // Avoid duplicates with "at most N"
        if !lower_text.contains("at most") {
            let mut meta = ConstraintMetadata::new();
            meta.set_pattern("maximum".to_string());
            meta.set_value(max_value.to_string());
            meta.set_source(text.to_string());

            let variable = extract_variable_context(&lower_text, "maximum");
            if let Some(var) = &variable {
                meta.insert(MetadataKey::Custom("variable".to_string()), var.clone());
            }

            let description_text = if let Some(var) = variable {
                format!("{} must be at most {}", var, max_value)
            } else {
                format!("Maximum value: {}", max_value)
            };

            let mut meta_with_desc = meta.clone();
            meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

            let formal = if let Some(var) = extract_variable_context(&lower_text, "maximum") {
                format!("(<= {} {})", var, max_value)
            } else {
                format!("<= {}", max_value)
            };

            constraints.push(Constraint {
                formal: Some(formal),
                kind: ConstraintKind::Universal,
                description: Some(description_text),
                metadata: Some(meta),
                meta: Some(meta_with_desc),
            });
        }
    }

    // Pattern 5: "exactly N"
    if let Some(exact_value) = extract_numeric_value(&lower_text, "exactly") {
        let mut meta = ConstraintMetadata::new();
        meta.set_pattern("exactly".to_string());
        meta.set_value(exact_value.to_string());
        meta.set_source(text.to_string());

        let variable = extract_variable_context(&lower_text, "exactly");
        if let Some(var) = &variable {
            meta.insert(MetadataKey::Custom("variable".to_string()), var.clone());
        }

        let description_text = if let Some(var) = variable {
            format!("{} must be exactly {}", var, exact_value)
        } else {
            format!("Exact value: {}", exact_value)
        };

        let mut meta_with_desc = meta.clone();
        meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

        let formal = if let Some(var) = extract_variable_context(&lower_text, "exactly") {
            format!("(== {} {})", var, exact_value)
        } else {
            format!("== {}", exact_value)
        };

        constraints.push(Constraint {
            formal: Some(formal),
            kind: ConstraintKind::Universal,
            description: Some(description_text),
            metadata: Some(meta),
            meta: Some(meta_with_desc),
        });
    }

    // Pattern 6: "between X and Y"
    if let Some((min, max)) = extract_range(&lower_text) {
        let mut meta = ConstraintMetadata::new();
        meta.set_pattern("range".to_string());
        meta.set_min(min.to_string());
        meta.set_max(max.to_string());
        meta.set_source(text.to_string());

        let variable = extract_variable_context(&lower_text, "between");
        if let Some(var) = &variable {
            meta.insert(MetadataKey::Custom("variable".to_string()), var.clone());
        }

        let description_text = if let Some(var) = variable {
            format!("{} must be between {} and {}", var, min, max)
        } else {
            format!("Range: {} to {}", min, max)
        };

        let mut meta_with_desc = meta.clone();
        meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

        let formal = if let Some(var) = extract_variable_context(&lower_text, "between") {
            format!("(and (>= {} {}) (<= {} {}))", var, min, var, max)
        } else {
            format!(">= {} && <= {}", min, max)
        };

        constraints.push(Constraint {
            formal: Some(formal),
            kind: ConstraintKind::Universal,
            description: Some(description_text),
            metadata: Some(meta),
            meta: Some(meta_with_desc),
        });
    }

    // Pattern 7: "must be" (boolean requirement)
    if lower_text.contains("must be") && !lower_text.contains("at least") && !lower_text.contains("at most")
        && let Some(pos) = lower_text.find("must be") {
            let after = &text[pos + 7..].trim();
            if !after.is_empty() {
                let mut meta = ConstraintMetadata::new();
                meta.set_pattern("must_be".to_string());
                meta.set_value(after.to_string());
                meta.set_source(text.to_string());

                let description_text = format!("Required: {}", after);
                let mut meta_with_desc = meta.clone();
                meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

                constraints.push(Constraint {
                    formal: Some(format!("== {}", after)),
                    kind: ConstraintKind::Universal,
                    description: Some(description_text),
                    metadata: Some(meta),
                    meta: Some(meta_with_desc),
                });
            }
        }

    // Pattern 8: "must not be" / "cannot be" (boolean prohibition)
    if lower_text.contains("must not") || lower_text.contains("cannot be") {
        let pattern = if lower_text.contains("must not") { "must not" } else { "cannot be" };
        if let Some(pos) = lower_text.find(pattern) {
            let after = &text[pos + pattern.len()..].trim();
            if !after.is_empty() {
                let mut meta = ConstraintMetadata::new();
                meta.set_pattern("must_not_be".to_string());
                meta.set_value(after.to_string());
                meta.set_source(text.to_string());

                let description_text = format!("Forbidden: {}", after);
                let mut meta_with_desc = meta.clone();
                meta_with_desc.insert(MetadataKey::Custom("description".to_string()), description_text.clone());

                constraints.push(Constraint {
                    formal: Some(format!("!= {}", after)),
                    kind: ConstraintKind::Universal,
                    description: Some(description_text),
                    metadata: Some(meta),
                    meta: Some(meta_with_desc),
                });
            }
        }
    }

    // Pattern 9: Generic "must" / "required" (universal constraint)
    if (lower_text.contains("must") || lower_text.contains("required"))
        && !lower_text.contains("must be")
        && !lower_text.contains("must not")
        && constraints.is_empty()  // Only add if no other constraints extracted
    {
        let mut metadata_map = HashMap::new();
        metadata_map.insert("type".to_string(), "universal".to_string());
        metadata_map.insert("description".to_string(), text.to_string());

        constraints.push(Constraint {
            formal: None, // Natural language only
            kind: ConstraintKind::Universal,
            description: Some(text.to_string()),
            metadata: Some(ConstraintMetadata::from(metadata_map.clone())),
            meta: Some(ConstraintMetadata::from(metadata_map)),
        });
    }

    constraints
}

/// Extract numeric value after a keyword
fn extract_numeric_value(text: &str, keyword: &str) -> Option<i64> {
    if let Some(pos) = text.find(keyword) {
        let after = &text[pos + keyword.len()..];
        for word in after.split_whitespace() {
            if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric() && c != '-').parse::<i64>() {
                return Some(n);
            }
        }
    }
    None
}

/// Extract minimum value using regex patterns
pub fn extract_minimum_value(text: &str) -> Option<u32> {
    use regex::Regex;
    let patterns = [
        r"at least (\d+)",
        r"minimum (\d+)",
        r"min (\d+)",
        r"minimum of (\d+)",
        r">= ?(\d+)",
        r"≥ ?(\d+)",
    ];

    for pattern in &patterns {
        if let Ok(re) = Regex::new(pattern)
            && let Some(cap) = re.captures(text)
                && let Some(num_str) = cap.get(1)
                    && let Ok(num) = num_str.as_str().parse::<u32>() {
                        return Some(num);
                    }
    }

    None
}

/// Extract maximum value using regex patterns
pub fn extract_maximum_value(text: &str) -> Option<u32> {
    use regex::Regex;
    let patterns = [
        r"at most (\d+)",
        r"maximum (\d+)",
        r"max (\d+)",
        r"maximum of (\d+)",
        r"<= ?(\d+)",
        r"≤ ?(\d+)",
    ];

    for pattern in &patterns {
        if let Ok(re) = Regex::new(pattern)
            && let Some(cap) = re.captures(text)
                && let Some(num_str) = cap.get(1)
                    && let Ok(num) = num_str.as_str().parse::<u32>() {
                        return Some(num);
                    }
    }

    None
}

/// Extract range from "between X and Y" pattern
fn extract_range(text: &str) -> Option<(i64, i64)> {
    if let Some(pos) = text.find("between") {
        let after = &text[pos + 7..];
        let parts: Vec<&str> = after.split("and").collect();
        if parts.len() >= 2 {
            let min = extract_first_number(parts[0])?;
            let max = extract_first_number(parts[1])?;
            return Some((min, max));
        }
    }
    None
}

/// Extract first number from string
fn extract_first_number(s: &str) -> Option<i64> {
    for word in s.split_whitespace() {
        if let Ok(n) = word.trim_matches(|c: char| !c.is_numeric() && c != '-').parse::<i64>() {
            return Some(n);
        }
    }
    None
}

/// Extract variable context (e.g., "password" from "password must be at least 8")
fn extract_variable_context(text: &str, keyword: &str) -> Option<String> {
    if let Some(pos) = text.find(keyword) {
        let before = &text[..pos];
        let words: Vec<&str> = before.split_whitespace().collect();

        // Look for common patterns
        if text.contains("password") {
            return Some("password_length".to_string());
        }
        if text.contains("length") || text.contains("size") {
            return Some("length".to_string());
        }
        if text.contains("count") {
            return Some("count".to_string());
        }

        // Generic: last word before keyword
        if let Some(&last_word) = words.last()
            && !last_word.is_empty() && last_word.chars().all(|c| c.is_alphanumeric() || c == '_') {
                return Some(last_word.to_string());
            }
    }
    None
}
