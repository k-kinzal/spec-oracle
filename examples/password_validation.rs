/// Password validation module demonstrating multi-layer specifications
///
/// Specification: Password must be at least 8 characters long
/// This requirement exists at multiple formality layers:
/// - Layer 0 (this doc comment): Natural language
/// - Layer 1 (function names): Structured conventions
/// - Layer 3 (assertions/code): Executable constraints

/// Validates that a password meets minimum length requirements.
/// Passwords must be at least 8 characters.
pub fn validate_password_length(password: &str) -> bool {
    // Layer 3: Executable specification
    assert!(password.len() >= 8, "Password must be at least 8 characters");
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that passwords shorter than 8 characters are rejected
    #[test]
    fn test_password_minimum_length() {
        // Layer 3: Executable specification via test
        assert!(!validate_password_length("short"));
        assert!(validate_password_length("verylongpassword"));
    }

    #[test]
    fn test_exactly_eight_characters() {
        assert!(validate_password_length("exactly8"));
    }
}
