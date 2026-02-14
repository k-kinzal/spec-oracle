# Bootstrapping Self-Specifications

**Date**: 2026-02-14

## Goal

Use spec-oracle to manage its own specifications, per CLAUDE.md requirement: "Once a minimum viable tool is developed, use it to manage its own specifications."

## Work Performed

### 1. Started the specd server

```bash
./target/release/specd &
```

### 2. Created domain structure

Added 5 core domains:
- **Architecture**: System structure and separation of concerns
- **Communication**: Protocol and client-server interaction
- **Storage**: Data persistence mechanisms
- **Analysis**: Specification analysis capabilities
- **Quality**: Testing and verification requirements

### 3. Added constraints

Defined 9 constraints from CLAUDE.md requirements:
- System separation (command vs daemon)
- gRPC communication
- Rust implementation
- Graph data storage
- Omission detection
- Contradiction detection
- Natural language processing
- Terminology resolution
- Test guarantees

### 4. Linked constraints to domains

Created refines edges to associate each constraint with its domain:
- Architecture ← system separation, Rust requirement
- Communication ← gRPC
- Storage ← graph data management
- Analysis ← omission detection, contradiction detection, NL processing, terminology
- Quality ← test guarantees

### 5. Added implementation assertions

Documented actual implementation choices:
- petgraph for graph structure
- JSON for persistence
- External AI CLI delegation (claude/codex)
- 14 passing unit tests
- Ask command implementation
- Contradiction detection algorithm
- Omission detection algorithm

### 6. Defined required scenarios

Specified 3 key scenarios:
- User can query using natural language
- System detects contradictions
- System identifies omissions

### 7. Linked assertions to scenarios

Connected implementation assertions to scenarios they support:
- Ask command → NL query scenario
- Contradiction analysis → contradiction scenario
- Omission analysis → omission scenario

### 8. Validated specification completeness

Ran analysis commands:
```bash
./target/release/spec detect-contradictions
# Result: No contradictions detected

./target/release/spec detect-omissions
# Result: No omissions detected (after adding supporting assertions)
```

## Final Specification Graph

- **24 nodes**: 5 domains, 9 constraints, 7 assertions, 3 scenarios
- **18 edges**: refines, derives_from relationships
- **0 contradictions**: Specification is internally consistent
- **0 omissions**: All domains have refinements, all scenarios have supporting assertions

## Status

The spec-oracle tool is now managing its own specifications. The specification graph accurately reflects:
1. The requirements from CLAUDE.md
2. The actual implementation choices
3. The testing guarantees

The system successfully detected omissions (missing assertions) and the issue was resolved by adding concrete implementation assertions. This validates that the omission detection capability works correctly.

## Next Steps

The system can now be used to:
- Query its own specifications: `spec ask "What are the architecture requirements?"`
- Detect inconsistencies as the system evolves
- Track specification changes alongside code changes
- Ensure all new features have corresponding specifications
