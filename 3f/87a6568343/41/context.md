# Session Context

## User Prompts

### Prompt 1

Implement the following plan:

# Architectural Refactoring: Separate Formal Layer from Data Layer

## Context

The user identified a critical architectural issue in spec-core: **SpecGraph (data layer) performs formal verification, which should be UDAFModel's (formal layer) responsibility.**

### Current Problems

1. **SpecGraph (graph.rs, 2792 lines)** mixes responsibilities:
   - Data persistence (nodes, edges, serialization) ✓ Correct
   - **Formal verification** (detect_contradiction_via_z3...

### Prompt 2

私は後方互換は不要であるとしました。Future Cleanupを全て完遂してください。

### Prompt 3

ありがとうございます。ここまでの変更内容をコミットしてください。

