# Session Context

## User Prompts

### Prompt 1

Implement the following plan:

# Refactoring Plan: Reorganize spec-core into formal/ Directory

## Context

The user requested to refactor spec-core by:
1. Moving all code into `spec-core/src/formal/` (formal verification layer)
2. Splitting large files (udaf.rs: 1,536 LOC, prover/mod.rs: 1,238 LOC) into smaller modules
3. Following Rust best practices with clear directory structure
4. **Key insight**: `formal/` IS the UDA/f space itself, not a wrapper around `udaf/`
5. **Important**: Each conce...

### Prompt 2

変更内容のコミットをお願いします。

