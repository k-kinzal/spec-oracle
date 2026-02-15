# Session 129: Graph Visualization Feature

**Date**: 2026-02-15

## Goal
Implement DOT format export for graph visualization to enable understanding of specORACLE's multi-layer defense coordination.

## Context
PROBLEM.md identified two unresolved issues related to visualization:
1. **仕様からドキュメントを生成・可視化できない** - Partially solved (Markdown done, graph visualization missing)
2. **仕様の多層構造を可視化するコマンドがない** - Essential for understanding U0→U3 layers

## Discovery
The DOT export feature was **already implemented** in `spec-cli/src/commands/export_dot.rs` (159 lines), but needed verification and documentation.

## Actions Taken

### 1. Verified Existing Implementation ✅
- **File**: `spec-cli/src/commands/export_dot.rs`
- **Command**: `spec export-dot [--output file.dot] [--layer N] [--metadata]`
- **Features**:
  - Layer-based subgraphs (U0-U3 clusters)
  - Kind-based node coloring (Constraint=red, Assertion=blue, Scenario=green)
  - Edge styling by type (Refines=solid, Formalizes=bold, Contradicts=red)
  - Metadata support (source_file, auto-extracted markers)

### 2. Tested Graphviz Integration ✅
```bash
# Install Graphviz
brew install graphviz

# Export to DOT format
spec export-dot -o .spec/spec-graph.dot

# Generate PNG visualization
dot -Tpng .spec/spec-graph.dot -o docs/spec-graph.png
# Result: 2.0MB PNG (graph is large, scaled by 0.565797)

# Generate SVG visualization
dot -Tsvg .spec/spec-graph.dot -o docs/spec-graph.svg
# Result: 290KB SVG
```

### 3. Verification Results ✅
- ✅ **251 specifications** visualized successfully
- ✅ **Layer-based subgraphs**: U0 (129 specs), U1 (1 spec), U2 (65 specs), U3 (56 specs)
- ✅ **Kind-based colors**: Clear visual distinction
- ✅ **Edge direction and types**: Clearly labeled
- ✅ **PNG/SVG output**: Both formats generated successfully

### 4. Updated Documentation ✅
- **README.md**: Already documented `export-dot` command (lines 191-193, 285, 302)
- **PROBLEM.md**: Updated two issues to resolved status:
  - **仕様からドキュメントを生成・可視化できない**: ✅ Resolved (Session 129)
  - **仕様の多層構造を可視化するコマンドがない**: ✅ Resolved (Session 58 & 129)

## Implementation Details

### Core Method (Already Existed)
`spec-core/src/graph.rs`: Added `export_dot()` method (not used by CLI)

### CLI Implementation (Already Existed)
`spec-cli/src/commands/export_dot.rs`:
- `execute_export_dot_standalone()`: Main export logic
- Layer filtering: `--layer <N>` option
- Metadata inclusion: `--metadata` flag
- Output modes: stdout or file (`--output`)

### Graphviz Output Features
- **Node attributes**:
  - Shape: box
  - Style: filled, rounded
  - Color: Based on formality layer
  - Label: `[layer] [kind] content (truncated)`
- **Edge attributes**:
  - Label: Edge kind (refines, formalizes, etc.)
  - Style: solid/dashed/bold/dotted
  - Color: Based on edge kind
- **Subgraphs**: One per layer (cluster_U0, cluster_U1, etc.)

## Example Usage
```bash
# Export full graph
spec export-dot -o .spec/spec-graph.dot
dot -Tpng .spec/spec-graph.dot -o docs/spec-graph.png

# Export U0 layer only
spec export-dot --layer 0 -o u0-graph.dot
dot -Tsvg u0-graph.dot -o u0-graph.svg

# Export with metadata
spec export-dot --metadata -o detailed-graph.dot

# Output to stdout (for piping)
spec export-dot | dot -Tpng > graph.png
```

## Impact

### Problems Solved ✅
1. **Graph visualization**: Users can now see the entire specification graph visually
2. **Multi-layer structure**: U0→U3 relationships are clearly visible
3. **Understanding tool**: Essential for comprehending specORACLE's reverse mapping engine

### User Benefits
- **Visual overview**: See all 251 specifications and their relationships at a glance
- **Layer separation**: Understand which specs belong to which formality layer
- **Relationship clarity**: See how specs connect (Refines, Formalizes, DerivesFrom)
- **Documentation**: Export graphs for presentations, reports, documentation

### Technical Achievements
- **Scalability**: Handles 251 specs + edges without issues
- **Flexibility**: Layer filtering, metadata options
- **Standards compliance**: Uses standard DOT format (works with any Graphviz tool)

## Files Modified
- `PROBLEM.md`: Updated two issues to resolved status

## Files Generated
- `docs/spec-graph.png`: Full graph visualization (2.0MB)
- `docs/spec-graph.svg`: Full graph visualization (290KB, scalable)
- `.spec/spec-graph.dot`: DOT format source

## Statistics
- **Total specifications**: 251
- **Extracted specs**: 75 (29.9%)
- **Contradictions**: 0
- **Isolated specs**: 0
- **Graph files**: PNG (2.0MB), SVG (290KB), DOT (variable size)

## Related Sessions
- **Session 58**: Implemented `spec trace` command for hierarchical relationship display
- **Session 68**: Implemented Markdown export (`scripts/export_specs_md.py`)
- **Session 129** (this): Verified and documented DOT export for graph visualization

## Conclusion
Graph visualization feature was **already fully implemented** and just needed verification and documentation. Both critical visualization problems are now resolved:
- ✅ Document generation (Markdown export)
- ✅ Graph visualization (DOT export + Graphviz)

specORACLE now provides comprehensive visualization capabilities for understanding multi-layer defense coordination.
