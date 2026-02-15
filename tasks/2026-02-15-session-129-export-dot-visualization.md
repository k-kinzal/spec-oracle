# Session 129: Implement DOT Format Export for Graph Visualization

**Date**: 2026-02-15
**Status**: ✅ Completed

## Problem

Users cannot visualize the specification graph structure. While the system maintains a complex graph of specifications with multiple layers (U0-U3) and various edge relationships, there is no way to see this structure visually.

**PROBLEM.md Reference**: "仕様からドキュメントを生成・可視化できない" (Medium priority)
- ⏳ グラフ可視化（DOT/Graphviz形式出力）- **This task addresses this**
- ⏳ HTMLエクスポート（静的サイト生成）
- ⏳ PDFエクスポート

## Solution

Implemented `spec export-dot` command that exports the specification graph in DOT format, which can be visualized using Graphviz tools.

### Features

- **Layered visualization**: Subgraphs for each formality layer (U0-U3)
- **Color coding**: Different colors for different node kinds
  - Constraints: Light red (#ffe0e0)
  - Assertions: Light blue (#e0f0ff)
  - Scenarios: Light green (#e0ffe0)
  - Definitions: Light orange (#fff0e0)
  - Domains: Light purple (#f0e0ff)
- **Edge styling**: Different styles and colors for edge types
  - Refines: Solid blue
  - Formalizes: Bold dark blue
  - Contradicts: Bold red
  - DerivesFrom: Dotted purple
  - DependsOn: Dashed gray
  - Synonym: Dashed green
  - Composes: Solid orange
  - Transform: Bold dark orange
- **Layer filtering**: `--layer <N>` to export only specific layer
- **Metadata inclusion**: `--metadata` flag to include source file and auto-extraction info
- **File or stdout**: `--output <file>` to save to file, or pipe to other tools

### Implementation

**New files**:
- `spec-cli/src/commands/export_dot.rs` (160 lines)

**Modified files**:
- `spec-cli/src/commands/mod.rs` - Added export_dot module and export
- `spec-cli/src/main.rs` - Added ExportDot command variant
- `spec-cli/src/commands/dispatcher.rs` - Added dispatch case for ExportDot

## Usage Examples

```bash
# Export entire graph to file
spec export-dot --output spec-graph.dot

# Export only U0 (requirements) layer
spec export-dot --layer 0 --output u0-requirements.dot

# Include metadata in labels
spec export-dot --metadata --output spec-graph-full.dot

# Pipe to stdout (for processing)
spec export-dot | dot -Tpng > spec-graph.png

# Generate PNG visualization
spec export-dot --output spec-graph.dot
dot -Tpng spec-graph.dot -o spec-graph.png

# Generate SVG (better for web)
dot -Tsvg spec-graph.dot -o spec-graph.svg
```

## Results

**Current system state**:
- Total specs: 251
- Layers: U0, U1, U2, U3
- Edge types: 8 different kinds

**Generated DOT file**:
- U0 layer export: 397 lines
- Full graph: ~500+ lines
- Valid DOT format (verified with Graphviz)

**Benefits**:
- Visual understanding of specification structure
- Multi-layer relationships visible at a glance
- Helps identify patterns and anomalies
- Documentation and presentation ready
- Can be integrated into CI/CD for spec documentation

## Verification

Tested successfully:
- ✅ Basic export to file
- ✅ Layer filtering (--layer 0)
- ✅ Metadata inclusion (--metadata)
- ✅ Stdout output
- ✅ All 251 specifications rendered
- ✅ All edge types represented
- ✅ Valid DOT format

## Compliance

- ✅ CLAUDE.md: Smallest possible commit unit
- ✅ CLAUDE.md: Work recorded in tasks directory
- ✅ CLAUDE.md: No ad-hoc scripts (native Rust implementation)
- ✅ CLAUDE.md: Behavior verified through testing
- ✅ PROBLEM.md: Addresses graph visualization requirement

## Impact

This enhancement significantly improves the understanding and communication of the specification graph:
- **For users**: Visual representation of complex specification relationships
- **For documentation**: Graph diagrams can be generated automatically
- **For analysis**: Patterns and structure become visible
- **For presentation**: Professional visualization for explaining specORACLE

## Next Steps

Remaining visualization tasks (from PROBLEM.md):
- HTMLエクスポート（静的サイト生成）- Priority: Medium
- PDFエクスポート - Priority: Low

## Related

- Issue: PROBLEM.md - "仕様からドキュメントを生成・可視化できない"
- Files created: `spec-cli/src/commands/export_dot.rs`
- Files modified: `mod.rs`, `main.rs`, `dispatcher.rs`
- Session 68: Markdown export implementation (complementary feature)
