# Session 69: Graph Visualization Export (2026-02-14)

## Goal

Add graph visualization capabilities to specORACLE to address the partial completion of "仕様からドキュメントを生成・可視化できない" issue in PROBLEM.md.

## Problem Statement

From PROBLEM.md (High priority):
- ✅ Markdown export implemented (Session 68)
- ⏳ **Graph visualization pending**
- Users need to visualize specification relationships and structure
- DOT/Graphviz format enables professional graph rendering

## Implementation

### Created `export_specs_dot.py`

**Location**: `scripts/export_specs_dot.py`

**Features**:
1. **DOT graph format generation**
   - Exports to Graphviz DOT format
   - Supports all Graphviz layout engines (dot, neato, fdp, sfdp, circo, twopi)

2. **Visual encoding**
   - Nodes color-coded by kind:
     - Assertion: Light blue (#E3F2FD)
     - Constraint: Light orange (#FFF3E0)
     - Scenario: Light green (#F1F8E9)
     - Definition: Light pink (#FCE4EC)
     - Domain: Light purple (#F3E5F5)
   - Node borders color-coded by layer:
     - U0: Blue (#BBDEFB)
     - U1: Green (#C8E6C9)
     - U2: Orange (#FFE0B2)
     - U3: Pink (#F8BBD0)

3. **Edge styling**
   - Formalizes: Blue, normal
   - Refines: Green, normal
   - DerivesFrom: Purple, dashed
   - DependsOn: Orange, dotted
   - Synonym: Grey, dashed
   - Relates: Black, solid

4. **Filtering options**
   - `--layer N`: Filter by formality layer (0-3)
   - `--kind TYPE`: Filter by specification kind
   - `--max-content N`: Limit node content length (default: 50)
   - `--layout ENGINE`: Choose Graphviz layout engine

5. **Statistics**
   - `--stats`: Print graph statistics instead of DOT output

### Documentation

Updated `scripts/README.md` with:
- Comprehensive usage examples
- Filtering options
- Layout engine descriptions
- Graphviz installation instructions
- Visual feature documentation

### Generated Examples

**Created in `docs/graphs/`**:
- `u0_layer.dot`: U0 layer visualization (70 nodes)
- `constraints.dot`: All constraint specifications (28 nodes)

### Dogfooding

Added 4 specifications to `.spec/specs.json`:
1. `[ea15885e]` - DOT export capability
2. `[6b8373d8]` - Filtering support
3. `[250c2181]` - Node color encoding
4. `[39df83fe]` - Edge styling

All set to U0 layer (natural language requirements).

## Usage Examples

```bash
# Generate full graph
python3 scripts/export_specs_dot.py > docs/graphs/full.dot

# Render to PNG (requires graphviz)
dot -Tpng docs/graphs/full.dot -o docs/graphs/full.png

# U0 layer only
python3 scripts/export_specs_dot.py --layer 0 > docs/graphs/u0.dot

# Constraints only, shorter labels
python3 scripts/export_specs_dot.py --kind constraint --max-content 30 > docs/graphs/constraints.dot

# Statistics
python3 scripts/export_specs_dot.py --stats
# Output:
# Total Nodes: 127
# Total Edges: 113
# By Layer: U0: 74, U1: 1, U2: 37, U3: 15
# By Kind: Assertion: 93, Constraint: 28, Scenario: 6
```

## Verification

```bash
$ ./target/release/spec check
✅ All checks passed! No issues found.

$ python3 scripts/export_specs_dot.py --stats
Total Nodes: 127
Total Edges: 113

By Layer:
  U0: 74
  U1: 1
  U2: 37
  U3: 15

By Kind:
  Assertion: 93
  Constraint: 28
  Scenario: 6
```

## Impact on PROBLEM.md

Updated issue status:
- **仕様からドキュメントを生成・可視化できない**: Now 🔄 **部分的に解決**
  - ✅ Markdown export (Session 68)
  - ✅ **DOT graph visualization (Session 69)**
  - ⏳ Remaining: HTML export, PDF export (優先度中)

## Files Modified

- Created: `scripts/export_specs_dot.py` (254 lines)
- Created: `scripts/set_graph_viz_layer.py` (utility)
- Modified: `scripts/README.md` (+67 lines documentation)
- Modified: `.spec/specs.json` (+4 specifications)
- Created: `docs/graphs/u0_layer.dot`
- Created: `docs/graphs/constraints.dot`

## Next Steps

1. ✅ Graph visualization implemented
2. Consider: Online visualization (no Graphviz installation required)
3. Consider: Interactive HTML export with D3.js
4. Consider: PDF generation pipeline

## Session Metrics

- Time: ~15 minutes
- Specifications added: 4
- Code lines: ~254 (Python script)
- Documentation lines: ~67 (README update)
- Total specifications: 127 nodes, 113 edges
- Health: 0 contradictions, 0 omissions ✅
