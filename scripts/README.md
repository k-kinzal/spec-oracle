# specORACLE Scripts

Utility scripts for working with specORACLE specifications.

## Documentation Export

### `export_specs_md.py`

Generate human-readable Markdown documentation from specifications.

**Basic Usage:**
```bash
# Export all specifications
python3 scripts/export_specs_md.py > docs/specifications.md

# Export only U0 (natural language) specifications
python3 scripts/export_specs_md.py --layer 0 > docs/u0-requirements.md

# Export only constraints
python3 scripts/export_specs_md.py --kind constraint > docs/constraints.md

# Include relationship information
python3 scripts/export_specs_md.py --with-edges > docs/specs-with-edges.md
```

**Output Format:**
- Organized by formality layer (U0-U3)
- Grouped by specification kind (Assertion, Constraint, Scenario)
- Includes metadata, timestamps, and IDs
- Optional edge/relationship information
- Summary statistics at the end

**Example Output:**
```markdown
## U0 (Natural Language Requirements)

### Constraint (10 specs)

#### 1. [81afa3f5] The system must detect contradictions...

- **ID**: `81afa3f5-4a41-4b04-b958-224d1037d76f`
- **Created**: 2026-02-14 18:10:08
```

### `export_specs_dot.py`

Generate DOT graph format for visualization with Graphviz.

**Basic Usage:**
```bash
# Generate DOT file for all specifications
python3 scripts/export_specs_dot.py > specs.dot

# Render to PNG (requires graphviz)
dot -Tpng specs.dot -o specs.png

# Render to SVG
dot -Tsvg specs.dot -o specs.svg

# Interactive visualization
dot -Tx11 specs.dot
```

**Filtering Options:**
```bash
# Export only U0 layer
python3 scripts/export_specs_dot.py --layer 0 > u0_specs.dot

# Export only constraints
python3 scripts/export_specs_dot.py --kind constraint > constraints.dot

# Limit content length in nodes
python3 scripts/export_specs_dot.py --max-content 30 > specs_short.dot

# Use different layout engine
python3 scripts/export_specs_dot.py --layout neato > specs_neato.dot
```

**Statistics:**
```bash
# Print graph statistics instead of DOT
python3 scripts/export_specs_dot.py --stats
```

**Layout Engines:**
- `dot` - Hierarchical (default, good for directed graphs)
- `neato` - Spring model (good for undirected graphs)
- `fdp` - Force-directed (good for large graphs)
- `sfdp` - Scalable force-directed (good for very large graphs)
- `circo` - Circular layout
- `twopi` - Radial layout

**Visual Features:**
- Color-coded nodes by kind (Assertion=blue, Constraint=orange, Scenario=green)
- Color-coded borders by layer (U0=blue, U1=green, U2=orange, U3=pink)
- Edge colors by relationship type (Formalizes=blue, Refines=green, etc.)
- Truncated content for readability
- Short IDs (8 chars) for reference

**Installing Graphviz:**
```bash
# macOS
brew install graphviz

# Ubuntu/Debian
sudo apt-get install graphviz

# Windows (via Chocolatey)
choco install graphviz
```

## Specification Connection

### `connect_layer_label_spec.py`

Connect isolated layer label specification to related implementations.

**Usage:**
```bash
python3 scripts/connect_layer_label_spec.py
```

Automatically creates Formalizes edges between specifications to maintain
graph connectivity and enable traceability.

## Requirements

- Python 3.6+
- No external dependencies (uses only standard library)
- Graphviz (optional, for rendering DOT files)

## See Also

- `../docs/specifications.md` - Generated specification documentation
- `../.spec/specs.json` - Source specification data
- `../PROBLEM.md` - Known issues and resolutions
