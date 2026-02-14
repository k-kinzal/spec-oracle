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

## See Also

- `../docs/specifications.md` - Generated specification documentation
- `../.spec/specs.json` - Source specification data
- `../PROBLEM.md` - Known issues and resolutions
