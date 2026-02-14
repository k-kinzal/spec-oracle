# Session 68 Part 2: Documentation Generation

**Date**: 2026-02-14
**Status**: ✅ Completed

## Objective

Implement human-readable documentation generation from specifications to address
the PROBLEM.md issue: "仕様からドキュメントを生成・可視化できない"

## Background

After achieving zero omissions in Session 68 Part 1, the next priority was to make
specifications more accessible and shareable. Specifications stored in `.spec/specs.json`
are difficult for humans to read, review, and share with stakeholders.

## Problem

From PROBLEM.md:
- Specifications locked in graph database (JSON format)
- Difficult to share with team members
- Cannot review specification changes in PR
- Hard to understand overall specification structure

## Solution

Created a Python script to export specifications to Markdown format without modifying
the CLI (minimal changes approach).

### Implementation

**Script**: `scripts/export_specs_md.py`

Features:
1. **Layer-based organization**: Group by U0, U1, U2, U3
2. **Kind-based grouping**: Assertion, Constraint, Scenario
3. **Filtering options**:
   - `--layer <N>`: Filter by formality layer (0-3)
   - `--kind <type>`: Filter by specification kind
   - `--with-edges`: Include relationship information
4. **Rich output**:
   - Full specification content
   - Metadata and timestamps
   - Short IDs for easy reference
   - Incoming/outgoing edges (optional)
5. **Summary statistics**:
   - Total specifications and edges
   - Distribution by layer
   - Distribution by kind

### Documentation

**Script README**: `scripts/README.md`
- Usage examples
- Output format explanation
- Command-line options

**Generated Documentation**: `docs/specifications.md`
- 938 lines
- All 123 specifications
- Organized and human-readable

## Usage Examples

```bash
# Export all specifications
python3 scripts/export_specs_md.py > docs/specifications.md

# Export only U0 (natural language requirements)
python3 scripts/export_specs_md.py --layer 0 > docs/u0-requirements.md

# Export only constraints
python3 scripts/export_specs_md.py --kind constraint > docs/constraints.md

# Include relationship information
python3 scripts/export_specs_md.py --with-edges > docs/specs-with-edges.md
```

## Results

### Generated Documentation Sample

```markdown
## U0 (Natural Language Requirements)

### Constraint (10 specs)

#### 1. [81afa3f5] The system must detect contradictions between specifications...

- **ID**: `81afa3f5-4a41-4b04-b958-224d1037d76f`
- **Created**: 2026-02-14 18:10:08
```

### Statistics

From generated `docs/specifications.md`:
- **Total Specifications**: 123
- **Total Edges**: 113
- **By Layer**:
  - U0: 70 specifications
  - U1: 1 specification
  - U2: 37 specifications
  - U3: 15 specifications
- **By Kind**:
  - Assertion: 89
  - Constraint: 28
  - Scenario: 6

## Impact

✅ **Benefits**:
1. **Human-readable format**: Easy to read and understand
2. **PR reviewability**: Can review specification changes in pull requests
3. **Stakeholder sharing**: Export to PDF, share with non-technical stakeholders
4. **Documentation baseline**: Can be committed to Git, versioned
5. **Filtering flexibility**: Generate targeted documentation (e.g., only U0 requirements)

✅ **Resolves PROBLEM.md issue** (partial):
- ✅ Markdown/HTML generation
- ✅ Layer-based organization
- ✅ Kind-based summary
- ✅ Timestamp/timeline information
- ⏳ Graph visualization (future work)

## Design Decisions

### Why Python script instead of CLI command?

1. **Minimal changes**: Avoids modifying the large `spec-cli/src/main.rs` (3507 lines)
2. **Rapid iteration**: Python easier to modify and extend
3. **Zero dependencies**: Uses only standard library
4. **Flexibility**: Easy to customize output format
5. **Separation of concerns**: Documentation generation is a separate concern from core CLI

### Why Markdown format?

1. **Universal**: Supported by GitHub, GitLab, documentation tools
2. **Human-readable**: Plain text, easy to read and edit
3. **Convertible**: Can convert to HTML, PDF, etc. using pandoc
4. **Git-friendly**: Diffable, reviewable in PRs
5. **Widely adopted**: Standard for technical documentation

## Remaining Work (PROBLEM.md)

From the original issue, still to be implemented:
- ⏳ Graph visualization (DOT/Graphviz format)
- ⏳ HTML export (static site generation)
- ⏳ PDF export (direct generation)

These can be added as separate scripts or CLI commands in future sessions.

## Files Changed

1. **`scripts/export_specs_md.py`** (new): Main export script
2. **`scripts/README.md`** (new): Documentation for scripts
3. **`docs/specifications.md`** (new): Generated documentation
4. **`PROBLEM.md`** (updated): Mark issue as partially resolved

## Technical Details

### Script Architecture

```python
def main():
    # Load specs.json
    # Index nodes by ID
    # Group by layer and kind
    # Apply filters (--layer, --kind)
    # Generate Markdown output
    # Add summary statistics
```

### Edge Information Format

When `--with-edges` is used:
```markdown
- **Relationships**:
  - **Incoming**:
    - [8a79071d] --Formalizes--> this spec
  - **Outgoing**:
    - this spec --Refines--> [f6953636]
```

## Lessons Learned

1. **Simple solutions work**: Python script provides 80% value with 20% effort
2. **Markdown is powerful**: Rich enough for technical docs, simple enough for humans
3. **Filtering is essential**: 123 specs too many to view at once
4. **Statistics matter**: Summary gives quick overview of specification landscape

## Next Steps

Potential enhancements:
1. **Graph visualization**: `export_specs_dot.py` for Graphviz
2. **HTML export**: `export_specs_html.py` with navigation
3. **Search**: Add full-text search to HTML export
4. **Diff**: Compare specifications between versions

## References

- PROBLEM.md: High priority issue "仕様からドキュメントを生成・可視化できない"
- Session 68 Part 1: Zero omissions achievement
- `docs/specifications.md`: Generated documentation example
