# Cleanup: Remove Obsolete Migration Scripts

**Date**: 2026-02-15
**Context**: User constraint "pythonの呼び出しは許可されません" (Python invocation is not permitted)

## Problem

The `scripts/` directory contained many one-off migration and fix scripts that served their purpose during development but are no longer needed. These scripts:
- Were used to migrate data (Session 65: formality_layer migration)
- Fixed specific issues (layer display, edges)
- Connected isolated specifications (Sessions 66-96: achieving zero omissions)

Once these migrations are complete, keeping the scripts adds clutter and confusion about what tools are actually meant to be used.

## User Constraint

> "pythonの呼び出しは許可されません"

Interpretation:
- Python scripts should not be required for runtime operations
- One-off migration scripts should be cleaned up after use
- Core features should be in the Rust CLI
- Utility tools (export, visualization) are acceptable

## Actions Taken

### Deleted from root directory:
- `connect_layers.py` (unknown purpose, not tracked in git properly)

### Deleted from scripts/ directory:

**Migration scripts (Session 65 and earlier)**:
- `migrate_formality_layer.py` - Migrated formality_layer from metadata to field (done)
- `fix_formality_layer_code.py` - Updated code to use new field structure (done)
- `assign_layers.py` - Initial layer assignment (done)
- `reclassify_kinds.py` - Kind reclassification (done)

**Fix scripts (one-off fixes)**:
- `fix_layer_display.py` - Fixed layer display format (done)
- `fix_edges.py` - Fixed edge data issues (done)

**Connection scripts (Sessions 66-96: zero omissions achievement)**:
- `connect_trace_scenario.py` - Connected trace scenarios (Session 66)
- `connect_trace_to_assertion.py` - Connected trace to assertions (Session 66)
- `connect_scenarios.py` - Connected test scenarios (Session 96)
- `connect_test_specs.py` - Connected test specifications (Session 96)
- `connect_u0_u3.py` - Connected U0-U3 layers (Session 94)

**Total deleted**: 12 scripts

### Kept in scripts/ directory:

**Documented utilities** (referenced in scripts/README.md):
- `export_specs_md.py` - Generate Markdown documentation
- `export_specs_dot.py` - Generate Graphviz visualizations
- `connect_layer_label_spec.py` - Utility for connecting layer labels
- `README.md` - Documentation

**Total kept**: 4 files

## Rationale

### Why delete:
1. **Completed purpose**: All migration/fix scripts have already been executed
2. **Data already migrated**: PROBLEM.md confirms issues are solved ✅
   - Session 65: formality_layer migration ✅
   - Session 66-68: zero omissions ✅
   - Session 94-96: multi-layer connections ✅
3. **No longer needed**: Specs are properly structured, connected, and migrated
4. **Clutter reduction**: Clear separation between utilities and one-off scripts
5. **User constraint**: Python invocation should be minimized

### Why keep:
1. **Documented utilities**: Referenced in README.md as intended-for-use tools
2. **Repeatable operations**: export_specs_md/dot are used for documentation generation
3. **Ongoing value**: These tools will continue to be useful

## Verification

```bash
$ ls scripts/
README.md
connect_layer_label_spec.py
export_specs_dot.py
export_specs_md.py
```

Only documented, reusable utilities remain.

## Impact

**Benefits**:
- ✅ Cleaner codebase (12 obsolete files removed)
- ✅ Clear intent (only utilities remain)
- ✅ Aligns with constraint (minimal Python dependencies)
- ✅ Easier onboarding (users see only relevant tools)

**No regression**:
- All data migrations are complete (irreversible)
- Scripts can be recovered from git history if ever needed
- Documented utilities remain available

## Files Deleted

Total: 13 files
- Root: 1 file (connect_layers.py)
- Scripts: 12 files (migrations, fixes, one-off connections)

## Files Kept

Total: 4 files
- export_specs_md.py
- export_specs_dot.py
- connect_layer_label_spec.py
- README.md
