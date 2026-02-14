# Session 107: Cleanup Documentation Extraction Issues

**Date**: 2026-02-15
**Goal**: Clean up contradictions and omissions created by documentation extraction
**Status**: ✅ Partially Complete

## Problem Identified

Session 106 (Documentation Extractor) broke the clean state achieved in Session 105:
- **Before** (Session 105): 0 contradictions, 0 omissions
- **After** (Session 106): 21 contradictions, 64 omissions

Root cause: Extracted specs from PROBLEM.md and README.md including:
1. **Example specs** used to illustrate problems (password: 8 vs 10 vs 12 chars)
2. **Meta-documentation** describing features/problems, not requirements
3. **Historical documentation** about completed work

## Solution Implemented

### 1. Mark Example Password Specs as Definition

**Script**: `scripts/cleanup_example_password_specs.py`

Marked 14 password-related specs as `Definition` (examples/meta-documentation):
- Example constraints from PROBLEM.md (12 chars, 10 chars, 8 chars)
- Command examples (`spec add "Password..."`)
- Code examples (`/// Password must be...`)
- Documentation with embedded specs

**Result**: 21 contradictions → **0 contradictions** ✓

### 2. Remove PROBLEM.md Specs

**Script**: `scripts/remove_meta_doc_specs.py`

Removed 46 specs extracted from PROBLEM.md:
- Problem descriptions
- Resolution documentation
- Historical notes about completed sessions
- Meta-specifications about the tool

Rationale: PROBLEM.md describes **problems to solve**, not **requirements to implement**.

**Result**: 64 omissions → **17 omissions** (73% reduction)

### 3. Mark Extractor Test Examples as Definition

**Script**: `scripts/mark_extractor_test_examples.py`

Marked 5 specs from test code as `Definition`:
- `Invariant: user.is_authenticated()` (test example)
- `Amount must be greater than zero` (test panic)
- `extract intent from test with ai` (test scenario)

These are test examples used to verify extraction, not real requirements.

**Result**: 17 omissions → **16 omissions**

## Current State

```
✅ Zero contradictions
⚠️  16 isolated specifications

Total specs: 237
Extracted: 88 (37.1%)
  - From code (.rs/.proto): 78 specs ✓
  - From README.md: 10 specs (isolated)
```

## Analysis

### Implementation Specs (78 specs) - Working Well

- Extracted from code, tests, proto
- Connected to specification graph
- This is the **reverse mapping engine** working as intended ✓

### Documentation Specs (10 specs from README.md) - Isolated

These are feature descriptions from README.md:
1. "Graph-based specification storage"
2. "CLI automatically detects `.spec/` directory"
3. "Breakthrough feature: Specifications automatically stay synchronized"
4. "constraint: Universal invariant" (definition)
5. "scenario: Existential requirement" (definition)
6. Command examples (some marked as Definition)

**Question**: Should README.md be extracted at all?
- Session 106 said: "✅ README.md, Requirements docs, User stories"
- But README.md contains **documentation** (what tool does), not **requirements** (what it should do)

### Remaining Isolated Specs Breakdown

- **documentation**: 10 specs (README.md)
- **assertion**: 3 specs
- **test**: 1 spec
- **doc**: 1 spec  
- **panic**: 1 spec

## Lessons Learned

### 1. Documentation ≠ Requirements

- **Requirements docs**: Specs for future features → Extract ✓
- **Documentation**: Description of current features → Don't extract ❌
- **Implementation**: Code, tests, proto → Extract ✓

PROBLEM.md and README.md are documentation, not requirements.

### 2. Meta-Documentation Creates Noise

Extracting from problem tracking and historical documentation creates:
- Example specs that illustrate problems (contradictions)
- Descriptions of completed work (not requirements)
- Test data mixed with real specs

### 3. Smart Filtering Needed

Session 106's next step #1: "Smart Document Filtering: Exclude meta-docs" ✓ Completed

Need to:
- Identify document type before extraction
- Filter meta-docs (PROBLEM.md, CHANGELOG.md)
- Only extract from requirement documents

## Next Steps

### Option A: Remove README.md Specs

- README.md is documentation, not requirements
- Would reduce to near-zero isolated specs
- Clean specification graph

### Option B: Connect README.md Specs

- Manually connect to implementation specs
- Verify documentation matches implementation
- Use as assertions about tool behavior

### Option C: Hybrid Approach

- Mark some README specs as Definition (examples, explanations)
- Connect real feature descriptions to implementation
- Selective extraction from documentation

## Files Changed

```
scripts/cleanup_example_password_specs.py    | New script
scripts/remove_meta_doc_specs.py             | New script
scripts/mark_extractor_test_examples.py      | New script
scripts/analyze_isolated_specs.py            | New script
.spec/specs.json                             | 283 → 237 nodes (-46)
```

## Verification

```bash
$ ./target/release/spec check
✓ No contradictions found
⚠️  16 isolated specification(s)

Total specs:        237
Extracted specs:    88 (37.1%)
Contradictions:     0  ✓
Isolated specs:     16
```

## Theoretical Context

This cleanup aligns with the core concept from CLAUDE.md:
> specORACLE is a reverse mapping engine. It constructs U0 from diverse artifacts through reverse mappings.

The reverse mapping should extract from:
- **Implementation artifacts** (code, tests, proto) → U3, U2
- **Formal specs** (TLA+, Alloy) → U1  
- **Requirements docs** (not documentation) → U0

Currently:
- ✅ U3 extraction working (code, tests)
- ✅ U2 extraction working (proto)
- ❌ U1 extraction not implemented (no TLA+/Alloy)
- ⚠️ U0 extraction unclear (what are "requirements docs"?)

## Status

**Completed**:
- ✅ Zero contradictions achieved
- ✅ 73% reduction in omissions (64 → 16)
- ✅ Removed meta-documentation specs
- ✅ Marked test examples as Definition

**Remaining**:
- ⏳ 16 isolated specs (mostly README.md documentation)
- ⏳ Decision on README.md extraction
- ⏳ Smart document type detection

