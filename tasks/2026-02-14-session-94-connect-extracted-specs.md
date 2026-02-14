# Session 94: Connect Extracted Specifications to Graph

## Problem

After Session 93 extraction implementation, we have:
- 305 total specifications
- 178 extracted specifications (metadata.inferred=true)
- **163 isolated extracted specs (91.6% disconnected!)**
- Only 15 extracted specs have edges

## Root Cause

The extraction pipeline (`spec extract`) creates specifications but doesn't automatically connect them to existing specifications in the graph. The `ingest()` function is not creating sufficient edges.

## Goal

Connect extracted specifications to existing specifications through automatic relationship inference:
1. Extracted U3 specs should connect to U0 specs via "Formalizes" edges
2. Related extracted specs should connect to each other
3. Achieve <10% isolated rate for extracted specs

## Current State

```bash
$ python3 -c "
import json
with open('.spec/specs.json') as f:
    data = json.load(f)
inferred_indices = [i for i, n in enumerate(data['graph']['nodes'])
                    if n.get('metadata', {}).get('inferred') == 'true']
connected = set()
for edge in data['graph']['edges']:
    if edge[0] in inferred_indices: connected.add(edge[0])
    if edge[1] in inferred_indices: connected.add(edge[1])
print(f'Inferred: {len(inferred_indices)}, Connected: {len(connected)}, Isolated: {len(inferred_indices) - len(connected)}')
"

Inferred: 178, Connected: 15, Isolated: 163
```

## Implementation Plan

1. Enhance `graph.ingest()` to create semantic edges:
   - Use AI to match extracted specs to existing specs
   - Create "Formalizes" edges from U3→U0
   - Create "Refines" edges between related specs

2. Implement batch edge creation:
   - Process all extracted specs at once
   - Use embedding similarity for matching
   - Set confidence threshold (>0.7)

3. Add `spec connect` command:
   - Manually trigger edge inference
   - `spec connect --auto` for all isolated specs

## Implementation

### Phase 1: Enhance `spec check` (User Feedback) ✅

Fixed the need for jq/python3:
- Show extracted specs breakdown by extractor type
- Display: assertion (102), test (106), function_name (14), doc (1)
- Total specs and percentage calculations

### Phase 2: Connect U0→U3 (Semantic Matching) ✅

Created `scripts/connect_u0_u3.py`:
- Keyword-based semantic matching
- Domain-specific boosts (command→function mapping)
- Threshold: 0.5 confidence
- Result: +7 Formalizes edges (U0→U3)

**Impact**:
- Before: 20/74 U0 specs had U3 connections (27%)
- After:  24/74 U0 specs have U3 connections (32.4%)
- Improvement: +4 connected U0 specs

## Next Steps

Remaining challenges:
1. **50 U0 specs still lack U3 connections** (67.6%)
   - Need AI-enhanced matching or manual review
   - Or implement U2 extraction to bridge the gap

2. **223 isolated specs** (mostly test assertions)
   - Many are low-value (test-specific assertions)
   - Focus on high-value: doc comments, function names

3. **U2 layer extraction** (PROBLEM.md High priority)
   - Proto/gRPC interface extraction
   - Would create U0→U2→U3 chains
