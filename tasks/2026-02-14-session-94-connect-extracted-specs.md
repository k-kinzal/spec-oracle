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

## Expected Outcome

- <20 isolated extracted specs (from 163)
- Meaningful U3→U0 connections
- Traceable multi-layer specifications
