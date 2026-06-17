VERDICT: OK

## Overview
The manuscript claims match the implementation and JSON outputs. No major blockers found. The core claims about deterministic replay (RQ6), three-value judgement (§6.2), and mutation detection are verified.

## Minor Suggestions

### 1. Clarify "Lean LOC" counting basis
**Location**: §7.4  
**Current**: "Lean LOC (paper/lean/UadfU0): 1502"  
**Issue**: The manuscript states "1502" but doesn't specify whether this includes blank lines, comments, or imports.  
**Suggestion**: Add footnote: "LOC counted via `wc -l` (includes blank lines and comments)."

### 2. Make mutation criterion more visible in main text
**Location**: §6.2  
**Current**: Mutation detection criteria are detailed in the table but not explicitly restated in the running text.  
**Suggestion**: Before the mutation results table, add: "Mutation detection uses two fixed criteria: (i) `judgement == contradictory` for stale lower bounds, (ii) `upper' <= floor(upper/2)` for unit mismatch."

### 3. Add cross-reference to negative example from §4.7
**Location**: §6.4 (negative example)  
**Current**: "§4.7 の理論選択を実装ポリシーへ写像できる"  
**Suggestion**: Add backward reference: "This demonstrates the must/may policy separation formalized in §4.7 and implemented as `apply_none_policy` (§11.2)."

### 4. Strengthen the "convenience sample" disclosure
**Location**: §6.2 (sampling statement)  
**Current**: Multiple mentions but scattered.  
**Suggestion**: Add upfront summary box after §6.2 title:
> **Sample scope**: `n=3` convenience sample (PostgreSQL, zlib, SQLite). Selection criteria: public 3-layer docs, numeric bounds, fixed URL. Not representative of general contradiction rates.

### 5. Clarify "parse_issue" vs "none" propagation
**Location**: §6.2 (extraction mode)  
**Current**: The JSON shows `has_parse_issue=false` everywhere but the graceful mode logs show parse failures.  
**Suggestion**: Add explicit note: "Baseline run (fail-fast) exits on first parse failure. Graceful mode propagates parse failures as `none`, recorded in `parse_issues`. The baseline JSON shows zero parse issues because extraction succeeded for all three projects under offline replay."
