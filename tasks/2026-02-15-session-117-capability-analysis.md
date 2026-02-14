# Session 117: Capability Analysis - Understanding specORACLE through specORACLE

## Goal
Use specORACLE to analyze itself and understand:
1. What features it currently has
2. What it was designed to do (from specifications)
3. Gaps between design and implementation
4. The essence of what specORACLE should resolve

## Current State Analysis

### Specifications Overview
- **Total specs**: 229
- **Extracted specs**: 75 (32.8%)
- **Contradictions**: 0
- **Isolated specs**: 0
- **Status**: All checks passed ✅

### Core Capabilities (from specifications)

#### 1. Reverse Mapping Engine (逆写像エンジン)
**Design** (from CLAUDE.md):
```
Code, Tests, Docs, Proto, Contracts, Types, TLA+ → [f₀ᵢ⁻¹] → U0
```

**Implementation Status**:
- ✅ f₀₃⁻¹: Code extraction (RustExtractor)
- ✅ f₀₂⁻¹: Proto extraction (ProtoExtractor)
- ✅ f₀₁⁻¹: Documentation extraction (partial)
- ⏳ Contract extraction (未実装)
- ⏳ Type extraction (未実装)
- ⏳ TLA+ extraction (未実装)

**Specifications**:
- [e33e97b5]: "The reverse mapping engine is verified as functional"
- [ac78bcec]: "Extraction engine must maintain idempotency"
- [98e02ebd]: "Cross-layer edge inference uses layer-aware similarity"

#### 2. Multi-Layer Defense Coordination
**Design** (from motivation.md):
> Modern software development relies on layered defenses (tests, contracts, properties, and formal methods) to ensure correctness. But when each layer evolves independently, global consistency becomes hard to maintain.

**Implementation Status**:
- ✅ U0-U3 layer tracking
- ✅ Cross-layer contradiction detection
- ✅ Layer inconsistency detection
- ✅ Formal verification (Z3 SMT solver)
- ⏳ Property-based test integration (未実装)
- ⏳ Contract verification integration (未実装)

**Specifications**:
- [717b4b00]: "verify-layers command checks multi-layer specification consistency"
- [0dc100e8]: "verify-layers provides formal verification"

#### 3. Self-Governance
**Design** (from CLAUDE.md):
> specORACLE is a reverse mapping engine. It does not manage specifications written by humans. It constructs U0 (the root specification) from diverse artifacts through reverse mappings.

**Implementation Status**:
- ✅ Self-specification management (229 specs)
- ✅ Self-contradiction detection (0 contradictions)
- ✅ Architectural violation detection (Session 115)
- ✅ Architectural correction (Session 116)
- ✅ Essence realization (Session 109)

**Specifications**:
- [5e3afc70]: "specORACLE must use itself to govern its own development"
- [de2d7a5a]: "The essence of specORACLE governance is REALIZED"

#### 4. Detection Capabilities
**Implementation Status**:
- ✅ Contradiction detection (with Z3 formal proof)
- ✅ Omission detection (isolated specs)
- ✅ Layer inconsistency detection
- ✅ Potential synonym detection
- ✅ Inter-universe inconsistency detection

**Specifications**:
- [81afa3f5]: "System must detect contradictions"
- [c8f23449]: "System must detect omissions"
- [448066d8]: "detect-contradictions uses formal prover"

## Gaps Analysis

### What specORACLE Should Resolve (from CLAUDE.md)
> Face the essence of specORACLE; the issues that should be resolved with specORACLE have not been addressed yet.

**Question**: What issues should be resolved?

### Hypothesis 1: Integration with Real Projects
specORACLE is managing its own specifications successfully, but:
- Is it being used to manage specifications for other projects?
- Can it integrate with existing test suites, contracts, property tests?
- Can it extract specifications from real-world codebases?

**Evidence**:
- PROBLEM.md mentions ztd-query-php project
- No integration examples in documentation
- No demonstration of managing external project specs

### Hypothesis 2: Completeness of Reverse Mapping
The reverse mapping engine is partially implemented:
- ✅ Code (Rust)
- ✅ Proto (gRPC)
- ⏳ Tests (partial - extracts test functions but not test assertions)
- ⏳ Contracts (Design by Contract - not implemented)
- ⏳ Property-based tests (not implemented)
- ⏳ Types (TypeScript, Flow - not implemented)
- ⏳ TLA+/Alloy (not implemented)

**Missing**: Full spectrum of "diverse artifacts" mentioned in CLAUDE.md

### Hypothesis 3: Multi-Layer Defense Coordination
From motivation.md:
> These are each correct individually, but when each layer focuses on itself, problems emerge in the whole.

**Current State**:
- specORACLE tracks specifications across layers (U0-U3)
- It detects contradictions and omissions
- BUT: Does it actually coordinate the layers?
- Does it ensure test coverage matches requirements?
- Does it verify that contracts align with specifications?

**Missing**: Active coordination mechanisms

### Hypothesis 4: Beyond Human-Written Specifications
From conversation.md (final insight):
> DSLが限界なのではない。人間がDSLを扱うことが限界である。

**The Paradigm Shift**:
- Humans should NOT write specifications in a DSL
- System should OBSERVE and EXTRACT specifications
- Specifications emerge from artifacts, not from human input

**Current State**:
- ✅ Extraction is implemented (RustExtractor, ProtoExtractor)
- ✅ Automatic relationship inference
- ⚠️  BUT: Users still use `spec add` to manually add specifications
- ⚠️  Manual specification input is still the primary workflow

**Question**: Should `spec add` be discouraged? Should extraction be the ONLY way?

## The Essence Question

From PROBLEM.md (Session 109):
> **本質の証明**:
> ```
> $ spec check
> ⚠️  1 contradiction(s) found
> Explicit contradiction edge 'meta-cli-violation-contradicts-separation'
> A: [d26341fb] The CLI architecture violates separation of concerns
> B: [b706e529] The CLI implementation must separate concerns
> ```
>
> **なぜこれが本質なのか**:
> - U0 (requirement): CLI must separate concerns
> - U3 (reality): CLI violates separation (4475 lines in main.rs)
> - **Governance in action**: specORACLE detects U3/U0 contradiction
> - これは失敗ではない - **システムが設計通りに機能している証拠**

**The Essence Realized**:
- specORACLE CAN detect its own violations
- specORACLE CAN extract architectural metrics from code
- specORACLE CAN compare U3 (implementation) to U0 (requirements)
- This IS the core concept working

**But...**:
- Session 116 fixed the violation (2172 lines → 531 lines)
- Now there are 0 contradictions
- Is this still demonstrating the essence?
- Or did we lose the demonstration by fixing it?

## Next Steps

### Investigation Needed
1. **Check if specORACLE is managing specifications for other projects**
   - Search for ztd-query-php specifications
   - Check if `.spec/` directories exist in other projects

2. **Verify multi-layer defense coordination**
   - Does specORACLE verify test coverage?
   - Does it check contract alignment?
   - Does it coordinate different verification methods?

3. **Understand the "beyond-DSL" paradigm**
   - Is manual `spec add` contradicting the vision?
   - Should extraction be the primary workflow?
   - What role should human input play?

4. **Assess completeness of reverse mapping**
   - What extractors are missing?
   - Can we implement contract extraction?
   - Can we implement property-based test extraction?

### Potential Tasks
- [ ] Implement contract extractor (Design by Contract)
- [ ] Implement property-based test extractor
- [ ] Demonstrate multi-project management
- [ ] Create integration examples
- [ ] Clarify role of manual vs extracted specifications

## The Critical Insight

### What specORACLE Was Designed to Solve

From `docs/motivation.md` (lines 9-24):
> 例えば、**ztd-query-php**プロジェクトを見ると、以下のような多層的な保証が行われています：
> - 契約（Design by Contract）: 事前条件・事後条件・不変条件
> - 性質検査（Property-Based Testing）: ランダム入力での性質検証
> - テスト（Unit/Integration/E2E）: 具体的な挙動の確認
> - 型システム: 静的な型安全性
> - Schema検証: データ構造の妥当性

**The Problem**: "各層にフォーカスして進めると、全体として問題が出る"
- E2Eテストは「8文字以上」を検証
- ドキュメントには「10文字以上推奨」
- **どれが正しいのか？**

### What specORACLE Is Actually Doing

**Current State**: specORACLE is managing its own specifications
- ✅ 229 specifications for spec-oracle itself
- ✅ 0 contradictions, 0 omissions
- ✅ Self-governance working

**But**: NO specifications for ztd-query-php
```bash
$ spec find "ztd-query"
No specifications found

$ find /Users/ab/Projects/ztd-query-php -name ".spec"
(no .spec directory exists)
```

### The Goal Not Reached

**CLAUDE.md says**:
> The goal has not been reached. Face the essence of specORACLE; the issues that should be resolved with specORACLE have not been addressed yet.

**The Essence**: specORACLE was designed to solve multi-layer defense coordination in **real projects like ztd-query-php**, but it's only managing itself.

## Conclusion

specORACLE has achieved:
- ✅ Self-governance (managing its own specs)
- ✅ Reverse mapping (code → specs, proto → specs)
- ✅ Formal verification (Z3 SMT solver)
- ✅ Essence realization (detecting and fixing violations)

**But the GOAL requires**:
- ❌ Managing specifications for ztd-query-php
- ❌ Coordinating multi-layer defenses in a real project:
  - Contracts (Design by Contract)
  - Property-based tests
  - Unit/Integration/E2E tests
  - Type system constraints
  - Schema validation
- ❌ Detecting contradictions across these layers
- ❌ Ensuring consistency when requirements change

## Next Steps

### Goal: Use specORACLE to manage ztd-query-php

1. **Initialize specORACLE for ztd-query-php**:
   ```bash
   cd /Users/ab/Projects/ztd-query-php
   spec init
   ```

2. **Extract specifications from ztd-query-php**:
   - Extract from PHP code (contracts, tests)
   - Extract from documentation
   - Extract from schema definitions

3. **Demonstrate multi-layer defense coordination**:
   - Show contradictions between layers
   - Show omissions (gaps in coverage)
   - Show how specORACLE coordinates the whole

4. **Prove the essence**:
   - specORACLE solves the problem it was designed for
   - Multi-layer defenses are coordinated
   - The goal is reached

**This is what "continue for goal" means**: Use specORACLE to solve real problems, not just manage itself.
