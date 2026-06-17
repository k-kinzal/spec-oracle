VERDICT: NG

## Blocking Issues

### 1. Manuscript Clarity Gaps (Major Revision Required)

**Problem**: The manuscript fails to establish a clear conceptual flow that readers can follow without extensive back-tracking.

Specific blocking points:
- **Section 0.1-0.2**: The "reverse mapping" concept is introduced metaphorically but never formally defined before being used throughout the paper. What exactly does "reverse mapping from artifacts to U0" mean operationally?
- **Section 2.1**: The notation table introduces `f_{0i}` and `proj_i` as if they are the same, but Section 2.6 reveals they are composed. This forward-reference structure forces readers to mentally reconstruct definitions.
- **Section 3**: The join/meet terminology is used before the `⊆` ordering is fixed in 3.3, creating ambiguity about what "join" means on first read.
- **Section 4.3**: Claims "抽象関係 `E` に対する一般結果" but readers encounter this without understanding what concrete `E` instances look like until Section 6.

**Why blocking**: A major-revision reviewer expects the manuscript to be self-contained and readable without constant forward-references. The current structure assumes readers already understand the model.

**Required fix**: Restructure Sections 0-4 to present concepts in dependency order:
1. Define `proj` composition (`obs ∘ extract`) upfront in Section 2.1
2. Move partial ordering fixation (Section 3.3) before join/meet introduction (Section 3.1-3.2)
3. Provide a concrete `E` example in Section 4.3 before the abstract theorems

---

### 2. Evaluation Claims Not Supported by Evidence

**Problem**: Section 6.2 claims "技術的再実行可能性" but the evidence shows implementation-specific regex brittleness, not technical reproducibility.

Specific gaps:
- **RQ6 scope shift**: The RQ states "実OSSアーティファクト抽出パイプラインの技術的再実行可能性を確保できるか" but the evaluation only demonstrates "same-input-same-output" via SHA256 locks, not "different-researcher-can-reproduce"
- **Section 6.4 negative case**: The regex drift example shows the system **breaks** when documentation changes phrase structure (`"inclusive"` → `"bytes"`), which directly contradicts "reproducibility"
- **Section 6.5 validity threats**: Lists "抽出一般性" and "ドキュメントドリフト" as threats, but these are not threats to RQ6—they **invalidate** the claim that the pipeline is technically reproducible

**Why blocking**: The paper conflates "deterministic replay from locked snapshots" with "reproducible extraction methodology". A conservative reviewer cannot accept RQ6 as answered when the negative case demonstrates fragility.

**Required fix**: Either:
1. Narrow RQ6 to "deterministic snapshot replay reproducibility" and remove claims about "技術的再実行可能性" of the extraction method, OR
2. Demonstrate that multiple researchers can extract the same constraints from **new** OSS versions (not locked snapshots)

---

### 3. Theoretical Claims Overstate Proof Scope

**Problem**: Section 4 presents theorems as "中核定理" but the theorems only hold under unverified assumptions.

Specific issues:
- **Section 4.1 `lifted_transfer`**: Assumes `hproj` (same-point connection) and `hA` (forward preservation), but the paper provides **no examples** where these assumptions are verified for real artifacts
- **Section 4.3 adequacy**: States "実抽出器への適用には抽出層の意味保存証明が別途必要" but then uses the theorems in Section 6.2 results without that proof—this is circular reasoning
- **Section 3.5 ideal root**: The `U*` theorems are explicitly marked as "仮定依存" but the abstract and introduction imply these are proven results

**Why blocking**: A major-revision reviewer expects theorems to be applied only where their assumptions are verified. The manuscript uses unverified theorems to support PoC claims.

**Required fix**: Add a table showing:
- For each theorem in Section 4
- Which assumptions it requires
- Which artifacts in Section 6 verify those assumptions
- Which results rely on unverified assumptions (and mark them as "subject to validation")

---

## Secondary Issues (Must Address for Acceptance)

### 4. Missing Related Work Connections

- **Institution theory**: You cite Goguen & Burstall but don't explain why their satisfaction condition translation doesn't solve your problem
- **BX literature**: You cite partial BX but don't position against hippocratic laws or lens frameworks
- **Requirements traceability**: Zero references to ECSS-E-ST-10-06C or ISO/IEC/IEEE 29148 despite targeting multi-layer requirement management

### 5. N=3 Sample Not Justified

- Section 6.2 states "convenience sample" but doesn't explain **why** these 3 projects instead of a stratified sample across domains (embedded, web, scientific computing)
- The "数値境界制約" limitation is acknowledged but not defended—why not include one temporal constraint or one structural constraint as feasibility check?

### 6. Lean Mechanization Not Leveraged

- 1502 LOC of Lean code but only 59 theorems—suggests heavy example code
- No discussion of **why** Lean instead of Coq/Isabelle/Agda for this domain
- No comparison to existing mechanizations (e.g., CompCert's specification layers)

---

## Verdict Justification

This manuscript addresses an important problem (multi-layer specification consistency) with a novel approach (root coverage baseline via projection inverses). However, **as a major-revision submission**, it fails on:

1. **Readability**: The forward-reference structure makes it inaccessible to readers unfamiliar with the authors' prior work
2. **Correctness**: The evaluation claims (RQ6 reproducibility) are contradicted by the negative case evidence
3. **Reproducibility**: The theorems are applied to artifacts without verifying their assumptions

A major-revision reviewer would **not recommend acceptance** until these structural issues are resolved.

---

**Path to Acceptance** (for authors):
1. Rewrite Sections 0-4 in dependency order (no forward-references)
2. Downscope RQ6 to "snapshot replay" or add 3 new-version extraction validations
3. Add assumption-verification table linking theorems to artifacts
4. Expand related work to show non-overlap with Institution/BX/traceability
5. Justify N=3 with negative-case-diversity argument or expand to N=6
