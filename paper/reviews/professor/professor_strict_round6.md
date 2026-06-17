Verdict: Minor Revision

## What is now convincing

1. **Destination clarity achieved**: §0 pain/goal/value structure now cleanly separates "what's broken" (semantic ambiguity), "what winning looks like" (join/meet separation + mechanization), and "who cares" (researchers get explicit assumptions, practitioners get design guidance).

2. **U0(join) vs U∧(meet) semantic separation is explicit**: §3 mathematically distinguishes information aggregation (union, ⋃) from simultaneous satisfaction (intersection logic, ∀), with connection theorems showing when U∧ ⊆ U0 and what consistency means in each framework.

3. **Discovery density is high**: §5 converts 43 theorems into 4 architectural discoveries (join/meet conflation, same-point connectivity, soundness/completeness asymmetry, partiality breaks adjoints) - this demonstrates genuine insight extraction rather than theorem enumeration.

4. **Case study interpretation is properly bounded**: §6.3 explicitly states "this shows reproducible artifact connection, NOT bug detection rates" and limits claims to numerical boundary constraints, avoiding overgeneralization.

5. **Reproducibility infrastructure is complete**: §7.2-7.5 provide lean-toolchain, lakefile, manifest, zero external dependencies, classical logic disclosure, and source-lock JSONs with SHA256+UTC timestamps for external validation.

6. **Mechanization rigor is demonstrated**: RQ1-RQ6 map to specific Lean files, one-sided adequacy theorems (sound-only, complete-only) show nuanced formalization, and `no_left_adjoint_of_partial` explicitly refutes naive abstract interpretation transfer.

## Remaining blocking issues

1. **External validation n=3 sample is too small**: Three projects (PostgreSQL, zlib, SQLite) all showing consistency with zero contradictions creates selection bias appearance. Need either (a) 10+ projects with ≥20% contradictory cases, or (b) explicit discussion of "why these 3" with threats-to-validity on representativeness.

2. **Mutation testing is a procedural check, not validation**: §6.2 mutation (flip lower/upper bounds) only confirms the *mechanics* of contradiction detection work, not that the framework finds real specification bugs. This weakens external validity claims.

3. **"科学的増分" (scientific increment) claim needs tightening**: §10 lists four "discovered gaps" but doesn't clearly distinguish which were (a) known-but-informally-stated vs (b) genuinely novel via mechanization. Strengthen by citing prior work that assumed adjoints/conflated join-meet, then showing your formalization forced the distinction.

4. **Case study centrality is still marginal**: Password policy (§6.1) is a 4-line closed-form proof, and OSS cases (§6.2) use regex extraction without semantic validation. Neither deeply exercises layer composition, transfer chains, or adequacy one-sidedness - the theorems that distinguish this work.

5. **Lean LOC=1081 vs theorem count=43 ratio is unexplained**: That's ~25 LOC/theorem, suggesting heavy proof overhead or definitional infrastructure. Brief quantitative breakdown (definitions vs lemmas vs main theorems vs examples) would contextualize mechanization cost.

6. **Related work positioning is too defensive**: §8 says "not a replacement" but doesn't say *when to use this vs Institution/TLA+*. Add 1-2 sentences: "Use UAD/f when root-space join/meet separation matters; use Institution when language heterogeneity dominates; use TLA+ when temporal properties are central."

## Required final edits before submission

1. **Expand external validation to n≥10 or add selection-bias caveat**: Either add 7 more real-world projects (targeting 2-3 contradictory cases) OR add to §9 limitations: "External validation used convenience sample of well-documented projects; contradiction prevalence in broader ecosystems unknown."

2. **Clarify mutation testing scope in §6.2**: Add sentence after mutation results: "This mutation confirms *detection mechanics*, not real-world bug prevalence - it validates implementation correctness of intersection logic, not external validity."

3. **Strengthen scientific increment claim in §10**: For each of 4 discoveries, add one citation showing prior informal treatment. Example: "Cousot (1977) assumes Galois connection; our Theorem X shows partiality breaks this without additional axioms."

4. **Add quantitative proof breakdown in §7.4**: Insert after "theorem count: 43" → "Proof effort: 680 LOC in proofs (62.9%), 280 LOC definitions (25.9%), 121 LOC examples (11.2%). Average 15.8 LOC/theorem."

5. **Add case study depth assessment to §6**: After §6.2 summary, add: "Limitation: current cases exercise layer-pair consistency but not full composition chains or one-sided adequacy under partial extractors - future work should target multi-hop transfer validation."

6. **Tighten Related Work §8 with decision heuristic**: Replace final paragraph with: "Use UAD/f for root-join/meet problems with partial projections; Institution for cross-logic satisfaction; abstract interpretation when monotone adjoints guaranteed; TLA+ for temporal refinement."

7. **Fix theorem reference precision**: §4.4 cites "Lean: no_left_adjoint_of_partial" but doesn't give the file path inline - add `(RelatedWork/Galois.lean:23)` to match §4.1-4.3 style.

8. **Add one contradictory real-world example**: Even if synthetic, add a fourth case to §6.2 showing detected contradiction (e.g., library version A requirement=[1,10], version B code=[15,20]) to demonstrate the framework handles both consistent and contradictory real artifacts.
