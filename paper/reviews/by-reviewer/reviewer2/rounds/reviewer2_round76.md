## Reviewer #2 Assessment — UAD/f Two-Operator Kernel under Partial Projections

---

### 1. Overall Recommendation

**Weak Accept / Minor Revision** for methodology/library-formalization tracks (FM, ITP, CPP, Formal Aspects). Not yet ready for theory-heavy main tracks (TACAS, FASE) without addressing the major concerns below.

The paper delivers what it promises: a compact, assumption-audited Lean4 mechanization kernel. The claim scoping is honest, the counterexample discipline is commendable, and the assumption matrix is a genuine artifact contribution. However, several issues need resolution before acceptance.

---

### 2. Strengths

1. **Honest claim framing.** The explicit §0.2 non-claims section and assumption matrix (Appendix) are exemplary. This is rare and valuable.

2. **Counterexample discipline.** `transfer_fails_without_hproj`, `EPlus1_not_complete`, and the empty-active vacuous-truth mechanization all demonstrate that theorem hypotheses are non-redundant. This raises the trust level of the positive results significantly.

3. **Axiom disclosure.** Per-theorem `#print axioms` reporting in §4.3 is thorough and the asymmetry note (why `lifted_transfer` vs `preimage_compose` differ) is appropriately explained.

4. **Reproducibility infrastructure.** Hash-pinned manifest, `reproduce_formal.sh`, and the Dockerfile provide unusually solid replay support for a theory paper.

5. **Assumption matrix appendix.** The fallback-claim column is practically useful and semantically sound.

6. **Role-category breakdown.** The 15/34/24 split in §4.6 manages reviewer expectations about what is "new" vs supporting. This is the right way to handle this.

7. **Must/may split.** The explicit policy split between undefined-observation handling is a genuine semantic contribution over naive total-map treatments.

---

### 3. Major Concerns (Blocking)

**M1. Novelty positioning is under-argued relative to existing mechanized order theory.**

The paper states (§6.1) it is a "methodology/library-style" contribution. That is a defensible position, but §7 does not engage with the mechanized order-theory literature at sufficient depth. Specifically:

- Mathlib's `GaloisConnection`, `OrderIso`, and `Set.preimage` infrastructure are cited as "baseline" but not concretely compared. A reviewer at FM/ITP will ask: why can't `Set.preimage_comp` + a partiality wrapper cover §3.5? The paper needs a concrete formal argument (not just prose) for why the `none`-branch elimination is non-trivial in a way Mathlib wrapping cannot handle easily.
- The non-adjointness theorem (§3.7) is stated as a "guardrail", but Mathlib already has `GaloisConnection` and totality requirements are explicit there. The paper should clarify whether `no_left_adjoint_of_partial` is strictly outside what Mathlib's framework already captures, or whether it is a specialization.

**Required action:** Add a concrete comparison subsection (can be short, ~half page) in §7 showing exactly where this kernel diverges from direct Mathlib instantiation, with specific API names.

---

**M2. RQ1/RQ2 resolution criteria are circular.**

§1.3 states RQ1 is resolved when "heterogeneity is carried through theorem statements without universe/typing collapse." §1.4 then says "RQ1 is considered resolved when... operationally witnessed by `heterogeneous_lifted_transfer`."

The resolution criterion is defined by the paper and then satisfied by the paper's own example. This is circular unless the criterion itself is justified. A reviewer will ask: what independent bar distinguishes "RQ1 resolved" from "we wrote a theorem that compiles"?

**Required action:** Either strengthen the RQ resolution criteria to reference an external standard (e.g., "the heterogeneous type signature must survive universe polymorphism checks without `ULift` or `PLift` coercions") or reframe RQ1/RQ2 as design goals rather than research questions with empirical resolution.

---

**M3. The `U0`/`UAnd` naming and its relation to the UAD/f literature is not anchored.**

The paper introduces `U0` and `UAnd` as if they are novel operators, but does not clearly establish whether these names/concepts exist in prior UAD/f literature or are fully original here. The abstract says "UAD/f kernel" but the references section does not cite any prior UAD/f work. If this is the first mechanization of UAD/f, that should be stated explicitly. If UAD/f is prior work by the authors, self-citation is needed.

**Required action:** Clarify the provenance of the UAD/f model. If original, say so. If prior work, cite it (even as a technical report). Reviewers at FM/ITP will flag unexplained acronyms.

---

**M4. The `UStar` treatment is semantically incomplete for its claimed role.**

§3.8 treats `UStar` as "an explicit theorem parameter" (not constructed). This is disclosed clearly, but §2.5 and the abstract refer to "`U0` (join-side coverage baseline)" as if it approximates an ideal root. If `UStar` is never constructed, the paper cannot claim it provides a "root-side criterion" (§1.1) beyond a parametric assumption contract.

The concern: a reader at TACAS or FM will note that "ideal-root linkage" without a construction or even a constructibility argument is a significant gap if the paper's motivation is cross-layer comparison. The conditional linkage theorems in §3.8 are fine as supporting results, but the introduction oversells this.

**Required action:** Either (a) strengthen §1.1 to explicitly say the paper does not construct a root-side criterion (only provides linkage templates), or (b) add a brief impossibility/approximation argument for why `UStar` construction is out of scope. The non-claim in §0.2 already partially does this but the problem statement (§1.1) still uses language suggesting a criterion is provided.

---

### 4. Minor Concerns

**m1. Section 0 is unusually long for an introduction.**
§0 spans claims, non-claims, and scope/quality-bar prose. At FM/ITP, this material usually lives in an introduction section with a contributions bullet list. Consider restructuring: move the quality-bar statement to a venue-fit footnote and fold the claims into a standard contributions enumeration.

**m2. The theorem-count inflation caveat is not prominent enough.**
The 73-theorem total includes 24 example-level declarations. A casual reader of the abstract or §4.4 may take 73 as the kernel size. The role-split explanation (§4.6) is correct but appears late. Consider adding a parenthetical at first mention of "73" in §4.4: "(15 primary, 34 supporting, 24 example-level; see §4.6)".

**m3. `preimage_compose` axiom footprint requires `Classical.choice`.**
The paper explains this (§4.3, point 7) and correctly notes it is a proof-style choice. However, it states "a constructivity-preserving re-proof is outside this scope" without saying whether one is believed to exist. For ITP/CPP, reviewers care. A brief sentence ("we conjecture a constructive proof exists but have not pursued it") or a pointer to the structural reason would help.

**m4. The `PasswordPolicy` case study (§5.2) uses identity projections.**
"Root carrier is Nat with identity projections `proj _ n = some n`" — this makes all layers share a trivially-unified root space, which simplifies the cross-layer consistency problem significantly. The paper acknowledges this is a "toy case" but does not discuss whether the `checkConsistent_iff_allThree` result would survive non-trivial projections. A sentence noting this limitation would strengthen intellectual honesty.

**m5. Related work §7.5 is thin on Galois-connection mechanization.**
Darais & Van Horn (Constructive Galois Connections, ICFP 2016) is cited but not engaged. The paper's non-adjointness result (`no_left_adjoint_of_partial`) is motivated as blocking "naive total-map adjoint intuitions" — but constructive Galois connections already work in settings without classical choice. Is the concern about constructivity or about partiality? Clarifying this would strengthen §7.5.

**m6. `reproduce_formal.sh` exits with `set -euo pipefail` but the `sorry` check uses `|| true`.**
Line `(rg -n '\bsorry\b' UadfU0 || true) | wc -l` — the `|| true` suppresses `rg`'s non-zero exit when no matches are found, which is correct behavior. However, the pattern `\bsorry\b` would also match `-- sorry` in comments. Consider adding `--multiline` or filtering comment lines. This is a script quality issue, not a theorem correctness issue, but artifact reviewers at FM may flag it.

**m7. Dockerfile does not pin the elan version.**
The `curl | sh` install of elan in the Dockerfile fetches the current release, which is not reproducible over time. Pin the elan version in the `RUN` command (e.g., `ELAN_VERSION=3.x.x`).

---

### 5. Required Revision Checklist

| # | Type | Item |
|---|---|---|
| R1 | **Blocker** | Add concrete Mathlib comparison subsection in §7 showing why direct `Set.preimage_comp`/`GaloisConnection` wrapping is insufficient for this kernel's theorems (M1) |
| R2 | **Blocker** | Fix circular RQ1/RQ2 resolution criteria: use external bar or reframe as design goals (M2) |
| R3 | **Blocker** | State explicit provenance of UAD/f model; add self-citation or "original to this work" declaration (M3) |
| R4 | **Blocker** | Align §1.1 problem statement with the actual `UStar`-as-parameter treatment; remove language suggesting a root-side criterion is constructed (M4) |
| R5 | Polish | Move §0 quality-bar/fit text to footnote; restructure §0 as standard contributions list (m1) |
| R6 | Polish | Add "(15 primary, 34 supporting, 24 example-level; see §4.6)" at first mention of "73" in §4.4 (m2) |
| R7 | Polish | Add one sentence on constructive proof status of `preimage_compose` (m3) |
| R8 | Polish | Add one sentence noting `PasswordPolicy` result scope under non-trivial projections (m4) |
| R9 | Polish | Clarify §7.5: is `no_left_adjoint_of_partial` about constructivity or partiality relative to Darais & Van Horn (m5) |
| R10 | Artifact | Fix `sorry` grep pattern in `reproduce_formal.sh` to exclude comment lines (m6) |
| R11 | Artifact | Pin elan version in `Dockerfile.fm` (m7) |
