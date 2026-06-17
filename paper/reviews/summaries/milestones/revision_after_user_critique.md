# Revision After Critical Review

Date: 2026-02-14

## Trigger
User指出: 論文が「定義の自明展開」に見え、UAD/f定義が本文で自己完結していない。

## Applied Revisions (paper only)
1. Typed UAD/f model introduced explicitly in manuscript and Lean:
   - root space `Ω`
   - layer carriers `βᵢ`
   - `Dᵢ`, `Aᵢ`, and invariant `Aᵢ ⊆ Dᵢ`
   - partial projection `projᵢ : Ω → Option βᵢ`
   - induced inverse image as concrete interpretation of `f₀ᵢ⁻¹`
2. Added non-trivial core theorem for operations:
   - layer-set extension monotonicity (`U0On_monotone`)
3. Clarified contribution boundaries and research questions (RQ1-RQ3).
4. Added related-work positioning and reproducibility metrics.

## Verification
- `paper/lean`: `lake build` succeeded after revision.
