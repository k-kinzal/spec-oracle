# Professor Review Round 1 (Claude -p)

- Verdict: NG
- Date: 2026-02-14

## Major Issues (summary)
1. inverse mapping semantics were under-specified (`inv` was arbitrary primitive).
2. claim wording around "least upper bound" needed stricter order-theoretic statement.
3. manuscript overstated contribution (definitions/tautologies presented as full model validity proof).

## Applied fixes
- Replaced primitive `inv` with projection-induced inverse image:
  - added `proj : ι → α → Option α`
  - defined `preimage`, `lifted`, `U0` from `proj`.
- Added non-trivial lemmas:
  - `preimage_monotone`
  - `preimage_union`
  - `U0_below_every_upper_bound`
  - `U0_is_supremum`
- Tightened claims in manuscript:
  - explicit scope/limitations
  - removed overclaims about full UAD/f semantic validity.
- Added contradictory-layer concrete example.
