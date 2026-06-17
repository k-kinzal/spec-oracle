# FM Submission Checklist

## Artifact Integrity
- [x] `lake build` succeeds on clean checkout
- [x] core theorem-name membership checks pass (`reproduce_formal.sh`)
- [x] theorem-to-file mapping in manuscript matches current Lean files
- [x] no hidden assumptions in theorem text (major hypotheses are named)
- [x] no claim that empirical PoC validates adequacy theorems directly
- [x] theorem-assumption matrix is published (`appendix/assumption_matrix.md`)

## Logical Scope
- [x] order convention fixed (inclusion only)
- [x] `U0`/`UAnd` roles separated and stable
- [x] must/may comparisons are not cross-mixed
- [x] non-adjointness statement scoped to partial projection setting

## Reproducibility Metadata
- [x] Lean toolchain version pinned (`paper/lean/lean-toolchain`)
- [x] build entry command documented
- [x] container replay recipe provided (`paper/formal-methods/appendix/Dockerfile.fm`)
- [x] proof assets listed with stable paths
- [x] manifest hash disclosed
- [x] theorem catalog published (`paper/formal-methods/appendix/theorem_catalog.md`)
- [x] axiom-audit command and outputs summarized in manuscript
- [x] local build evidence snapshot published (`paper/formal-methods/appendix/build_evidence.md`)

## Positioning
- [x] explicitly states classical overlap (LUB/GLB, pullback)
- [x] explicitly states mechanization-specific contribution (assumption audit + partiality)
- [x] no overclaim of mathematical novelty

## Suggested Verification Commands
```bash
cd paper/lean
lake build
rg -n '^theorem ' UadfU0 | wc -l
rg -n '\bsorry\b' UadfU0 || true
```
