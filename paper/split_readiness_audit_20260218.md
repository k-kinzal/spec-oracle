# Split-Paper Readiness Audit (2026-02-18, Updated)

## Scope
- Target A: FM/ITP/CPP/TACAS/FASE/Formal Aspects quality bar (formal-methods paper)
- Target B: SE top-conference main-track quality bar (engineering paper)

Assessed files:
- `paper/formal-methods/manuscript_fm.md`
- `paper/engineering/manuscript_se.md`
- `paper/engineering/reproducibility/replay_acceptance_contract.md`
- `paper/lean/UadfU0/*`
- `paper/case-study/real_projects/*`

---

## A. Formal-Methods Paper Readiness

### A1. Criteria and status
1. Typed model, notation stability, and explicit assumptions: **PASS**
2. Non-trivial theorem layer (transfer/composition/adequacy/non-adjointness): **PASS**
3. Theorem-to-file traceability and mechanization reproducibility: **PASS**
4. Logic-basis disclosure (toolchain/manifest/axiomatic footprint): **PASS**
5. Novelty positioning vs classical overlap (no overclaim): **PASS**
6. Related-work contrast with contribution delta: **PASS**
7. Claim boundaries vs engineering PoC separation: **PASS**

### A2. Evidence snapshot
- `lake build` succeeds.
- theorem count (`paper/lean/UadfU0`): `59`
- `sorry` count: `0`
- LOC (`paper/lean/UadfU0`): `1502`
- toolchain: `leanprover/lean4:v4.27.0`
- manifest hash: `8c098d788704fb7c279c7004a1f492723bd892acf2500483665ae39e7a00a6e7`

### A3. Verdict
Formal-methods manuscript is at submission-ready quality for the stated FM venues.

---

## B. Engineering Paper Readiness

### B1. Criteria and status
1. Pain/goal/non-goal clarity and architecture transparency: **PASS**
2. Deterministic replay contract with machine-checkable pass condition: **PASS**
3. Tri-valued uncertainty semantics and policy projection separation: **PASS**
4. Reproducibility independence (Python-only acceptance path): **PASS**
5. Comparative evidence (policy ablation + strict binary baseline): **PASS**
6. Drift/failure-mode observability and mutation expectation discipline: **PASS**
7. Threats-to-validity and scope boundaries: **PASS**

### B2. Evidence snapshot
- replay entrypoint passes:
  - `bash paper/case-study/real_projects/reproduce.sh`
  - `python3 paper/case-study/real_projects/verify_replay.py --logs-dir paper/case-study/real_projects/logs`
- acceptance projection (4 fields) stable.
- ablation report:
  - `n_scenarios = 21`
  - contradiction detection rate: must/may/binary_strict = `1.0 / 1.0 / 1.0`
  - false contradiction on non-contradiction: `0.733 / 0.133 / 0.867`
  - uncertainty collapse: `1.0 / 0.0 / 1.0`

### B3. Residual risk (non-blocking for current claim level)
- real-project sample remains convenience-scale (`n=3`), so external statistical generalization is intentionally out of scope.
- engineering manuscript already constrains claims to replay trust and operational transparency, not population-level effectiveness.

### B4. Verdict
Engineering manuscript is at submission-ready quality for the claimed engineering contribution class (deterministic replay trust design with bounded empirical scope).

---

## Bottom Line
- Split strategy is complete and internally consistent.
- FM paper: submission-ready under formal-methods bar.
- Engineering paper: submission-ready under explicitly bounded SE contribution claims.
- Remaining edits are editorial (wording/format), not technical blockers.
