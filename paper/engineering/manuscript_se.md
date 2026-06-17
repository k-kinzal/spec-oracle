# Engineering Trust for Multi-Layer Consistency Audits: Deterministic Replay on top of the UAD/f Kernel

## Abstract
This paper presents an engineering trust design for multi-layer consistency audits over requirements/API/code artifacts.
Our core contribution is not formal theorem proving (handled in the companion FM paper), but an operationally reproducible pipeline with explicit uncertainty handling and machine-checkable replay acceptance.
The pipeline fixes inputs by lock+snapshot+hash, separates raw tri-valued judgement from policy projection, and pre-registers mutation expectations.
We report feasibility-stage evidence on three real OSS families plus a deterministic policy-ablation benchmark (21 scenarios) against a strict binary baseline.

## 0. Positioning and Claim Boundary
This manuscript is the engineering paper in a two-paper strategy:
- formal kernel correctness: `paper/formal-methods/manuscript_fm.md`
- engineering replay trust: this paper

Target bar: SE top-conference main-track style (clear pain/goal, reproducible artifact, explicit non-goals, falsifiable evaluation contract).

Non-goals in this paper:
- no statistical population inference from `n=3` convenience sample
- no proof that the concrete regex extractor satisfies formal adequacy hypotheses
- no claim of full behavioral/temporal specification governance

## 1. Pain, Goal, and Stakeholders
### 1.1 Pain
Teams maintain constraints across heterogeneous artifacts.
Frequent failures are:
- silent drift: same intent, different bounds across layers
- extraction fragility: wording drift breaks parsers
- non-replayability: reported results cannot be reconstructed from fixed inputs

### 1.2 Goal
Provide a pipeline where:
1. reported results are replayable from pinned inputs,
2. undefined extraction outcomes are explicit and policy-controlled,
3. contradiction vs uncertainty are separated,
4. mutation expectations are pre-specified and machine-checked.

### 1.3 Users
- quality/reliability engineers who must justify audit outcomes
- platform engineers maintaining multi-layer constraints
- reviewers/auditors who need deterministic replay evidence

## 2. System Architecture
Pipeline root: `paper/case-study/real_projects`.

Core components:
- runner/extractor: `external_validation.py`
- replay entrypoint: `reproduce.sh`
- replay verifier: `verify_replay.py`
- ablation harness: `evaluate_policy_ablation.py`
- canonical lock: `external_validation_sources.lock.json`
- drift lock and drift snapshot:
  - `logs/regex_drift_lock.json`
  - `logs/regex_drift_snapshot.txt`

`reproduce.sh` executes 6 sections in one run:
1. offline fail-fast
2. graceful must
3. graceful may
4. drift replay suite
5. edge-case log generation
6. policy-ablation benchmark generation

## 3. PoC Semantics
### 3.1 Per-layer status
For each layer:
- `supported`: two-sided interval extracted and well-formed (`l <= u`)
- `invalid`: two-sided interval extracted but ill-formed (`l > u`)
- `unknown`: parse failure or one-sided bound only

Important: `invalid` is IR well-formedness failure, not semantic contradiction proof.

### 3.2 Tri-valued judgement and policy projection
- `judgement` (raw): `consistent | contradictory | inconclusive`
- `policy_judgement`: projection of `inconclusive` under policy
  - must: `inconclusive -> contradictory`
  - may: `inconclusive -> consistent`

This avoids conflating logical contradiction with operational uncertainty.

Implementation excerpt (`external_validation.py`):
```python
def apply_none_policy(judgement: Judgement, none_semantics: NoneSemantics) -> Judgement:
    if judgement != "inconclusive":
        return judgement
    return "contradictory" if none_semantics == "must" else "consistent"
```

### 3.3 U0-side indicators vs UAnd-side diagnosis
PoC intentionally separates two observation paths:
- `proj_i^{U0}` path (`interval`) for coverage-style monitoring
- `measure_i^{UAnd}` path (`bounds`) for consistency diagnosis

Operational indicators:
- `u0_support_indicator`
- `u0_unfalsified_indicator`
- `u0_unknown_only`
- `support_ratio`, `unknown_ratio`, `invalid_interval_ratio`

Diagnosis outputs:
- `judgement`
- `policy_judgement`
- intersection bounds when available

## 4. Deterministic Replay Contract
### 4.1 Fixed inputs
- script: `external_validation.py`
- canonical lock: `external_validation_sources.lock.json`
- snapshots referenced by lock
- drift lock + drift snapshot

### 4.2 Acceptance projection (paper-level pass/fail)
Replay acceptance uses exactly four fields:
- `n_real_projects`
- `raw_judgement_distribution`
- `policy_judgement_distribution`
- `mutation_detected_by_expectation`

Rationale: these four are the publication-level acceptance projection.
Other outputs are preserved as audit detail, not pass/fail keys.

### 4.3 Determinism level
- equality criterion: semantic equality of the four-field projection
- key order is ignored
- distribution keys required: `{consistent, contradictory, inconclusive}`
- additional keys do not affect pass/fail
- `date` and similar runtime metadata are explicitly outside pass/fail

### 4.4 Machine-checkable procedure
Python-only (stdlib) path:
```bash
cd paper/case-study/real_projects
bash reproduce.sh
python3 verify_replay.py --logs-dir logs
```
Pass condition:
- process exit code `0`
- line `OK: replay verification checks passed`
- verification includes acceptance projection, drift split, edge-case log, and policy-ablation summary checks.

Optional: `jq` probes are supported but not required.

## 5. Feasibility Evidence (Current)
### 5.1 Real-project replay (`n=3`, graceful may)
Current replay projection:
- `n_real_projects = 3`
- `raw_judgement_distribution = {consistent:3, contradictory:0, inconclusive:0}`
- `policy_judgement_distribution = {consistent:3, contradictory:0, inconclusive:0}`
- `mutation_detected_by_expectation = 6` (`6 out of 6`)

Audit-detail snapshot:
- `avg_support_ratio = 0.7778` (`7/9`)
- `avg_unknown_ratio = 0.2222` (`2/9`)
- `support_frequency = {requirement:3, api:3, code:1}`
- `unknown_frequency = {requirement:0, api:0, code:2}`

Interpretation:
- coverage evidence is partial (code-side unknown appears in 2/3),
- this is not a failure condition by itself;
- unknown is retained as first-class observability signal.
- in this PoC, code-layer unknown primarily reflects one-sided extraction outcomes under current regex coverage, not immediate evidence of semantic inconsistency.

### 5.2 Drift scenario (regex wording breakage)
On drifted lock input:
- fail-fast mode stops immediately
- graceful modes continue and preserve tri-valued raw output

Observed drift split:
- must policy: one inconclusive case projected to contradiction side
- may policy: same inconclusive case projected to consistency side

This is expected and demonstrates policy transparency under extraction uncertainty.

### 5.3 Policy-ablation benchmark (`n=21` scenarios)
Generated by `evaluate_policy_ablation.py` from lock-fixed artifacts.
Scenario construction is deterministic and hand-crafted from replay-locked baseline artifacts (no random sampling).
Groups:
- contradiction: 6
- uncertainty: 9
- benign change: 6

Methods compared:
- `policy_must`
- `policy_may`
- `binary_strict` baseline (fail-closed binary)

Current summary:
- contradiction detection rate: must `1.0`, may `1.0`, binary_strict `1.0`
- false contradiction rate on non-contradiction: must `0.733`, may `0.133`, binary_strict `0.867`
- uncertainty collapse rate: must `1.0`, may `0.0`, binary_strict `1.0`

Engineering reading:
- `policy_may` reduces contradiction-side escalation under uncertainty,
- `policy_must` and strict binary aggressively collapse uncertainty to contradiction,
- explicit policy design is materially better than implicit binary collapse.

## 6. Why This is an Engineering Contribution
The engineering novelty is a trustable operation contract:
- lock + snapshot + hash chain discipline
- explicit uncertainty channel (`inconclusive`)
- configurable uncertainty projection (`must` / `may`)
- pre-registered mutation expectations with machine checks
- deterministic replay acceptance projection with executable verifier

This makes audit claims inspectable and repeatable by third parties.

## 7. Claim-to-Evidence Matrix
| Claim | Evidence artifact | Scope |
|---|---|---|
| deterministic replay from locked inputs | `reproduce.sh`, `verify_replay.py`, lock files | operational |
| uncertainty handled separately from contradiction | `judgement` vs `policy_judgement` outputs in logs | operational |
| drift behavior is policy-sensitive and reproducible | `regex_drift_*.log` trio | operational |
| acceptance is machine-checkable | Python-only verification path with exit code contract | reproducibility |
| policy choice changes error trade-offs | `policy_ablation_report.json` (`n=21`) + strict baseline | empirical-feasibility |

## 8. Threats to Validity
- convenience sample (`n=3`) only; no population inference
- regex extractor generalization is limited
- current mutation families are narrow (stale-lower, unit-scaling)
- no human-annotation validation pass yet
- interval-domain only

## 9. Roadmap to SE Top-Tier Evidence
### Stage A (completed in this artifact)
- deterministic replay contract
- tri-valued + policy-projected reporting
- drift harness
- policy ablation with explicit baseline

### Stage B (required for stronger external validity)
- larger benchmark with published sampling protocol
- human validation subset for extraction outputs
- broader mutation families (inclusive/exclusive, defaults, unit aliases)
- per-project failure taxonomy and confidence intervals
- baseline expansion beyond strict binary policy

## 10. Relationship to the FM Paper
This engineering paper consumes the FM kernel as trusted substrate, but does not claim concrete extractor adequacy proofs.
Formal theorems and assumptions are in:
- `paper/formal-methods/manuscript_fm.md`
- Lean code under `paper/lean/UadfU0/*`

The split prevents mixed-claim ambiguity:
- FM: theorem correctness and assumptions
- SE: operational trust and replay discipline

## 11. Reproducibility Pointers
- `paper/case-study/real_projects/README.md`
- `paper/engineering/reproducibility/replay_acceptance_contract.md`
- `paper/case-study/real_projects/reproduce.sh`
- `paper/case-study/real_projects/verify_replay.py`
- `paper/case-study/real_projects/evaluate_policy_ablation.py`
