# paper

This directory now follows a two-paper strategy:

1. **Formal-methods paper** (theory/mechanization first)
2. **Engineering paper** (operational trust and replayability)

## Structure
- `formal-methods/`
  - `manuscript_fm.md`: FM/ITP/CPP/TACAS/FASE/Formal Aspects-oriented manuscript
  - `appendix/fm_submission_checklist.md`
- `engineering/`
  - `manuscript_se.md`: SE-engineering oriented manuscript
  - `reproducibility/replay_acceptance_contract.md`
- `lean/`
  - Lean4 mechanization for UAD/f kernel and theorem assets
- `case-study/real_projects/`
  - PoC extraction/replay artifacts used by engineering manuscript
- `manuscript/`
  - legacy integrated manuscript drafts (kept for traceability)
- `reviews/`
  - review logs (organized by reviewer/professor/summary)

## Recommended Build/Replay
Formal mechanization:
```bash
cd paper/lean
~/.elan/bin/lake build
```

Engineering PoC replay:
```bash
cd paper/case-study/real_projects
bash reproduce.sh
python3 verify_replay.py --logs-dir logs
```

Readiness audit:
- `split_readiness_audit_20260218.md`
