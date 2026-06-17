# Engineering Paper Package

Primary manuscript:
- `paper/engineering/manuscript_se.md`

PoC artifacts:
- `paper/case-study/real_projects/README.md`
- `paper/case-study/real_projects/reproduce.sh`
- `paper/case-study/real_projects/verify_replay.py`
- `paper/case-study/real_projects/external_validation.py`
- `paper/engineering/reproducibility/replay_acceptance_contract.md`

Recommended replay:
```bash
cd paper/case-study/real_projects
bash reproduce.sh
python3 verify_replay.py --logs-dir logs
```
