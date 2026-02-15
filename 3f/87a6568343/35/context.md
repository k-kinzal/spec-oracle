# Session Context

## User Prompts

### Prompt 1

Reviewer=R3 (reproducibility).
Use ONLY provided files. If a claim is not verifiable from provided files, do NOT include it in required_fixes.
Assess replay, naming consistency, and terminology alignment.
PROMPT > /tmp/reviewer3_round34.json


# Context files

--- BEGIN FILE: paper/case-study/real_projects/reproduce.sh ---
#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}"

mkdir -p logs

python3 external_validation.py \
  --offli...

