# Session Context

## User Prompts

### Prompt 1

GOAL:
- Strict reproducibility/artifact re-review after reproducibility fixes.

CONTEXT:
- Verify hash/self-check workflow, lock/snapshot semantics, drift logs availability, and replay command coherence.

TASK:
- Determine if independent replay and acceptance checks are fully executable.
- required_fixes only for true replay blockers.

OUTPUT:
- Return ONLY JSON matching schema.
- pass_gate=true only if reproducibility gate is satisfied.


# Context files

--- BEGIN FILE: paper/manuscript/uadf_u...

