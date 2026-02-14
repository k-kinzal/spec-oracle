#!/usr/bin/env bash
set -euo pipefail

STATE_FILE="${CLAUDE_PROJECT_DIR}/.claude/claude-loop.state.json"

log() {
  [[ -f "${CLAUDE_PROJECT_DIR}/.claude/claude-loop.debug" ]] && echo "[claude-loop hook] $1" >&2 || true
}

INPUT=$(cat)
[[ ! -f "$STATE_FILE" ]] && exit 0

STATE=$(cat "$STATE_FILE")
[[ $(echo "$STATE" | jq -r '.active // false') != "true" ]] && exit 0

if [[ $(echo "$INPUT" | jq -r '.stop_hook_active // false') == "true" ]]; then
  log "decision=stop_hook_active"
  jq '.hook_called = true | .decision = "stop_hook_active"' "$STATE_FILE" > "${STATE_FILE}.tmp" \
    && mv "${STATE_FILE}.tmp" "$STATE_FILE"
  exit 0
fi

TRANSCRIPT_PATH=$(echo "$INPUT" | jq -r '.transcript_path // empty')
ITERATION=$(echo "$STATE" | jq -r '.iteration // 1')
MAX_ITERATIONS=$(echo "$STATE" | jq -r '.max_iterations // 0')
COMPLETION_PROMISE=$(echo "$STATE" | jq -r '.completion_promise // ""')

if [[ -n "$COMPLETION_PROMISE" ]] && [[ -n "$TRANSCRIPT_PATH" ]] && [[ -f "$TRANSCRIPT_PATH" ]]; then
  if jq -r 'select(.type == "assistant") | .message.content[]? | select(.type == "text") | .text // empty' "$TRANSCRIPT_PATH" 2>/dev/null | grep -qF "$COMPLETION_PROMISE"; then
    log "decision=complete (iteration=$ITERATION)"
    jq '.decision = "complete" | .hook_called = true' "$STATE_FILE" > "${STATE_FILE}.tmp" \
      && mv "${STATE_FILE}.tmp" "$STATE_FILE"
    exit 0
  fi
fi

if [[ "$MAX_ITERATIONS" -gt 0 ]] && [[ "$ITERATION" -ge "$MAX_ITERATIONS" ]]; then
  log "decision=max_reached (iteration=$ITERATION/$MAX_ITERATIONS)"
  jq '.decision = "max_reached" | .hook_called = true' "$STATE_FILE" > "${STATE_FILE}.tmp" \
    && mv "${STATE_FILE}.tmp" "$STATE_FILE"
  exit 0
fi

NEW_ITERATION=$((ITERATION + 1))
log "decision=continue (iteration=$ITERATION->$NEW_ITERATION)"
jq --argjson iter "$NEW_ITERATION" '.iteration = $iter | .decision = "continue" | .hook_called = true' \
  "$STATE_FILE" > "${STATE_FILE}.tmp" && mv "${STATE_FILE}.tmp" "$STATE_FILE"

( sleep 0.1; kill -TERM "$PPID" 2>/dev/null || true ) &
exit 0
