#!/bin/bash
# Start project-local specification server

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPEC_DIR="$PROJECT_ROOT/.spec"
PID_FILE="$SPEC_DIR/specd.pid"
LOG_FILE="$SPEC_DIR/specd.log"

if [ -f "$PID_FILE" ]; then
    PID=$(cat "$PID_FILE")
    if kill -0 "$PID" 2>/dev/null; then
        echo "✗ specd is already running (PID: $PID)"
        exit 1
    fi
    rm "$PID_FILE"
fi

export SPECD_STORE_PATH="$SPEC_DIR/specs.json"

echo "Starting project-local specd..."
echo "  Store: $SPECD_STORE_PATH"
echo "  Log: $LOG_FILE"

specd > "$LOG_FILE" 2>&1 &
echo $! > "$PID_FILE"

sleep 1

if kill -0 $(cat "$PID_FILE") 2>/dev/null; then
    echo "✓ specd started (PID: $(cat "$PID_FILE"))"
else
    echo "✗ Failed to start specd. Check $LOG_FILE"
    rm "$PID_FILE"
    exit 1
fi
