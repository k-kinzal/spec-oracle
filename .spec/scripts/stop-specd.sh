#!/bin/bash
# Stop project-local specification server

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPEC_DIR="$PROJECT_ROOT/.spec"
PID_FILE="$SPEC_DIR/specd.pid"

if [ ! -f "$PID_FILE" ]; then
    echo "✗ specd is not running (no PID file)"
    exit 1
fi

PID=$(cat "$PID_FILE")
if ! kill -0 "$PID" 2>/dev/null; then
    echo "✗ specd is not running (stale PID file)"
    rm "$PID_FILE"
    exit 1
fi

echo "Stopping specd (PID: $PID)..."
kill "$PID"
rm "$PID_FILE"

echo "✓ specd stopped"
