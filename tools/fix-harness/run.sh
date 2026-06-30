#!/usr/bin/env bash
set -euo pipefail

FIX_PORT=${FIX_PORT:-9878}
REPO_ROOT=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
HARNESS_DIR="$REPO_ROOT/tools/fix-harness"

podman build -t fix-harness "$HARNESS_DIR"

FIX_PORT=$FIX_PORT cargo run -p nexus-fix-engine --example blocking_session &
ENGINE_PID=$!
trap "kill $ENGINE_PID 2>/dev/null || true" EXIT

echo "waiting for engine on port $FIX_PORT..."
until (echo >/dev/tcp/127.0.0.1/"$FIX_PORT") 2>/dev/null; do sleep 0.3; done
echo "engine ready"

podman run --rm \
    --network=host \
    -e FIX_PORT="$FIX_PORT" \
    -v "$HARNESS_DIR/features:/harness/features:Z" \
    fix-harness \
    behave /harness/features
