#!/bin/bash
set -euo pipefail

# Run loom model-checking tests (compiled under --cfg loom) for the workspace
# or specific crates. Loom tests live at <crate>/tests/loom_*.rs and are
# excluded from normal `cargo test` by the `#![cfg(loom)]` gate.
#
# Usage:
#   ./tools/loom.sh                          # every loom test in the workspace
#   ./tools/loom.sh nexus-channel nexus-shm  # only these crates
#
# Loom explores interleavings exhaustively. For a larger model that takes too
# long, bound the search by exporting LOOM_MAX_PREEMPTIONS (e.g. =3).

cd "$(dirname "$0")/.."

export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }--cfg loom"
shopt -s nullglob

declare -a files=()
if [ $# -eq 0 ]; then
    files=(*/tests/loom_*.rs)
else
    for crate in "$@"; do
        files+=("$crate"/tests/loom_*.rs)
    done
fi

if [ ${#files[@]} -eq 0 ]; then
    echo "no loom tests found"
    exit 0
fi

for f in "${files[@]}"; do
    crate="${f%%/*}"
    test="$(basename "$f" .rs)"
    echo "=== loom: $crate :: $test ==="
    cargo test -p "$crate" --test "$test" --release
done
