#!/bin/bash
set -euo pipefail

# Run miri tests (the tests/miri_tests.rs target) for the workspace or specific
# crates. Requires the nightly toolchain with the miri component:
#
#   rustup toolchain install nightly
#   rustup +nightly component add miri
#
# Usage:
#   ./tools/miri.sh               # every miri_tests target in the workspace
#   ./tools/miri.sh nexus-slab    # only this crate
#
# -Zmiri-ignore-leaks is required because slab backing memory uses Box::leak
# for stable addresses; override by exporting MIRIFLAGS.

cd "$(dirname "$0")/.."

export MIRIFLAGS="${MIRIFLAGS:--Zmiri-ignore-leaks}"
shopt -s nullglob

declare -a files=()
if [ $# -eq 0 ]; then
    files=(*/tests/miri_tests.rs)
else
    for crate in "$@"; do
        files+=("$crate"/tests/miri_tests.rs)
    done
fi

if [ ${#files[@]} -eq 0 ]; then
    echo "no miri tests found"
    exit 0
fi

for f in "${files[@]}"; do
    crate="${f%%/*}"
    echo "=== miri: $crate ==="
    cargo +nightly miri test -p "$crate" --test miri_tests
done
