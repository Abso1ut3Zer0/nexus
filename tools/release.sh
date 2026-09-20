#!/usr/bin/env bash
# tools/release.sh — release one workspace crate via cargo-release + create
# a GitHub Release from the CHANGELOG entry.
#
# Usage:
#   tools/release.sh <crate> <bump>
#
# Where:
#   <crate>  is the package name (e.g., nexus-collections)
#   <bump>   is one of: patch | minor | major | <explicit-version>
#
# Workflow:
#   1. cargo-release bumps Cargo.toml, renames `## [Unreleased]` in
#      CHANGELOG.md to `## [<version>] — <date>`, commits, tags as
#      `<crate>-v<version>`, pushes the tag, publishes to crates.io.
#   2. This script then extracts the `## [<version>]` section from
#      CHANGELOG.md and creates a GitHub Release with that as notes.
#
# Pre-requisites:
#   - On main, working tree clean.
#   - cargo-release installed (`cargo install cargo-release`).
#   - gh CLI authenticated (`gh auth status`).
#   - CARGO_REGISTRY_TOKEN set or `cargo login` done previously.

set -euo pipefail

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <crate> <bump>" >&2
    echo "  e.g.: $0 nexus-collections patch" >&2
    exit 1
fi

crate="$1"
bump="$2"

if [ ! -f "$crate/Cargo.toml" ]; then
    echo "Error: $crate/Cargo.toml not found (run from workspace root)" >&2
    exit 1
fi

if [ ! -f "$crate/CHANGELOG.md" ]; then
    echo "Error: $crate/CHANGELOG.md not found" >&2
    exit 1
fi

if [ "$(git symbolic-ref --short HEAD 2>/dev/null)" != "main" ]; then
    echo "Error: not on main branch" >&2
    exit 1
fi

if [ -n "$(git status --porcelain)" ]; then
    echo "Error: working tree not clean" >&2
    exit 1
fi

# Pre-flight: guard against the double-bump that shipped nexus-id as 3.0.0
# instead of 2.0.0. In steady state the current Cargo.toml version is the last
# released one, so it is already on crates.io; release.sh then bumps UP from it.
# If the current version is NOT published, a previous run bumped without
# publishing (e.g. an invalid token) — refuse rather than bump a second time.
# Membership test (not max-version), so yanked versions don't affect it; fails
# open if crates.io is unreachable or the crate is brand new (404).
cur_version=$(grep -m1 '^version' "$crate/Cargo.toml" | cut -d'"' -f2)
crate_json=$(curl -sf --max-time 10 "https://crates.io/api/v1/crates/$crate" || true)
if [ -n "$crate_json" ] && ! printf '%s' "$crate_json" | grep -qF "\"num\":\"$cur_version\""; then
    echo "Error: current version $cur_version of $crate is not published on" >&2
    echo "crates.io — a previous release likely bumped without publishing." >&2
    echo "Reconcile (reset the version, or publish/yank the pending one) before" >&2
    echo "releasing again." >&2
    exit 1
fi

# Pre-flight: fail before bumping if no crates.io credentials are present, rather
# than leaving a half-completed release behind.
if [ -z "${CARGO_REGISTRY_TOKEN:-}" ] && [ ! -f "${CARGO_HOME:-$HOME/.cargo}/credentials.toml" ]; then
    echo "Error: no crates.io credentials found (set CARGO_REGISTRY_TOKEN or run" >&2
    echo "cargo login) before releasing." >&2
    exit 1
fi

echo "==> cargo release $bump --execute -p $crate"
cargo release "$bump" --execute -p "$crate"

# After cargo-release: read the new version from Cargo.toml.
version=$(grep -m1 '^version' "$crate/Cargo.toml" | cut -d'"' -f2)
tag="${crate}-v${version}"

echo "==> Extracting CHANGELOG section for $version"
notes_file=$(mktemp)
trap 'rm -f "$notes_file"' EXIT
awk -v ver="$version" '
    $0 ~ "^## \\[" ver "\\]" { p=1; print; next }
    p && $0 ~ "^## \\[" { exit }
    p { print }
' "$crate/CHANGELOG.md" > "$notes_file"

if [ ! -s "$notes_file" ]; then
    echo "Warning: could not extract CHANGELOG section for [$version] in $crate/CHANGELOG.md" >&2
    echo "Creating release with empty notes — edit on GitHub if needed." >&2
fi

echo "==> gh release create $tag"
# Use --notes-file (not --notes "...") to avoid shell/OS argument-length
# limits on long CHANGELOG sections (e.g., major release notes with
# migration tables).
gh release create "$tag" \
    --title "$crate v$version" \
    --notes-file "$notes_file"

echo
echo "Released: $tag"
echo "  crates.io: https://crates.io/crates/$crate/$version"
echo "  GitHub:    https://github.com/Abso1ut3Zer0/nexus/releases/tag/$tag"
