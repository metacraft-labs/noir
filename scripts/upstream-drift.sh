#!/usr/bin/env bash
#
# Report how far this fork has drifted from upstream noir-lang/noir.
#
# This fork carries the CodeTracer tracer (tooling/tracer, tooling/tracer_wasm,
# `nargo trace`). It is expected to track an upstream *release*, not master.
# Without this script the drift is invisible: `git describe` needs upstream's
# tags, and a fork clone does not have them.
#
# Usage:
#   scripts/upstream-drift.sh                 # the current branch
#   scripts/upstream-drift.sh codetracer      # any set of refs
#
# Requires a remote named `upstream` pointing at noir-lang/noir; the script
# adds it if missing.

set -euo pipefail

UPSTREAM_URL="https://github.com/noir-lang/noir"

if ! git remote get-url upstream >/dev/null 2>&1; then
  echo "adding 'upstream' remote -> $UPSTREAM_URL" >&2
  git remote add upstream "$UPSTREAM_URL"
fi

echo "fetching upstream refs and tags (this is slow the first time)..." >&2
git fetch -q upstream --tags

latest=$(git describe --tags --abbrev=0 --match 'v[0-9]*' upstream/master)

for ref in "${@:-HEAD}"; do
  base=$(git describe --tags --abbrev=0 --match 'v[0-9]*' "$ref")
  # tags at or after $base, minus $base itself
  behind=$(( $(git tag -l 'v1.0.0-beta.*' --sort=v:refname --contains "$base" | wc -l) - 1 ))
  commits=$(git rev-list --count "$ref..upstream/master")
  printf '%-40s %s — %s releases behind %s, %s upstream commits not merged\n' \
    "$ref" "$base" "$behind" "$latest" "$commits"
done
