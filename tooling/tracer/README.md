# Noir Tracer

A tracer for Noir that produces execution traces.

Invoke with `nargo trace --out-dir=<place to store trace>`.

## Keeping the fork small

`CARRY-VS-UPSTREAM.md` in this directory is the standing position on which of the
fork's compiler changes should be sent upstream and which are CodeTracer's to
carry, with the measured line counts behind it. Read it before adding to the
`compiler/` delta — that is the only part of this fork that costs anything on an
upstream bump.

## Drift from upstream

`scripts/upstream-drift.sh` reports how far each tracked ref is behind
`noir-lang/noir`'s latest release, and exits non-zero past `DRIFT_MAX_BEHIND`
(default 2 releases). `.github/workflows/upstream-drift.yml` runs it weekly.
