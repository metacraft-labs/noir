# Carry versus upstream — what this fork should stop carrying

**Milestone:** VN-M2a of `codetracer-specs/Planned-Work/Verno-CodeTracer-Integration.milestones.org`
**Measured:** 2026-08-28, against `noir-lang/noir` `v1.0.0-beta.26` (`3d3a1ce788`), which is
this branch's merge base with `upstream/master`.

## The size of the thing

```
$ git diff --shortstat 3d3a1ce788 HEAD
114 files changed, 5498 insertions(+), 120 deletions(-)

$ git diff --stat 3d3a1ce788 HEAD -- compiler
 compiler/noirc_driver/src/lib.rs                |  13 +-
 compiler/noirc_evaluator/src/ssa/builder.rs     |  41 ++-
 compiler/noirc_evaluator/src/ssa/mod.rs         | 104 ++++--
 compiler/noirc_evaluator/src/ssa/ssa_gen/mod.rs |   3 +
 compiler/noirc_frontend/src/debug/mod.rs        | 417 +++++++++++++++++++++++-
 5 files changed, 533 insertions(+), 45 deletions(-)
```

**Only those 533 lines are the fork.** Everything else is additive: `tooling/tracer` (2 490),
`tooling/tracer_wasm` (860), `tooling/debugger` (209), `tooling/nargo_cli` incl. `nargo trace`
(232), `test_programs/trace` (746), `scripts/` (60), the `justfile` and two CI jobs (111).
Additive files do not conflict; the 1 614 upstream commits absorbed in this sync merged into
them without a single conflict.

So the cost of the next bump is not 5 498 lines. It is 533 lines in five files. And it splits
cleanly in two:

* **417 of them are `debug/mod.rs`** — the `AssignOp` arm, the `Loop`/`While` arms, the three
  exhaustive matches and their regression tests (§2 below). All of it is a fix to *upstream's*
  own `DebugInstrumenter`, so this number should go to zero by being sent upstream rather than
  by being carried better. It is large only because a silent defect deserves loud comments and
  real tests.
* **116 of them are the SSA/driver changes** (§1, §3) — and, disproportionately, inside
  `primary_passes()`, the single most churn-prone function in the SSA pipeline, where the fork
  appends `.only_when_optimizing()` at **23** separate call sites. That is the part that
  actually conflicts on every bump, and that is where to aim.

## Per-change position

### 1. `OptimizationLevel::Debug` + `SsaPass::only_when_optimizing()` — **upstream, first priority**

`ssa/mod.rs` (104), `ssa/builder.rs` (41), `noirc_driver/src/lib.rs` (13) — 158 of the 533
insertions, and almost all of the compiler delta outside `debug/mod.rs`.
Adds a second SSA optimization level that skips every pass which rewrites the control-flow
graph (unrolling, flattening, constant folding, inlining, LICM, function specialization), so
opcodes keep the source line they were generated for.

Upstream it because:

* It serves **`nargo debug`**, which is upstream's own command, identically to how it serves
  `nargo trace`. Upstream already has the two adjacent mechanisms — `create_program_with_minimal_passes`
  and `--skip-ssa-pass` — so this is a third point on a line it is already drawing, not a new
  concept.
* It is the **expensive** part to carry. The diff is interleaved through the pass list
  (`.only_when_optimizing()` appended at 23 separate sites inside `primary_passes()`), so every
  upstream commit that adds, removes or reorders a pass touches it. Breakage #4 of this sync —
  step granularity moving, on re-measurement 15 of 21 fixtures by step count and 19 of 21 by
  full decoded document — came from exactly this function.
* Carrying it has a **silent** failure mode, which the code itself documents: `allowed_at_debug`
  defaults to `true`, so a newly added upstream pass runs at `Debug` until someone notices it
  rewrites the CFG. That is the same class of defect as the `AssignOp` one below — wrong
  recorded data, green build. Upstream, the default would be reviewed by the pass's author.

### 2. `DebugInstrumenter`'s `AssignOp` / `Loop` / `While` arms and its exhaustive matches — **upstream, immediately, as two bug fixes**

`noirc_frontend/src/debug/mod.rs`. This is not CodeTracer code: `DebugInstrumenter` is upstream's,
and it feeds upstream's `nargo debug`. When noir-lang/noir#12123 (`beta.20`) made `x <op>= y`
its own `StatementKind::AssignOp` instead of desugaring it in the parser, the instrumenter's
`_ => {} // Constrain, Error` catch-all swallowed it, and **every compound assignment stopped
being recorded — in upstream's own debugger too**. `x` shows its pre-assignment value for the
whole run while the circuit computes the right answer.

The whole package is upstreamable as one PR and it is the cheapest win available: it removes
fork lines *and* fixes a live upstream bug.

* the `walk_assign_op_statement` desugaring, which preserves both properties
  `test_programs/execution_success/op_assign_desugaring` pins (rhs evaluated before the lvalue
  is read; an lvalue index sub-expression evaluated exactly once);
* the exhaustive matches over `StatementKind`, `ExpressionKind` and `LValue` that replace the
  catch-alls, so the *next* upstream variant is a compile error rather than data loss;
* the `StatementKind::{Loop, While}` arms. The same catch-all was also swallowing these two,
  so **assignments inside a `while` or `loop` body were never recorded at all** — and, unlike
  the `AssignOp` case, that was never a regression: both variants already existed at
  `beta.18` and already fell into the same `_ => {}`. It went unnoticed because no fixture in
  `test_programs/trace` used `while` or `loop`. Recorded on a `beta.18` build, the new
  `while_loop` fixture yields four observations — `n`, `out`, `acc = 0`, `i = 0` — and then
  nothing for five iterations, while the circuit computes the right answer.
* the six `debug::tests` regression tests, plus the `while_loop` fixture and
  `test_tracer.rs::test_while_loop_body_assignments_are_recorded`, which pins the recorded
  value sequence end to end. Note that `op_assign_desugaring` alone does **not** catch the
  `AssignOp` defect — the program executes correctly whether or not the instrumenter ran. Only
  counting emitted `__debug_var_assign` calls does, and only comparing recorded *values*
  catches the `while`/`loop` one; step counts do not move enough to notice.

### 3. `codegen_ident` sets the builder location — **upstream**

`ssa/ssa_gen/mod.rs`, three lines. A source-location accuracy fix with no CodeTracer-specific
content. Send it with (1).

### 4. `tooling/debugger` — **upstream, medium priority**

209 lines: `DebugContext` promoted from `pub(super)` to a documented public API (the change is
almost entirely `pub(super)` → `pub` plus a doc comment grouping the surface), and the CLI
front-ends (`repl`, `dap`) and the RPC oracle resolver moved behind cargo features so the
debugger crate can cross the wasm32 boundary.

Note this area is already *shrinking*: `06e3d2db36` deleted
`DebugContext::{get_filepath_for_location, get_line_for_location, get_column_for_location}`
because they were one-line forwarders over `DebugArtifact` methods upstream already made
public, leaving `debug_artifact()` as the only accessor the fork actually adds. Column-aware
recording is unaffected — the tracer now calls `DebugArtifact::location_column_number`
directly. That is the model for the rest of this list.

Upstream has its own browser/wasm ambitions and this is exactly the shape they need; the fork
has already proved it compiles for `wasm32-unknown-unknown` (`just check-wasm`, wired into
`.github/workflows/formatting.yml`). Feature-gating is also the kind of change upstream accepts
readily because it is opt-out, not behavioural.

### 5. `tooling/tracer`, `tooling/tracer_wasm`, `nargo trace`, `test_programs/trace` — **carry**

~4 000 lines. CTFS containers, the Nim writer FFI, CodeTracer's capability flags. There is no
upstream constituency for it and it should not be offered.

**But it is what makes this repository untestable in CI**, which is a bigger problem than
anything above. The workspace root `Cargo.toml` declares
`codetracer_trace_types` and `codetracer_trace_writer` as `path =
"../codetracer-trace-format/…"` dependencies, which `tooling/tracer` then inherits with
`workspace = true`. Those are *sibling repositories* that do not exist in a bare checkout, and
because the declaration is at the workspace root the breakage is not confined to
`tooling/tracer`: nothing in the workspace resolves, not even `cargo metadata`. Every
scheduled Rust job on this fork currently dies before compiling a single crate:

```
error: failed to load manifest for workspace member `/Users/runner/work/noir/noir/tooling/tracer`
referenced by workspace at `/Users/runner/work/noir/noir/Cargo.toml`
  failed to load manifest for dependency `codetracer_trace_types`
  failed to read `/Users/runner/work/noir/codetracer-trace-format/codetracer_trace_types/Cargo.toml`
```

Fixing that — a git or registry dependency instead of a path one, or making `tooling/tracer` a
non-default workspace member — is worth more than any single upstreaming above, because it is
the precondition for the fork having any working CI at all.

### 6. `justfile` and the wasm32 CI job — **carry**

60 lines across two files, no conflict surface.

## The rule

Budget the **compiler** delta, not the total. `tooling/` is additive and merged clean across
eight releases; `compiler/` is what costs. Target for the next sync: 533 → 0, and the 417 in
`debug/mod.rs` should be the first to go, because it is upstream's bug and upstream's test.

Order of value: (2) first — it is a bug fix, it is small, and it fixes upstream's own debugger.
Then (1), which is most of the remaining lines and all of the recurring conflict. (3) rides
along with (1). (4) is worth opening but will take longer to land.
