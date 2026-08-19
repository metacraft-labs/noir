# Noir source → a `.ct` trace container, in a browser

A single static page that hands a JavaScript string of Noir source to a
WebAssembly module and gets a complete `.ct` CodeTracer container back. The Noir
compiler, its standard library, the ACVM/Brillig interpreter and the CTFS
container writer are all inside the module; the page is served as plain files
and nothing runs on the server.

```
just serve-web          # build the module, stage it, serve on 127.0.0.1:8730
just check-web          # drive the page in headless Chromium and check the counts
just compare-web-traces # trace every fixture from source, compare with native
```

`file://` will not work: WebAssembly needs a real origin and the
`application/wasm` MIME type.

## Files

| file | what it is |
|---|---|
| `index.html` | the page: two textareas, a button, a decoded result |
| `tracer.mjs` | the driver over the module's `ct_*` C ABI — no wasm-bindgen glue |
| `check_web.mjs` | headless-Chromium check: clicks the button, reads the DOM |
| `compare_fixtures.mjs` | every `test_programs/trace` fixture, wasm vs native |

`tracer.mjs` is shared verbatim by all three, so what the checks verify is what
the page runs.

## Why there is no JS glue

The module is built `--no-default-features`, which drops the wasm-bindgen
binding and leaves only `ct_alloc` / `ct_free` / `ct_trace_source` /
`ct_trace_source_container` / `ct_result_len` / `ct_result_is_error`. Strings cross as `(ptr, len)` pairs in
linear memory. The module still *declares* a handful of `__wbindgen_*` imports —
they come from `uuid`'s and `getrandom`'s wasm features — but none are reached,
and the host binds every one of them to a function that throws, so reaching one
would fail loudly rather than quietly do the wrong thing.

## What comes back

`web_demo.ct` — a real CTFS container, assembled in the module's linear memory.
The event stream is offered as a second download for anyone who wants to read
the raw events; both come from a single pass, so they always describe the same
recording.

`ct_trace_source_container` frames the two as
`[u32 LE summary_len][summary JSON][.ct container]`, because a container is
arbitrary bytes and cannot ride inside JSON.

### What the container does not carry: columns

It is written by the pure-Rust `CtfsTraceWriter`, the only `.ct` writer that
builds for `wasm32-unknown-unknown` today. That writer has no column-bearing
step encoder — no `paths.dat` Layout A line-length table, no `sekDeltaColumn`
opcode — so it does not set the `meta.dat` capability bits either. The Noir
recorder *does* request column-aware steps on every trace; the writer reports
that the request was dropped and the page says so, in the `column-aware` row.
Native `nargo trace` still produces the column-aware container.

### Reading the container back

`ct-print` must be built from `codetracer-trace-format-nim` branch
`wasm/nim-to-wasm`. The stock reader cannot decode **any** container the
pure-Rust writer produces, natively or otherwise: it does not skip the writer's
8-byte `HEADERV1` prefix on `events.log`, it treats a zstd frame with no pledged
content size as a size, and it requires a `text` key on a boolean value that the
Rust `ValueRecord::Bool` does not carry.

```
nix develop --command nimble buildCtPrint   # in codetracer-trace-format-nim
ct-print --full web_demo.ct
```

`just check-web` does this to the file the browser actually downloaded, and
`just compare-web-traces` does it to every fixture, comparing three columns:
the native `nargo trace` container, the module's event stream, and the module's
own `.ct`.

## Branches this demo requires, across three repos

The `.ct` writer and the reader that can read it are both on **unmerged
branches in sibling worktrees**. This branch does not build without them.

| repo | branch / checkout | what it provides |
|---|---|---|
| `noir` | `wasm/webpage` (this) | the page, the in-wasm compile, `CtfsSink` |
| `codetracer-trace-format` | `wasm/ctfs-writer` in `../ctf-wt-wasm` | `CtfsTraceWriter` on wasm32 |
| `codetracer-trace-format-nim` | `wasm/nim-to-wasm` in `../ctfnim-wt-wasm` | the `ct-print` that can read it |

The workspace `Cargo.toml` points `codetracer_trace_types`,
`codetracer_trace_writer` (the Nim package) and `codetracer_trace_writer_rs`
(the pure-Rust one) **all** into `../ctf-wt-wasm`. They have to resolve to one
checkout: two copies of `codetracer_trace_types` on different paths are two
distinct types and `FullValueRecord` will not unify. `[patch.crates-io]` cannot
express this, since it only retargets registry dependencies.
