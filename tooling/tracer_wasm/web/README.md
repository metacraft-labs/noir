# Noir source → execution trace, in a browser

A single static page that hands a JavaScript string of Noir source to a
WebAssembly module and gets an execution trace back. The Noir compiler, its
standard library and the ACVM/Brillig interpreter are all inside the module;
the page is served as plain files and nothing runs on the server.

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
`ct_result_len` / `ct_result_is_error`. Strings cross as `(ptr, len)` pairs in
linear memory. The module still *declares* a handful of `__wbindgen_*` imports —
they come from `uuid`'s and `getrandom`'s wasm features — but none are reached,
and the host binds every one of them to a function that throws, so reaching one
would fail loudly rather than quietly do the wrong thing.

## What comes back

Today: the low-level event stream as JSON — the same events, in the same order,
that a CTFS container writer would buffer. **Not** a `.ct` container: no `.ct`
writer can currently be reached from `wasm32-unknown-unknown` (the Nim writer
links a static library; the pure-Rust one gates its CTFS writer behind
`#[cfg(not(target_arch = "wasm32"))]` and pulls in C `zstd`). When a writer that
can, lands, the download becomes the container and nothing else here changes.

The counts the page renders (steps, calls, paths, IO events) are checked against
what `ct-print --full` reports for the container native `nargo trace` produces
from the same program — see `just compare-web-traces`.
