// Drive the `noir_tracer_wasm` module: a JavaScript string of Noir source goes
// in, an execution trace comes back.
//
// Deliberately host-agnostic. It is handed the module's bytes and knows nothing
// about where they came from, so `index.html` (which `fetch`es them) and the
// headless harness in `check_web.mjs` (which reads them off disk) run *this*
// code unchanged. Whatever the harness verifies is therefore what the page does.
//
// The module is built with `--no-default-features`, which drops the
// wasm-bindgen binding and leaves only the `ct_*` C ABI. There is no generated
// JS glue anywhere in this file: strings cross the boundary as `(ptr, len)`
// pairs in the module's linear memory. That is the point -- the compile and the
// trace demonstrably happen inside WebAssembly, because nothing else is present
// that could be doing them.

/// Instantiate the module and return a handle to its entry points.
export async function loadTracer(wasmBytes) {
  const module = await WebAssembly.compile(wasmBytes);

  // Satisfy whatever the module declares without pretending to implement it.
  // Built without `js` this should be empty; if a future change makes the
  // linker keep an import alive, the call throws loudly rather than silently
  // returning something wrong.
  const imports = {};
  for (const { module: m, name } of WebAssembly.Module.imports(module)) {
    imports[m] ??= {};
    imports[m][name] = () => {
      throw new Error(`the module reached ${m}.${name}, which this host does not provide`);
    };
  }

  const { exports } = await WebAssembly.instantiate(module, imports);
  const encoder = new TextEncoder();
  const decoder = new TextDecoder();

  // `exports.memory.buffer` must be re-read after every call into wasm: the
  // allocator grows linear memory, and growing it detaches every ArrayBuffer
  // view taken before. Caching a view here would produce zero-length reads that
  // look like an empty result rather than an error.
  const view = (ptr, len) => new Uint8Array(exports.memory.buffer, ptr, len);

  function writeString(str) {
    const encoded = encoder.encode(str);
    const ptr = exports.ct_alloc(encoded.length);
    view(ptr, encoded.length).set(encoded);
    return [ptr, encoded.length];
  }

  function takeResult(resultPtr) {
    const len = exports.ct_result_len();
    const isError = exports.ct_result_is_error() !== 0;
    // `.slice()` copies out of linear memory before it can be freed or grown.
    const bytes = view(resultPtr, len).slice();
    exports.ct_free(resultPtr, len);
    return { bytes, isError };
  }

  return {
    /// The imports the instantiated module actually declared, so a caller can
    /// show that the module is self-contained rather than assert it.
    imports: WebAssembly.Module.imports(module).map(({ module: m, name }) => `${m}.${name}`),

    /// Compile Noir source and trace it. `request` is a `TraceRequest`:
    /// `{ files, entry_point, inputs, inputs_are_json, package }`.
    traceSource(request) {
      const [ptr, len] = writeString(JSON.stringify(request));
      let result;
      try {
        result = takeResult(exports.ct_trace_source(ptr, len));
      } finally {
        exports.ct_free(ptr, len);
      }
      return finish(result);
    },

    /// Trace an already-compiled program. `artifactJson` is a `ProgramArtifact`
    /// as `nargo trace --emit-debug-artifact` writes it. The page does not use
    /// this, but it is what lets a comparison run both halves of the pipeline
    /// against each other inside one module.
    traceArtifact(artifactJson, inputs, inputsAreJson = false) {
      const [aPtr, aLen] = writeString(artifactJson);
      const [iPtr, iLen] = writeString(inputs);
      let result;
      try {
        result = takeResult(exports.ct_trace(aPtr, aLen, iPtr, iLen, inputsAreJson ? 1 : 0));
      } finally {
        exports.ct_free(aPtr, aLen);
        exports.ct_free(iPtr, iLen);
      }
      return finish(result);
    },
  };

  function finish(result) {
    const text = decoder.decode(result.bytes);
    if (result.isError) {
      throw new Error(text);
    }
    return JSON.parse(text);
  }
}

/// Reduce the low-level event stream to the counts `ct-print --full` reports,
/// so a trace made here can be compared with one made by native `nargo trace`.
///
/// `TraceLowLevelEvent` is an externally tagged serde enum, so each event is a
/// one-key object such as `{"Step": {...}}`.
export function summarize(trace) {
  const kinds = {};
  for (const event of trace.events) {
    const kind = typeof event === 'string' ? event : Object.keys(event)[0];
    kinds[kind] = (kinds[kind] ?? 0) + 1;
  }

  return {
    // `ct-print`'s `counts.calls` reports the call tree *below* the root, so
    // the synthetic `<toplevel>` call is excluded to match it.
    steps: kinds.Step ?? 0,
    calls: Math.max((kinds.Call ?? 0) - 1, 0),
    paths: trace.paths.length,
    // Likewise `<toplevel>` is function 0 and `None` is type 0 on this side.
    functions: Math.max((kinds.Function ?? 0) - 1, 0),
    varnames: kinds.VariableName ?? 0,
    types: kinds.Type ?? 0,
    values: kinds.Value ?? 0,
    io_events: kinds.Event ?? 0,
    events_total: trace.events.length,
    kinds,
  };
}

/// The error events the program produced, e.g. a failed `assert`.
export function errorEvents(trace) {
  return trace.events
    .filter((e) => typeof e === 'object' && 'Event' in e && e.Event.kind === 'Error')
    .map((e) => e.Event.content);
}
