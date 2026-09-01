// drive_noir_wasm_modes.mjs — drive `compiler/wasm`'s bare C ABI the way a browser does.
//
// The module DECLARES wasm-bindgen placeholder imports and REACHES none of them: the
// `nv_*` path touches no JS. So the imports are satisfied here with stubs that throw,
// and the count of stubs actually called is asserted at zero. That is the property the
// bare ABI exists for, stated as a measurement rather than as an instantiation trick —
// a page supplies the same throwing stubs and never sees one fire.
//
// What it asserts: `contract-debug` reaches `compile_contract` and returns a CONTRACT
// artifact, and an unknown mode is REFUSED rather than quietly compiled as a `program`.
// Both are claims about the bytes the deploy ships, not about `cargo test`.

import { readFileSync } from "node:fs";

const modulePath = process.argv[2];
if (!modulePath) {
  console.error("usage: node drive_noir_wasm_modes.mjs <noir_wasm.wasm>");
  process.exit(2);
}

let failures = 0;
const ok = (what, cond, detail = "") => {
  if (cond) {
    console.log(`ok   ${what}${detail ? ` (${detail})` : ""}`);
  } else {
    failures += 1;
    console.error(`FAIL ${what}${detail ? `: ${detail}` : ""}`);
  }
};

const bytes = readFileSync(modulePath);
const compiled = new WebAssembly.Module(bytes);
const declared = WebAssembly.Module.imports(compiled);

// Every declared import becomes a stub that records that it was reached and then throws.
// A module that genuinely needs JS would fail loudly here rather than silently working.
let reached = 0;
const reachedNames = [];
const importObject = {};
for (const { module, name } of declared) {
  importObject[module] ??= {};
  importObject[module][name] = (...args) => {
    reached += 1;
    reachedNames.push(`${module}.${name}`);
    throw new Error(`the nv_* path reached the JS import ${module}.${name}`);
  };
}

const instance = await WebAssembly.instantiate(compiled, importObject);
const x = instance.exports;

for (const name of ["nv_alloc", "nv_free", "nv_compile_vfs", "nv_result_len", "memory"]) {
  ok(`the module exports ${name}`, typeof x[name] !== "undefined");
}
if (failures) process.exit(1);

ok("the module declares its wasm-bindgen placeholder imports", declared.length > 0,
   `${declared.length} imports`);

function compile(request) {
  const payload = new TextEncoder().encode(JSON.stringify(request));
  const ptr = x.nv_alloc(payload.length);
  new Uint8Array(x.memory.buffer, ptr, payload.length).set(payload);
  const outPtr = x.nv_compile_vfs(ptr, payload.length);
  const outLen = x.nv_result_len();
  const out = new TextDecoder().decode(
    new Uint8Array(x.memory.buffer, outPtr, outLen).slice(),
  );
  x.nv_free(ptr, payload.length);
  x.nv_free(outPtr, outLen);
  return JSON.parse(out);
}

// A `type = "contract"` package. Small on purpose: this file is about the MODE reaching
// the compiler through the ABI, and the real Aztec tree is measured natively in
// `compile_vfs.rs`'s own tests.
const files = {
  "ctr/Nargo.toml": '[package]\nname = "counter"\ntype = "contract"\n',
  "ctr/src/main.nr":
    "contract Counter {\n" +
    "    fn triple(x: Field) -> pub Field { x + x + x }\n" +
    "    fn bump(x: Field) -> pub Field {\n" +
    "        let a = x + 1;\n" +
    "        let b = a + a;\n" +
    "        b\n" +
    "    }\n" +
    "}\n",
};

// --- contract-debug: the combination that used to be unreachable -----------------------
const debugged = compile({ files, package_dir: "ctr", mode: "contract-debug" });
ok("contract-debug compiles", debugged.ok === true, debugged.message ?? "");
ok("…and returns a contract artifact", debugged.artifact?.name === "Counter",
   JSON.stringify(debugged.artifact?.name));
ok("…with both of the contract's functions", debugged.artifact?.functions?.length === 2,
   `${debugged.artifact?.functions?.length}`);
// Instrumentation is what a tracer needs. `debug_symbols` is base64 of a GZIPPED blob,
// so what is comparable through the ABI is its size against the same contract compiled
// without instrumentation — a ratio, not an absolute. The exact figure that matters (the
// number of brillig opcodes mapped to source locations) is asserted natively, in
// `a_real_aztec_contract_compiles_for_debugging_and_is_instrumented`, where the
// artifact is a typed value rather than JSON.
const plain = compile({ files, package_dir: "ctr", mode: "contract" });
ok("contract (uninstrumented) also compiles", plain.ok === true, plain.message ?? "");
const debugSyms = (debugged.artifact?.functions ?? [])
  .map((f) => f.debug_symbols.length).reduce((a, b) => a + b, 0);
const plainSyms = (plain.artifact?.functions ?? [])
  .map((f) => f.debug_symbols.length).reduce((a, b) => a + b, 0);
ok("…and carries materially more debug information than the uninstrumented one",
   debugSyms > plainSyms * 2, `${debugSyms} vs ${plainSyms} bytes of debug symbols`);

// --- debug alone still cannot compile a contract ---------------------------------------
const asProgram = compile({ files, package_dir: "ctr", mode: "debug" });
ok("`debug` alone still fails on a contract crate", asProgram.ok === false);
ok("…for want of a `main`",
   (asProgram.diagnostics ?? []).some((d) => d.message.includes("main")),
   JSON.stringify((asProgram.diagnostics ?? []).map((d) => d.message).slice(0, 2)));

// --- an unknown mode is refused, not degraded ------------------------------------------
const unknown = compile({ files, package_dir: "ctr", mode: "contract_debug" });
ok("an unknown mode is refused", unknown.ok === false);
ok("…as `unknown-mode`", unknown.kind === "unknown-mode", unknown.kind);
ok("…naming the mode it was given", (unknown.message ?? "").includes("`contract_debug`"),
   unknown.message);
for (const m of ["resolve", "program", "contract", "debug", "contract-debug"]) {
  ok(`…and offering \`${m}\``, (unknown.message ?? "").includes(m));
}
// The old behaviour, named: it compiled a `program` and reported a diagnostic against a
// stdlib file the caller never wrote.
ok("…with no diagnostics, because nothing was compiled",
   (unknown.diagnostics ?? []).length === 0,
   JSON.stringify((unknown.diagnostics ?? []).map((d) => d.file)));
ok("…and no stdlib file named in the answer",
   !JSON.stringify(unknown).includes("aes128"));

// THE PROPERTY THE BARE ABI EXISTS FOR: none of the declared JS imports was reached,
// so a page can drive the compiler with stubs and no wasm-bindgen glue.
ok(`none of the ${declared.length} declared imports was reached`, reached === 0,
   reachedNames.join(", "));

console.log(failures === 0 ? "wasm module: OK" : `wasm module: ${failures} FAILED`);
process.exit(failures === 0 ? 0 : 1);
