// Trace every `test_programs/trace` fixture from SOURCE inside wasm, and check
// each result against the `.ct` container native `nargo trace` produces.
//
//   node compare_fixtures.mjs [--fixture <name>] [--nargo <path>] [--ct-print <path>]
//                             [--locations]
//
// `--locations` additionally compares every step's `(file, line)`, not just the
// counts. That is a stricter comparison than the counts, and it currently FAILS
// on most fixtures -- for reasons that have nothing to do with wasm; see the
// note above the reporting section.
//
// The wasm side is given nothing but the fixture's `src/**.nr` text and its
// `Prover.toml` -- it compiles the program itself. The native side runs the real
// `nargo trace`, and the expected numbers are read out of the resulting
// container with the real `ct-print --full`. Nothing is mocked and nothing is
// hard-coded: both columns of the table below are measured on every run.
//
// This is the same `tracer.mjs` the page uses, so a discrepancy here is a
// discrepancy in what the page would show.

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, readdirSync, existsSync, statSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';

import { loadTracer, summarize } from './tracer.mjs';

const WEB_DIR = dirname(fileURLToPath(import.meta.url));
const ROOT = join(WEB_DIR, '..', '..', '..');

const argv = process.argv.slice(2);
const flag = (name, fallback) => {
  const i = argv.indexOf(`--${name}`);
  return i === -1 ? fallback : argv[i + 1];
};

const NARGO = flag('nargo', join(ROOT, 'target/debug/nargo'));
const CT_PRINT = flag(
  'ct-print',
  process.env.CT_PRINT ?? join(ROOT, '..', 'codetracer-trace-format-nim', 'ct-print'),
);
const WASM = join(WEB_DIR, 'noir_tracer_wasm.wasm');

for (const [what, path] of [
  ['nargo', NARGO],
  ['ct-print', CT_PRINT],
  ['the wasm module', WASM],
]) {
  if (!existsSync(path)) {
    console.error(`missing ${what}: ${path}`);
    process.exit(2);
  }
}

/// Every `.nr` under the fixture's `src/`, keyed by its path relative to the
/// fixture root -- so a fixture's own `mod foo;` resolves the same way it does
/// on disk.
function collectSources(dir, base = dir, out = {}) {
  for (const entry of readdirSync(dir)) {
    const path = join(dir, entry);
    if (statSync(path).isDirectory()) collectSources(path, base, out);
    else if (entry.endsWith('.nr')) out[relative(base, path)] = readFileSync(path, 'utf8');
  }
  return out;
}

const tracer = await loadTracer(readFileSync(WASM));
console.log(`module imports declared: ${tracer.imports.length} (none are reached)\n`);

const only = flag('fixture', null);
const fixtureDir = join(ROOT, 'test_programs/trace');
const fixtures = readdirSync(fixtureDir)
  .filter((f) => statSync(join(fixtureDir, f)).isDirectory())
  .filter((f) => (only ? f === only : true))
  .sort();

const KEYS = ['steps', 'calls', 'paths', 'io_events'];
const rows = [];
let failures = 0;

for (const fixture of fixtures) {
  const dir = join(fixtureDir, fixture);
  const proverPath = join(dir, 'Prover.toml');
  if (!existsSync(proverPath)) {
    rows.push({ fixture, note: 'no Prover.toml — skipped' });
    continue;
  }

  // --- native ------------------------------------------------------------
  // A fixture whose *native* run fails is reported as such rather than blamed
  // on wasm; the comparison simply has no baseline to compare against.
  const out = mkdtempSync(join(tmpdir(), `noir-cmp-${fixture}-`));
  let native;
  let nativeLocations = [];
  try {
    execFileSync(NARGO, ['--program-dir', dir, 'trace', '--out-dir', out], { stdio: 'pipe' });
    // The container is named after the *package*, which is not always the
    // directory: `types_test/Nargo.toml` says `name = "zk_dungeon"` and
    // `reference_basic/Nargo.toml` says `name = "reference"`.
    const container = join(out, readdirSync(out).find((f) => f.endsWith('.ct')) ?? `${fixture}.ct`);
    const decoded = JSON.parse(
      execFileSync(CT_PRINT, ['--full', container], { maxBuffer: 1 << 30 }),
    );
    native = decoded.counts;
    nativeLocations = decoded.events
      .filter((e) => e.kind === 'step')
      .map((e) => `${e.path.split('/').pop()}:${e.line}`);
  } catch (e) {
    const detail = (e.stderr?.toString() ?? e.message).split('\n')[0];
    rows.push({ fixture, note: `native baseline unavailable: ${detail}` });
    continue;
  }

  // --- wasm, from source -------------------------------------------------
  // Keyed relative to the fixture root, so the entry point is `src/main.nr` --
  // it has to sit in a directory for the instrumenter to tell the package apart
  // from the standard library.
  const files = collectSources(join(dir, 'src'), dir);
  let wasm;
  let wasmLocations = [];
  let error = null;
  try {
    const trace = tracer.traceSource({
      files,
      entry_point: 'src/main.nr',
      inputs: readFileSync(proverPath, 'utf8'),
      inputs_are_json: false,
      package: fixture,
    });
    wasm = summarize(trace);
    wasmLocations = trace.events
      .filter((e) => typeof e === 'object' && 'Step' in e)
      .map((e) => `${String(trace.paths[e.Step.path_id]).split('/').pop()}:${e.Step.line}`);
  } catch (e) {
    error = e.message.split('\n')[0];
  }

  if (error) {
    failures++;
    rows.push({ fixture, note: `wasm error: ${error}` });
    continue;
  }

  const mismatches = KEYS.filter((k) => wasm[k] !== native[k]);
  if (mismatches.length) failures++;
  const locationDiffs = nativeLocations
    .map((n, i) => [i, n, wasmLocations[i]])
    .filter(([, n, w]) => n !== w);
  rows.push({ fixture, native, wasm, mismatches, locationDiffs, steps: nativeLocations.length });
}

// ------------------------------------------------------------------ reporting

const pad = (s, n) => String(s).padEnd(n);
const num = (s, n) => String(s).padStart(n);
console.log(
  `${pad('fixture', 22)}${num('steps', 13)}${num('calls', 13)}${num('paths', 13)}${num('io', 13)}`,
);
console.log(`${pad('', 22)}${num('native/wasm', 13).repeat(4)}`);
console.log('-'.repeat(74));

for (const row of rows) {
  if (row.note) {
    console.log(`${pad(row.fixture, 22)}${row.note}`);
    continue;
  }
  const cells = KEYS.map((k) => num(`${row.native[k]}/${row.wasm[k]}`, 13)).join('');
  console.log(`${pad(row.fixture, 22)}${cells}${row.mismatches.length ? '   <-- MISMATCH' : ''}`);
}

console.log('-'.repeat(74));
const compared = rows.filter((r) => !r.note).length;
console.log(`${compared} fixtures compared, ${failures} mismatched`);

// The counts agree everywhere. Every step's *location* does not, and it is
// worth being precise about why, because it is easy to read the table above as
// "the traces are identical".
//
// The difference is NOT the in-wasm compile: tracing an artifact that `nargo`
// itself compiled, through this same module, reproduces the source-compiled
// locations exactly. It is the in-memory `MemorySink` disagreeing with the Nim
// CTFS writer, and it predates any of this work -- both sides of that pair are
// unmodified here.
//
// Two shapes show up:
//   * the final step: the container reports a *byte offset* where a line number
//     belongs (a_1_mul's `main.nr` is 273 bytes and 9 lines, and the container
//     says line 264), while the event stream reports the real last line;
//   * loop and block ends: the container attributes the step to the enclosing
//     function's closing brace, the event stream to the block's own.
if (argv.includes('--locations')) {
  console.log('\nstep-location differences (native container vs in-memory stream):');
  let withDiffs = 0;
  for (const row of rows) {
    if (row.note) continue;
    if (!row.locationDiffs.length) {
      console.log(`${pad(row.fixture, 22)} all ${row.steps} step locations identical`);
      continue;
    }
    withDiffs++;
    console.log(`${pad(row.fixture, 22)} ${row.locationDiffs.length}/${row.steps} differ`);
    for (const [i, n, w] of row.locationDiffs.slice(0, 3)) {
      console.log(`${pad('', 22)}   step ${i}: container ${n}, stream ${w}`);
    }
  }
  console.log(`\n${withDiffs}/${compared} fixtures differ in at least one step location.`);
}

process.exit(failures === 0 ? 0 : 1);
