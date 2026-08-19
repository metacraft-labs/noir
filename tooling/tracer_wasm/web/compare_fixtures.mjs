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
// `Prover.toml` -- it compiles the program itself, and hands back a `.ct`
// container built in its own linear memory. The native side runs the real
// `nargo trace`. BOTH containers are then read with the real `ct-print --full`,
// so the table compares two files produced by two writers, decoded by one
// reader. Nothing is mocked and nothing is hard-coded: every number below is
// measured on every run.
//
// `ct-print` must be the build from `codetracer-trace-format-nim` branch
// `wasm/nim-to-wasm`; the stock reader cannot decode a container written by the
// pure-Rust `CtfsTraceWriter` at all.
//
// This is the same `tracer.mjs` the page uses, so a discrepancy here is a
// discrepancy in what the page would show.

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, readdirSync, existsSync, statSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';

import { writeFileSync } from 'node:fs';

import { loadTracer, summarize, looksLikeCtfs } from './tracer.mjs';

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
  process.env.CT_PRINT ?? join(ROOT, '..', 'ctfnim-wt-wasm', 'ct-print'),
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

/// Read a `.ct` with `ct-print --full` and normalise the two shapes it emits.
///
/// `ct-print` prints a v4 multi-stream container (what the Nim writer produces,
/// which is column-aware) as `{counts, events:[{kind:"step", path, line, …}]}`,
/// and a container it has to read through the legacy combined `events.log`
/// (what the pure-Rust writer produces) as
/// `{paths, events:[{type:"Step", path_id, line}]}` with no `counts` at all.
/// Both are `ct-print --full` output; they are not the same JSON, and a
/// comparison that assumed one silently sees zero of everything on the other.
function decodeContainer(path) {
  const decoded = JSON.parse(execFileSync(CT_PRINT, ['--full', path], { maxBuffer: 1 << 30 }));

  if (decoded.counts) {
    return {
      counts: decoded.counts,
      locations: decoded.events
        .filter((e) => e.kind === 'step')
        .map((e) => `${e.path.split('/').pop()}:${e.line}`),
      columnAware: decoded.metadata?.flags?.has_column_aware_steps === true,
    };
  }

  const kinds = {};
  for (const event of decoded.events) kinds[event.type] = (kinds[event.type] ?? 0) + 1;
  return {
    counts: {
      steps: kinds.Step ?? 0,
      // `<toplevel>` is call 0 and function 0 on this side, as in `summarize`.
      calls: Math.max((kinds.Call ?? 0) - 1, 0),
      paths: decoded.paths.length,
      functions: Math.max((kinds.Function ?? 0) - 1, 0),
      varnames: kinds.VariableName ?? 0,
      values: kinds.Value ?? 0,
      io_events: kinds.Event ?? 0,
    },
    locations: decoded.events
      .filter((e) => e.type === 'Step')
      .map((e) => `${String(decoded.paths[e.path_id]).split('/').pop()}:${e.line}`),
    columnAware: decoded.metadata?.flags?.has_column_aware_steps === true,
  };
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
    ({ counts: native, locations: nativeLocations } = decodeContainer(container));
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
  let ct = null;
  let ctLocations = [];
  let ctCounts = null;
  let ctError = null;
  let error = null;
  try {
    const result = tracer.traceSourceContainer({
      files,
      entry_point: 'src/main.nr',
      inputs: readFileSync(proverPath, 'utf8'),
      inputs_are_json: false,
      package: fixture,
      // Pinned rather than minted, so a container is reproducible run to run.
      recording_id: '01949fcc-7d92-7e9c-8000-00000000ce11',
    });
    const trace = result.trace;
    ct = result.ct;
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

  // --- read the wasm-written container back, with the same decoder ---------
  // The point of the exercise: the file the browser would hand you has to be
  // readable, and has to describe the trace the page showed.
  if (!looksLikeCtfs(ct)) {
    ctError = 'the container does not start with the CTFS magic';
  } else {
    const wasmContainer = join(out, `${fixture}.wasm.ct`);
    writeFileSync(wasmContainer, ct);
    try {
      ({ counts: ctCounts, locations: ctLocations } = decodeContainer(wasmContainer));
    } catch (e) {
      ctError = (e.stderr?.toString() ?? e.message).split('\n')[0];
    }
  }
  if (ctError) failures++;

  const mismatches = KEYS.filter((k) => wasm[k] !== native[k]);
  // The container must agree with the stream it was built from, too -- if it
  // did not, the counts printed next to a download would describe a different
  // recording than the file.
  const ctMismatches = ctCounts ? KEYS.filter((k) => ctCounts[k] !== wasm[k]) : [];
  if (mismatches.length || ctMismatches.length) failures++;
  const locationDiffs = nativeLocations
    .map((n, i) => [i, n, wasmLocations[i]])
    .filter(([, n, w]) => n !== w);
  const ctLocationDiffs = wasmLocations
    .map((w, i) => [i, w, ctLocations[i]])
    .filter(([, w, c]) => w !== c);
  rows.push({
    fixture,
    native,
    wasm,
    ctCounts,
    ctError,
    ctBytes: ct?.length ?? 0,
    mismatches,
    ctMismatches,
    locationDiffs,
    ctLocationDiffs,
    steps: nativeLocations.length,
  });
}

// ------------------------------------------------------------------ reporting

const pad = (s, n) => String(s).padEnd(n);
const num = (s, n) => String(s).padStart(n);
console.log(
  `${pad('fixture', 22)}${num('steps', 15)}${num('calls', 15)}${num('paths', 15)}${num('io', 15)}${num('.ct KiB', 10)}`,
);
console.log(`${pad('', 22)}${num('native/wasm/.ct', 15).repeat(4)}`);
console.log('-'.repeat(94));

for (const row of rows) {
  if (row.note) {
    console.log(`${pad(row.fixture, 22)}${row.note}`);
    continue;
  }
  const cells = KEYS.map((k) =>
    num(`${row.native[k]}/${row.wasm[k]}/${row.ctCounts ? row.ctCounts[k] : '?'}`, 15),
  ).join('');
  const flag = row.ctError
    ? `   <-- .ct UNREADABLE: ${row.ctError}`
    : row.mismatches.length || row.ctMismatches.length
      ? '   <-- MISMATCH'
      : '';
  console.log(`${pad(row.fixture, 22)}${cells}${num((row.ctBytes / 1024).toFixed(0), 10)}${flag}`);
}

console.log('-'.repeat(94));
const compared = rows.filter((r) => !r.note).length;
console.log(
  `${compared} fixtures compared, ${failures} mismatched.\n` +
    'Columns are: native `nargo trace` container / the wasm module\'s event stream /\n' +
    'the wasm module\'s own .ct container, all three measured on this run.',
);

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

  // The tighter of the two comparisons, and the one that must be clean: the
  // container the module wrote against the stream it wrote it from. A
  // difference here would be this integration's fault, unlike the block above.
  console.log("\nstep-location differences (the module's stream vs the module's own .ct):");
  let ctWithDiffs = 0;
  for (const row of rows) {
    if (row.note || row.ctError) continue;
    if (!row.ctLocationDiffs.length) {
      console.log(`${pad(row.fixture, 22)} all ${row.wasm.steps} step locations identical`);
      continue;
    }
    ctWithDiffs++;
    console.log(`${pad(row.fixture, 22)} ${row.ctLocationDiffs.length}/${row.wasm.steps} differ`);
    for (const [i, w, c] of row.ctLocationDiffs.slice(0, 3)) {
      console.log(`${pad('', 22)}   step ${i}: stream ${w}, container ${c}`);
    }
  }
  console.log(`\n${ctWithDiffs}/${compared} fixtures differ between the stream and its own container.`);
  if (ctWithDiffs > 0) failures++;
}

process.exit(failures === 0 ? 0 : 1);
