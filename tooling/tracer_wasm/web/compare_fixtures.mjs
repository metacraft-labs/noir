// Trace every `test_programs/trace` fixture from SOURCE inside wasm, and check
// each result against the `.ct` container native `nargo trace` produces.
//
//   node compare_fixtures.mjs [--fixture <name>] [--nargo <path>] [--ct-print <path>]
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
  try {
    execFileSync(NARGO, ['--program-dir', dir, 'trace', '--out-dir', out], { stdio: 'pipe' });
    // The container is named after the *package*, which is not always the
    // directory: `types_test/Nargo.toml` says `name = "zk_dungeon"` and
    // `reference_basic/Nargo.toml` says `name = "reference"`.
    const container = join(out, readdirSync(out).find((f) => f.endsWith('.ct')) ?? `${fixture}.ct`);
    native = JSON.parse(execFileSync(CT_PRINT, ['--full', container], { maxBuffer: 1 << 30 }))
      .counts;
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
  let error = null;
  try {
    wasm = summarize(
      tracer.traceSource({
        files,
        entry_point: 'src/main.nr',
        inputs: readFileSync(proverPath, 'utf8'),
        inputs_are_json: false,
        package: fixture,
      }),
    );
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
  rows.push({ fixture, native, wasm, mismatches });
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
process.exit(failures === 0 ? 0 : 1);
