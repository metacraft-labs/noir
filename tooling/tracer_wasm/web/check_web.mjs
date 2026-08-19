// Verify the demo page in a *real browser*, by driving it the way a user would.
//
//   node check_web.mjs [--keep] [--chromium <path>] [--port <n>]
//
// Serves `tooling/tracer_wasm/web/` over HTTP (wasm needs a real origin and the
// right MIME type; `file://` will not do), opens it in headless Chromium over
// the DevTools protocol, clicks the Trace button, and reads the counts the page
// rendered back out of the DOM. Fails loudly on any page error or console error.
//
// This asserts nothing about the page that it did not observe: the numbers it
// prints are scraped from the rendered table, and the elapsed time is the
// page's own measurement of the wasm call.

import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, extname, join, normalize } from 'node:path';
import { fileURLToPath } from 'node:url';

const WEB_DIR = dirname(fileURLToPath(import.meta.url));

const argv = process.argv.slice(2);
const flag = (name, fallback) => {
  const i = argv.indexOf(`--${name}`);
  return i === -1 ? fallback : argv[i + 1];
};
const CHROMIUM = flag('chromium', process.env.CHROMIUM ?? '/usr/bin/chromium');
const PORT = Number(flag('port', '8731'));

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  // The one that matters: `WebAssembly.instantiateStreaming` and a strict
  // `fetch` both require `application/wasm`.
  '.wasm': 'application/wasm',
};

function fail(message) {
  console.error(`FAIL: ${message}`);
  process.exitCode = 1;
  throw new Error(message);
}

// ---------------------------------------------------------------- static server

function serve() {
  const server = createServer(async (req, res) => {
    const rel = normalize(decodeURIComponent(req.url.split('?')[0])).replace(/^(\.\.[/\\])+/, '');
    const path = join(WEB_DIR, rel === '/' ? 'index.html' : rel);
    try {
      const body = await readFile(path);
      res.writeHead(200, {
        'content-type': MIME[extname(path)] ?? 'application/octet-stream',
        'content-length': body.length,
      });
      res.end(body);
    } catch {
      res.writeHead(404).end('not found');
    }
  });
  return new Promise((resolve) => server.listen(PORT, '127.0.0.1', () => resolve(server)));
}

// ------------------------------------------------------------------------- CDP

class Cdp {
  #ws;
  #next = 1;
  #pending = new Map();
  #handlers = new Map();

  static async connect(url) {
    const cdp = new Cdp();
    cdp.#ws = new WebSocket(url);
    await new Promise((resolve, reject) => {
      cdp.#ws.addEventListener('open', resolve, { once: true });
      cdp.#ws.addEventListener('error', () => reject(new Error(`cannot reach ${url}`)), {
        once: true,
      });
    });
    cdp.#ws.addEventListener('message', (event) => {
      const message = JSON.parse(event.data);
      if (message.id !== undefined) {
        const entry = cdp.#pending.get(message.id);
        cdp.#pending.delete(message.id);
        if (!entry) return;
        message.error ? entry.reject(new Error(JSON.stringify(message.error))) : entry.resolve(message.result);
      } else {
        cdp.#handlers.get(message.method)?.forEach((h) => h(message.params));
      }
    });
    return cdp;
  }

  on(method, handler) {
    if (!this.#handlers.has(method)) this.#handlers.set(method, []);
    this.#handlers.get(method).push(handler);
  }

  send(method, params = {}, sessionId) {
    const id = this.#next++;
    this.#ws.send(JSON.stringify({ id, method, params, sessionId }));
    return new Promise((resolve, reject) => this.#pending.set(id, { resolve, reject }));
  }

  close() {
    this.#ws.close();
  }
}

// ------------------------------------------------------------------------ main

const wasmPath = join(WEB_DIR, 'noir_tracer_wasm.wasm');
if (!existsSync(wasmPath)) {
  fail(`${wasmPath} is missing — run \`just build-web\` first.`);
}

const server = await serve();
const origin = `http://127.0.0.1:${PORT}/`;
console.log(`serving ${WEB_DIR} at ${origin}`);

const profile = await import('node:fs/promises').then((fs) =>
  fs.mkdtemp(join(process.env.TMPDIR ?? '/tmp', 'noir-web-check-')),
);
const browser = spawn(CHROMIUM, [
  '--headless=new',
  '--no-sandbox',
  '--disable-gpu',
  '--remote-debugging-port=0',
  `--user-data-dir=${profile}`,
  'about:blank',
]);

const wsUrl = await new Promise((resolve, reject) => {
  let buffered = '';
  const timer = setTimeout(() => reject(new Error('Chromium never printed a DevTools URL')), 30000);
  browser.stderr.on('data', (chunk) => {
    buffered += chunk;
    const match = buffered.match(/DevTools listening on (ws:\/\/\S+)/);
    if (match) {
      clearTimeout(timer);
      resolve(match[1]);
    }
  });
  browser.on('exit', (code) => reject(new Error(`Chromium exited early (${code}): ${buffered}`)));
});

const cdp = await Cdp.connect(wsUrl);
const { targetId } = await cdp.send('Target.createTarget', { url: 'about:blank' });
const { sessionId } = await cdp.send('Target.attachToTarget', { targetId, flatten: true });

const consoleErrors = [];
const pageErrors = [];
cdp.on('Runtime.consoleAPICalled', (p) => {
  if (p.type === 'error') consoleErrors.push(p.args.map((a) => a.value ?? a.description).join(' '));
});
cdp.on('Runtime.exceptionThrown', (p) =>
  pageErrors.push(p.exceptionDetails.exception?.description ?? p.exceptionDetails.text),
);

await cdp.send('Runtime.enable', {}, sessionId);
await cdp.send('Page.enable', {}, sessionId);

const loaded = new Promise((resolve) => cdp.on('Page.loadEventFired', resolve));
await cdp.send('Page.navigate', { url: origin }, sessionId);
await loaded;

const evaluate = async (expression) => {
  const { result, exceptionDetails } = await cdp.send(
    'Runtime.evaluate',
    { expression, awaitPromise: true, returnByValue: true },
    sessionId,
  );
  if (exceptionDetails) {
    fail(`in-page exception: ${exceptionDetails.exception?.description ?? exceptionDetails.text}`);
  }
  return result.value;
};

// Wait for the module to finish instantiating, i.e. for the button to enable.
const ready = await evaluate(`
  (async () => {
    for (let i = 0; i < 600; i++) {
      const status = document.getElementById('status').textContent;
      if (!document.getElementById('run').disabled) return { ok: true, status };
      if (document.getElementById('status').classList.contains('bad')) return { ok: false, status };
      await new Promise((r) => setTimeout(r, 100));
    }
    return { ok: false, status: 'timed out waiting for the module' };
  })()
`);
if (!ready.ok) fail(`the page never became ready: ${ready.status}`);
console.log(`page ready: ${ready.status}`);

// Click the real button and wait for the page to render a result.
const outcome = await evaluate(`
  (async () => {
    document.getElementById('run').click();
    for (let i = 0; i < 1200; i++) {
      const status = document.getElementById('status');
      if (status.classList.contains('bad')) return { ok: false, status: status.textContent };
      if (!document.getElementById('results').classList.contains('hidden')) {
        const counts = {};
        for (const row of document.querySelectorAll('#counts tr')) {
          const cells = row.querySelectorAll('td');
          if (cells.length === 2) counts[cells[0].textContent] = Number(cells[1].textContent);
        }
        return {
          ok: true,
          status: status.textContent,
          counts,
          note: document.getElementById('module-note').textContent,
          stepLines: document.getElementById('steps').textContent.split('\\n').length,
          downloadLabel: document.getElementById('download').textContent,
          downloadHidden: document.getElementById('download').classList.contains('hidden'),
        };
      }
      await new Promise((r) => setTimeout(r, 100));
    }
    return { ok: false, status: 'timed out waiting for a trace' };
  })()
`);

console.log('\n--- what the browser rendered ---');
console.log(JSON.stringify(outcome, null, 2));

// Re-run with *different* source, to show the textarea genuinely drives the
// compile. Without this the whole demo is consistent with the module ignoring
// its input and replaying something baked in at build time.
const EDITED_SOURCE = `fn main(x: u32, y: u32) {
    let mut a = x;
    a += y;
    a += y;
    assert(a == 11);
}
`;
const edited = await evaluate(`
  (async () => {
    document.getElementById('source').value = ${JSON.stringify(EDITED_SOURCE)};
    document.getElementById('inputs').value = 'x = "3"\\ny = "4"\\n';
    document.getElementById('run').click();
    for (let i = 0; i < 1200; i++) {
      const status = document.getElementById('status');
      if (status.classList.contains('bad')) return { ok: false, status: status.textContent };
      if (status.textContent.startsWith('Traced in') && !document.getElementById('run').disabled) {
        const counts = {};
        for (const row of document.querySelectorAll('#counts tr')) {
          const cells = row.querySelectorAll('td');
          if (cells.length === 2) counts[cells[0].textContent] = Number(cells[1].textContent);
        }
        return { ok: true, status: status.textContent, counts };
      }
      await new Promise((r) => setTimeout(r, 100));
    }
    return { ok: false, status: 'timed out on the edited program' };
  })()
`);
console.log('\n--- after editing the source in the page ---');
console.log(JSON.stringify(edited, null, 2));

// And a program that does not compile: the page must surface the diagnostic
// rather than hang or show a stale result.
const broken = await evaluate(`
  (async () => {
    document.getElementById('source').value = 'fn main(x: u32) { let y: Field = x; }';
    document.getElementById('inputs').value = 'x = "1"\\n';
    document.getElementById('run').click();
    for (let i = 0; i < 600; i++) {
      const status = document.getElementById('status');
      if (status.classList.contains('bad')) return { ok: true, message: status.textContent };
      await new Promise((r) => setTimeout(r, 100));
    }
    return { ok: false, message: 'a broken program did not produce an error' };
  })()
`);
console.log('\n--- a program that does not compile ---');
console.log(JSON.stringify(broken, null, 2));

cdp.close();
browser.kill();
server.close();

if (!outcome.ok) fail(outcome.status);
if (pageErrors.length) fail(`page errors: ${pageErrors.join('; ')}`);
if (consoleErrors.length) fail(`console errors: ${consoleErrors.join('; ')}`);
if (outcome.downloadHidden) fail('no download was offered');

// The counts the native `nargo trace` + `ct-print --full` produce for the
// prefilled `a_1_mul` example. Hard-coded so a regression is a test failure
// rather than a number nobody reads.
const EXPECTED = { steps: 14, calls: 1, paths: 1, functions: 1, varnames: 3, io_events: 0 };
for (const [key, want] of Object.entries(EXPECTED)) {
  if (outcome.counts[key] !== want) {
    fail(`${key}: the page rendered ${outcome.counts[key]}, native produces ${want}`);
  }
}

// The edited program must produce a *different* trace. If it did not, every
// number above would be consistent with a module that ignores its input and
// replays something baked in at build time -- which is the one thing this demo
// exists to rule out.
if (!edited.ok) fail(`editing the source failed: ${edited.status}`);
if (edited.counts.steps === outcome.counts.steps) {
  fail(
    `editing the source did not change the trace (${edited.counts.steps} steps both times) — ` +
      'the module may not be reading the textarea',
  );
}

// A program that does not compile must surface the compiler's own diagnostic.
if (!broken.ok) fail(broken.message);
if (!/src\/main\.nr:\d+:\d+/.test(broken.message)) {
  fail(`the compile error carried no source location: ${broken.message}`);
}

console.log('\nPASS: the browser compiled Noir source and traced it inside wasm,');
console.log('      and the counts match native `nargo trace`.');
