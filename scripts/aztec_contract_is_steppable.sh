#!/usr/bin/env bash
#
# aztec_contract_is_steppable.sh — an Aztec contract compiles in a DEBUGGABLE form, and
# the artifact it produces is one a tracer can actually step.
#
# ## What this exists to prove
#
# `compile_vfs.rs` used to derive two booleans from one mode string —
# `as_contract = mode == "contract"` and `for_debugging = mode == "debug"` — while
# `vfs::compile_resolved(plan, files, as_contract, for_debugging)` takes them
# INDEPENDENTLY. `as_contract && for_debugging` was therefore unreachable, and since
# `debug` is `compile_main` and a contract crate has no `main`, a contract could not be
# made steppable in one compile or in ten.
#
# The claim a build had to settle — and which could NOT be settled by reading the source —
# is whether `compile_contract` under `instrument_debug: true, force_brillig: true`
# yields a TRACER-CONSUMABLE artifact. The failure mode being guarded against is one this
# campaign has already met: an uninstrumented artifact traces to ONE event and ZERO steps
# while the compiler and the tracer both cheerfully report success. A trace that exists
# but has no steps is the exact shape of a false pass, so nothing below asserts "a trace
# came back". It asserts the STEP COUNT, and prints it.
#
# ## Usage
#
#   bash scripts/aztec_contract_is_steppable.sh
#
# `AZTEC_VFS_JSON` may point at an already-vendored tree; otherwise this vendors one with
# `tools/vendor_noir_tree.py` from the aztec-avm-runtime repository (see AZTEC_TOOLS).

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK="${AZTEC_STEPPABLE_WORK:-${TMPDIR:-/tmp}/aztec-contract-steppable}"
mkdir -p "${WORK}"

PASS=0
FAIL=0

pass() {
	PASS=$((PASS + 1))
	echo "  ok   $1"
}
fail() {
	FAIL=$((FAIL + 1))
	echo "  FAIL $1" >&2
}
assert_eq() {
	# assert_eq <what> <expected> <actual>
	if [ "$2" = "$3" ]; then pass "$1 ($3)"; else fail "$1: expected [$2], got [$3]"; fi
}
assert_true() {
	local what="$1"
	shift
	if "$@" >/dev/null 2>&1; then pass "${what}"; else fail "${what}"; fi
}
# A numeric floor, because "greater than zero" is the assertion that let an
# uninstrumented artifact through once already.
assert_ge() {
	if [ "$3" -ge "$2" ] 2>/dev/null; then pass "$1 ($3 >= $2)"; else fail "$1: $3 < $2"; fi
}

echo "== 0. the checkout under test"
NOIR_REV="$(git -C "${REPO_ROOT}" rev-parse HEAD 2>/dev/null)"
echo "  noir:            ${REPO_ROOT}"
echo "  rev:             ${NOIR_REV}"
echo "  compiler/wasm:   $(git -C "${REPO_ROOT}" rev-parse HEAD:compiler/wasm/src 2>/dev/null)"
# A stale sibling checkout has already produced one wrong conclusion in this campaign, so
# the tree being measured names itself rather than being assumed.
assert_true "the working tree is clean, so the rev above describes what is tested" \
	test -z "$(git -C "${REPO_ROOT}" status --porcelain)"

# ------------------------------------------------------------------------------------
echo
echo "== 1. the vendored aztec-nr tree"
# ------------------------------------------------------------------------------------
if [ -z "${AZTEC_VFS_JSON:-}" ]; then
	AZTEC_TOOLS="${AZTEC_TOOLS:-$(cd "${REPO_ROOT}/.." && pwd)/aztec-vendoraztec}"
	AZTEC_PACKAGES="${AZTEC_PACKAGES:-$(cd "${REPO_ROOT}/.." && pwd)/aztec-packages}"
	CONTRACT_DIR="${AZTEC_CONTRACT_DIR:-${AZTEC_PACKAGES}/noir-projects/labs/noir-contracts/contracts/app/simple_token_contract}"
	GIT_DEPS_ROOT="${AZTEC_GIT_DEPS_ROOT:-${HOME}/.cache/aztec-vendor-noirlibs}"
	VENDOR_TOOL="${AZTEC_TOOLS}/tools/vendor_noir_tree.py"

	if [ ! -f "${VENDOR_TOOL}" ]; then
		echo "  the vendoring tool is not at ${VENDOR_TOOL}" >&2
		echo "  remedy: set AZTEC_VFS_JSON to an already-vendored tree, or AZTEC_TOOLS to" >&2
		echo "          the aztec-avm-runtime checkout holding tools/vendor_noir_tree.py" >&2
		exit 2
	fi
	AZTEC_VFS_JSON="${WORK}/vfs.json"
	rm -f "${AZTEC_VFS_JSON}" "${AZTEC_VFS_JSON}.manifest.json"
	python3 "${VENDOR_TOOL}" --entry "${CONTRACT_DIR}" --roots "${GIT_DEPS_ROOT}" \
		--out "${AZTEC_VFS_JSON}" >"${WORK}/vendor.log" 2>&1
	vendor_status=$?
	assert_eq "the vendoring succeeded" "0" "${vendor_status}"
fi
export AZTEC_VFS_JSON
export AZTEC_VFS_PACKAGE_DIR="${AZTEC_VFS_PACKAGE_DIR:-contract}"

assert_true "the vendored tree exists" test -f "${AZTEC_VFS_JSON}"
VFS_FACTS="$(python3 - "${AZTEC_VFS_JSON}" <<'PY'
import json, sys
v = json.load(open(sys.argv[1], encoding="utf-8"))
raw = open(sys.argv[1], encoding="utf-8").read()
print(len(v))
print(sum(len(s.encode()) for s in v.values()))
print(sum(1 for p in v if p.endswith("Nargo.toml")))
print(1 if 'git = "' in raw else 0)
PY
)"
VFS_FILES="$(echo "${VFS_FACTS}" | sed -n 1p)"
VFS_BYTES="$(echo "${VFS_FACTS}" | sed -n 2p)"
VFS_MANIFESTS="$(echo "${VFS_FACTS}" | sed -n 3p)"
VFS_GIT="$(echo "${VFS_FACTS}" | sed -n 4p)"
assert_ge "the tree is the real aztec-nr closure, in files" "400" "${VFS_FILES}"
assert_ge "…and in source bytes" "4000000" "${VFS_BYTES}"
assert_eq "…spanning the nine vendored packages" "9" "${VFS_MANIFESTS}"
# The compiler refuses `git` dependencies by name; a tree with one left has not been
# vendored, and every compile below would fail at resolve for a reason unrelated to modes.
assert_eq "…with every git dependency rewritten to a path" "0" "${VFS_GIT}"

# ------------------------------------------------------------------------------------
echo
echo "== 2. the compiler's own tests, including the three that need the tree"
# ------------------------------------------------------------------------------------
run_tests() {
	# run_tests <log> [extra cargo test args...]
	local log="$1"
	shift
	(cd "${REPO_ROOT}" && cargo test -p noir_wasm --lib "$@") >"${log}" 2>&1
	return $?
}

# The ordinary suite: the mode table, the unknown-mode refusal, and the synthetic
# contract that is compiled for debugging and then actually traced.
run_tests "${WORK}/unit.log"
assert_eq "the noir_wasm unit suite passes" "0" "$?"
UNIT_LINE="$(grep -E '^test result:' "${WORK}/unit.log" | tail -1)"
echo "  ${UNIT_LINE}"
UNIT_PASSED="$(echo "${UNIT_LINE}" | sed -n 's/.*ok\. \([0-9]*\) passed.*/\1/p')"
UNIT_FAILED="$(echo "${UNIT_LINE}" | sed -n 's/.*passed; \([0-9]*\) failed.*/\1/p')"
assert_eq "…with no failures" "0" "${UNIT_FAILED}"
assert_ge "…and a substantive number of tests actually ran" "40" "${UNIT_PASSED:-0}"

# The four Aztec arms. They are `#[ignore]` so a bare `cargo test` does not pretend to
# cover them; running them here with the PASS COUNT ASSERTED is what stops "it was
# ignored" from being mistaken for "it passed".
run_tests "${WORK}/aztec.log" -- --ignored --nocapture --test-threads=1
AZTEC_STATUS=$?
sed -n 's/^\(SimpleToken.*\)$/  \1/p;s/^\(Stepping::.*\)$/  \1/p;s/^\( *[0-9]* steps in.*\)$/  \1/p;s/^\( *[0-9]* of 27 entrypoints.*\)$/  \1/p;s/^\( *control for.*\)$/  \1/p;s/^\( *oracle answers for.*\)$/  \1/p' \
	"${WORK}/aztec.log"
assert_eq "the four Aztec arms pass" "0" "${AZTEC_STATUS}"
AZTEC_LINE="$(grep -E '^test result:' "${WORK}/aztec.log" | tail -1)"
AZTEC_PASSED="$(echo "${AZTEC_LINE}" | sed -n 's/.*ok\. \([0-9]*\) passed.*/\1/p')"
assert_eq "…and all four of them RAN rather than being ignored" "4" "${AZTEC_PASSED:-0}"

# The numbers themselves, lifted out of the log so this script reports a result rather
# than a chain of green ticks.
STEPS="$(sed -n 's/.*: \([0-9]*\) source-level steps in.*/\1/p' "${WORK}/aztec.log" | tail -1)"
OWN="$(sed -n 's/^ *\([0-9]*\) steps in stepping\/src\/main.nr over \([0-9]*\) distinct lines/\1 \2/p' "${WORK}/aztec.log")"
LOCATED="$(sed -n 's/.*instrumented, \([0-9]*\) located brillig opcodes.*/\1/p' "${WORK}/aztec.log")"
assert_ge "a contract on the real Aztec tree traces to source-level steps" "8" "${STEPS:-0}"
assert_ge "…and the artifact maps brillig opcodes to source in quantity" "10000" "${LOCATED:-0}"

# ------------------------------------------------------------------------------------
# The oracle host's own numbers. `the_aztec_entrypoints_halt_at_the_first_oracle` used to
# stand here recording 27/27 entrypoints halting with a best step count of 1; it was
# REMOVED rather than softened, under the removal rule it stated itself ("replaced by a
# real step-count assertion over SimpleToken itself"). These are that replacement.
# ------------------------------------------------------------------------------------
STEPPED="$(sed -n 's/^ *\([0-9]*\) of 27 entrypoints stepped;.*/\1/p' "${WORK}/aztec.log")"
TOTAL_OWN="$(sed -n 's/.* \([0-9]*\) source-level steps in contract\/src\/main.nr in total.*/\1/p' "${WORK}/aztec.log")"
BEST_STEPS="$(sed -n 's/.*best is [^ ]* with \([0-9]*\) steps over \([0-9]*\) distinct lines.*/\1/p' "${WORK}/aztec.log")"
BEST_LINES="$(sed -n 's/.*best is [^ ]* with \([0-9]*\) steps over \([0-9]*\) distinct lines.*/\2/p' "${WORK}/aztec.log")"
CONTROL="$(sed -n 's/^ *control for [^:]*: \([0-9]*\) step(s).*/\1/p' "${WORK}/aztec.log")"
REFUSALS="$(sed -n 's/^ *\([0-9]*\) entrypoints stopped at a NAMED oracle refusal.*/\1/p' "${WORK}/aztec.log")"

assert_ge "SimpleToken entrypoints step through their own source" "8" "${STEPPED:-0}"
assert_ge "…for a substantive total step count in the contract's own file" "400" "${TOTAL_OWN:-0}"
assert_ge "…with the best single entrypoint stepping substantively" "100" "${BEST_STEPS:-0}"
assert_ge "…over several distinct lines, so the steps ADVANCE" "5" "${BEST_LINES:-0}"
# The control is the whole point: the SAME artifact, no oracle host, one step and `ok`.
# If this stops being 1 the halt has another cause and every number above moved with it.
assert_eq "…while the identical artifact with NO oracle host still halts after one step" \
	"1" "${CONTROL:-0}"
assert_ge "…and the entrypoints this host cannot serve stop at a NAMED refusal" "10" "${REFUSALS:-0}"

# ------------------------------------------------------------------------------------
echo
echo "== 2b. the tracer records a field element wider than i128"
# ------------------------------------------------------------------------------------
# Recording a Poseidon digest used to abort the trace (`field element too large for
# i128`), and values between i64::MAX and i128::MAX were silently TRUNCATED by the `as
# i64` on the same line. Both are unavoidable on real Aztec contract code, so the fix has
# its own unit arms rather than being implied by the step counts above.
(cd "${REPO_ROOT}" && cargo test -p noir_tracer --lib field_recording_tests) \
	>"${WORK}/field.log" 2>&1
assert_eq "the field-recording arms pass" "0" "$?"
FIELD_LINE="$(grep -E '^test result:' "${WORK}/field.log" | tail -1)"
FIELD_PASSED="$(echo "${FIELD_LINE}" | sed -n 's/.*ok\. \([0-9]*\) passed.*/\1/p')"
assert_eq "…and all five of them ran" "5" "${FIELD_PASSED:-0}"

# ------------------------------------------------------------------------------------
echo
echo "== 3. the same two modes, through the wasm module the deploy ships"
# ------------------------------------------------------------------------------------
# The native tests exercise `run_request`; a browser reaches it through the bare C ABI in
# a `wasm32-unknown-unknown` cdylib. Those are the bytes a user runs, so the two modes
# this change adds are driven through the module itself rather than only through cargo.
MODULE="${REPO_ROOT}/target/wasm32-unknown-unknown/release/noir_wasm.wasm"
if [ ! -f "${MODULE}" ]; then
	echo "  building the wasm module (this is what the deploy pin names) ..."
	(cd "${REPO_ROOT}/compiler/wasm" && cargo build --release \
		--target wasm32-unknown-unknown) >"${WORK}/wasm-build.log" 2>&1
	assert_eq "the wasm module builds" "0" "$?"
fi
assert_true "the wasm module exists" test -f "${MODULE}"
MODULE_BYTES="$(wc -c <"${MODULE}" | tr -d ' ')"
echo "  module: ${MODULE_BYTES} bytes"
assert_eq "…and begins with the wasm magic" "0061736d" \
	"$(head -c 4 "${MODULE}" | od -An -tx1 | tr -d ' \n')"
# An order-of-magnitude floor, matching the pin's own reasoning: a module that arrives at
# 4 KB is a build that emitted an error page.
assert_ge "…and is a whole compiler rather than a stub" "10000000" "${MODULE_BYTES}"

if command -v node >/dev/null 2>&1; then
	node "${REPO_ROOT}/scripts/drive_noir_wasm_modes.mjs" "${MODULE}" >"${WORK}/wasm.log" 2>&1
	WASM_STATUS=$?
	sed 's/^/  /' "${WORK}/wasm.log"
	assert_eq "the module answers contract-debug and refuses an unknown mode" "0" "${WASM_STATUS}"
else
	fail "node is required to drive the wasm module"
fi

# ------------------------------------------------------------------------------------
echo
echo "== 4. mutation arms — each must redden ITS OWN assertion"
# ------------------------------------------------------------------------------------
# An arm that is killed by a different check than the one it targets is a miss, so each
# arm below runs ONLY its target test. The mutation is applied to a working tree that is
# restored immediately afterwards; the tree was asserted clean in §0, so the restore is
# exact rather than hopeful.
SRC="${REPO_ROOT}/compiler/wasm/src/compile_vfs.rs"

mutate() {
	# mutate <label> <target test> <expected assertion fragment> <python replacement>
	local label="$1" target="$2" fragment="$3" script="$4"
	python3 - "${SRC}" <<PY
import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
${script}
open(p, "w", encoding="utf-8").write(s)
PY
	local applied=$?
	if [ "${applied}" -ne 0 ]; then
		fail "${label}: the mutation did not apply — its premise has moved"
		git -C "${REPO_ROOT}" checkout -- "${SRC}"
		return
	fi
	(cd "${REPO_ROOT}" && cargo test -p noir_wasm --lib "${target}" -- --exact \
		--include-ignored "compile_vfs::tests::${target}") >"${WORK}/mut-${label}.log" 2>&1
	local status=$?
	git -C "${REPO_ROOT}" checkout -- "${SRC}"

	# The same vacuity guard as `mutate_in`: a test that was ignored or filtered out exits
	# 0, which is indistinguishable from passing.
	local ran
	ran="$(sed -n 's/^test result:.*[.] \([0-9]*\) passed; \([0-9]*\) failed.*/\1 \2/p' \
		"${WORK}/mut-${label}.log" | tail -1 | tr ' ' '+')"
	if [ "$(( ${ran:-0} ))" -eq 0 ]; then
		fail "${label}: ${target} never ran — the arm is vacuous, not covered"
		return
	fi

	if [ "${status}" -eq 0 ]; then
		fail "${label}: ${target} still passed — the mutation is not covered"
		return
	fi
	# Killed — but by its OWN assertion? A compile error, or a panic from some other
	# check, would also be a non-zero status and would prove nothing.
	if grep -q "error\[E[0-9]*\]" "${WORK}/mut-${label}.log"; then
		fail "${label}: the mutant did not compile, so nothing was measured"
		return
	fi
	if grep -qF "${fragment}" "${WORK}/mut-${label}.log"; then
		pass "${label}: ${target} reddened on its own assertion"
	else
		fail "${label}: ${target} failed, but not on [${fragment}]"
	fi
}

# ARM 1 — the defect itself, restored at the call site rather than in the mode table, so
# the table test cannot be the thing that catches it. This is exactly the old behaviour:
# `for_debugging` wins and `as_contract` is dropped.
mutate "exclusive-again" "contract_debug_mode_produces_a_contract_artifact" \
	"contract-debug must compile" \
	'old = "compile_resolved(&plan, &tree, mode.as_contract, mode.for_debugging)"
new = "compile_resolved(&plan, &tree, mode.as_contract && !mode.for_debugging, mode.for_debugging)"
assert old in s, "the dispatch call has moved"
s = s.replace(old, new)'

# ARM 2 — the second defect: an unknown mode falls back to `program` instead of being
# refused, which is how `contract-debug` looked like a real attempt before it existed.
mutate "unknown-degrades" "an_unknown_mode_is_refused_and_named_rather_than_treated_as_a_program" \
	"an unknown mode is not a successful compile" \
	'old = "            _ => return None,"
new = "            _ => (false, false, false),"
assert old in s, "the unknown-mode arm has moved"
s = s.replace(old, new)'

# ARM 3 — the false pass this whole check is built around: `contract-debug` produces a
# contract, but an UNINSTRUMENTED one. Everything still reports success; only the step
# count notices.
mutate "uninstrumented-contract" "a_contract_compiled_for_debugging_traces_with_source_level_steps" \
	"must trace to a substantive number of source-level steps" \
	'old = "            \"contract-debug\" => (true, true, false),"
new = "            \"contract-debug\" => (true, false, false),"
assert old in s, "the contract-debug row has moved"
s = s.replace(old, new)'

# ------------------------------------------------------------------------------------
# Arms for the oracle host. These mutate files OTHER than `compile_vfs.rs`, and some
# target a test in a different crate, so they need the file and the crate as parameters.
# ------------------------------------------------------------------------------------
mutate_in() {
	# mutate_in <label> <file> <crate> <test path> <target filter> <fragment> <python replacement>
	local label="$1" file="$2" krate="$3" testpath="$4" target="$5" fragment="$6" script="$7"
	python3 - "${file}" <<PY
import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
${script}
open(p, "w", encoding="utf-8").write(s)
PY
	local applied=$?
	if [ "${applied}" -ne 0 ]; then
		fail "${label}: the mutation did not apply — its premise has moved"
		git -C "${REPO_ROOT}" checkout -- "${file}"
		return
	fi
	# `--include-ignored` because the Aztec arms are `#[ignore]`: without it cargo runs
	# ZERO tests, exits 0, and the arm reports "not covered" while having measured
	# nothing at all. That is the vacuous arm this campaign keeps meeting, and it cost a
	# full script run to notice.
	(cd "${REPO_ROOT}" && cargo test -p "${krate}" --lib "${target}" -- --exact \
		--include-ignored "${testpath}") >"${WORK}/mut-${label}.log" 2>&1
	local status=$?
	git -C "${REPO_ROOT}" checkout -- "${file}"

	# Did the target actually RUN? A filtered-out or ignored test produces a green exit
	# that is indistinguishable from a passing one, so the count is checked explicitly
	# rather than inferred from the status.
	local ran
	ran="$(sed -n 's/^test result:.*[.] \([0-9]*\) passed; \([0-9]*\) failed.*/\1 \2/p' \
		"${WORK}/mut-${label}.log" | tail -1 | tr ' ' '+')"
	if [ "$(( ${ran:-0} ))" -eq 0 ]; then
		fail "${label}: ${target} never ran — the arm is vacuous, not covered"
		return
	fi

	if [ "${status}" -eq 0 ]; then
		fail "${label}: ${target} still passed — the mutation is not covered"
		return
	fi
	if grep -q "error\[E[0-9]*\]" "${WORK}/mut-${label}.log"; then
		fail "${label}: the mutant did not compile, so nothing was measured"
		return
	fi
	if grep -qF "${fragment}" "${WORK}/mut-${label}.log"; then
		pass "${label}: ${target} reddened on its own assertion"
	else
		fail "${label}: ${target} failed, but not on [${fragment}]"
	fi
}

ORACLES="${REPO_ROOT}/tooling/debugger/src/aztec_oracles.rs"
GLUE="${REPO_ROOT}/tooling/tracer/src/tracer_glue.rs"
# (the tracer_wasm path is no longer mutated directly; see ARM 6)

# ARM 4 — the single most dangerous change that could be made to this host: refusing an
# oracle it cannot answer becomes returning an EMPTY result. Execution then sails past the
# oracle on a value nobody computed, and every step afterwards is confident fiction. The
# step count would go UP, not down, so only the refusal assertion catches this.
mutate_in "refusal-becomes-fabrication" "${ORACLES}" "noir_wasm" \
	"compile_vfs::tests::simpletoken_public_entrypoints_step_through_their_own_source" \
	"simpletoken_public_entrypoints_step_through_their_own_source" \
	"must stop at a refusal that NAMES the" \
	'old = """        self.refusals.insert(name.to_string(), needs.to_string());
        Err(ForeignCallError::NoHandler(name.to_string()))"""
new = """        self.refusals.insert(name.to_string(), needs.to_string());
        Ok(ForeignCallResult::default())"""
assert old in s, "the refusal body has moved"
s = s.replace(old, new)'

# ARM 5 — the fidelity classification stops distinguishing: a public storage read of a slot
# nothing wrote is reported as `Faithful` rather than `DebugLocal`. Every step still
# happens and every count above is unchanged; only the fidelity assertion notices that the
# debugger has started calling an invented value a real one.
mutate_in "fidelity-collapses" "${ORACLES}" "noir_wasm" \
	"compile_vfs::tests::simpletoken_public_entrypoints_step_through_their_own_source" \
	"simpletoken_public_entrypoints_step_through_their_own_source" \
	"MUST be classified debug-local" \
	'old = "                    None => self.single(name, Fidelity::DebugLocal, FieldElement::zero()),"
new = "                    None => self.single(name, Fidelity::Faithful, FieldElement::zero()),"
assert old in s, "the unwritten-slot arm has moved"
s = s.replace(old, new)'

# ARM 6 — the host is never wired into the executor chain, which is the state this
# milestone started in. It is mutated where the TRACER consumes the option rather than
# where `trace_artifact` sets it, because the stepping test passes its own host through
# `trace_artifact_with_options`; mutating the default would leave that path untouched and
# the arm would prove nothing.
mutate_in "host-unwired" "${REPO_ROOT}/tooling/tracer/src/lib.rs" "noir_wasm" \
	"compile_vfs::tests::simpletoken_public_entrypoints_step_through_their_own_source" \
	"simpletoken_public_entrypoints_step_through_their_own_source" \
	"must step substantively through its own source" \
	'old = "        options.aztec_oracles.clone(),"
new = "        None,"
assert old in s, "the tracer no longer threads the oracle host through"
s = s.replace(old, new)'

# ARM 7 — the truncating half of the i128 defect returns: a value above `i64::MAX` is
# squeezed into an `i64` instead of being recorded exactly. Nothing panics and no step
# count changes; the trace just contains a different number than the program computed.
mutate_in "i64-truncates-again" "${GLUE}" "noir_tracer" \
	"tracer_glue::field_recording_tests::a_field_above_i64_max_is_not_silently_truncated" \
	"a_field_above_i64_max_is_not_silently_truncated" \
	"must not be squeezed into Int" \
	'old = """        if let Ok(i) = i64::try_from(wide)
            && (signed || wide >= 0)
        {
            return ValueRecord::Int { i, type_id };
        }"""
new = """        return ValueRecord::Int { i: wide as i64, type_id };"""
assert old in s, "the i64 guard has moved"
s = s.replace(old, new)'

# ARM 8 — the panicking half returns: `to_i128` is reached for a field that does not fit,
# which is what aborted the trace of every contract that hashes anything.
mutate_in "i128-panics-again" "${GLUE}" "noir_tracer" \
	"tracer_glue::field_recording_tests::a_field_wider_than_i128_records_as_a_bigint_rather_than_panicking" \
	"a_field_wider_than_i128_records_as_a_bigint_rather_than_panicking" \
	"must not panic" \
	'old = "    if field.fits_in_i128() {"
new = "    if true {"
assert old in s, "the fits_in_i128 guard has moved"
s = s.replace(old, new)'

assert_true "the tree is restored after the mutation arms" \
	test -z "$(git -C "${REPO_ROOT}" status --porcelain)"

# ------------------------------------------------------------------------------------
echo
echo "== summary"
echo "  ${PASS} assertions passed, ${FAIL} failed"
[ "${FAIL}" -eq 0 ] || {
	echo "RESULT: FAILED"
	exit 1
}
echo "RESULT: OK"
