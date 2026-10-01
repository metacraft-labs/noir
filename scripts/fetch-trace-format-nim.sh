#!/usr/bin/env bash
# Provision the Nim sources `codetracer_trace_writer_nim` compiles, at pinned
# revisions, into `.codetracer-deps/` at the root of this repository.
#
# WHY THIS EXISTS. `nargo_cli` links `codetracer_trace_writer_nim` (through
# `noir_tracer/nim-writer`). That crate's `build.rs` compiles a Nim static
# library from the `codetracer-trace-format-nim` repository, which it looks for
# as a sibling of its own checkout unless `CODETRACER_TRACE_FORMAT_NIM_DIR`
# names one. The crate reaches this workspace as a cargo GIT dependency, and a
# cargo git checkout has no siblings, so without this script a plain
# `cargo build` stops in that build script with "Nim FFI entry point not found".
#
# WHAT IT PROVIDES. Three checkouts and one Nim config file:
#
#   .codetracer-deps/codetracer-trace-format-nim   the FFI sources
#   .codetracer-deps/nim-stew                      its `requires "stew"`
#   .codetracer-deps/nim-results                   its `requires "results"`
#   .codetracer-deps/nim.cfg                       puts the last two on Nim's
#                                                  search path
#
# `.cargo/config.toml` points `CODETRACER_TRACE_FORMAT_NIM_DIR` at the first
# and sets `CODETRACER_TRACE_FORMAT_NIM_SKIP_NIMBLE_INSTALL`, so the build
# script neither needs `nimble` nor touches the network. Nim reads `nim.cfg`
# from every parent directory of the module it compiles, which is how the two
# dependency checkouts reach the compile without a nimble package store.
#
# The Nim compiler itself (`nim` on PATH) is NOT provided here.
#
# REPRODUCIBILITY. Every checkout is fetched by full commit hash and verified
# after checkout; a directory already at the pinned revision is left alone, and
# one at any other revision is moved to the pin. The stew and results revisions
# are the ones `codetracer-trace-format-nim`'s own `flake.lock` locks at
# `TRACE_FORMAT_NIM_REV`, and the script refuses to continue if they disagree.
#
# BUMPING. `TRACE_FORMAT_NIM_REV` is the Nim half of the trace-format revision
# `Cargo.toml` pins for `codetracer_trace_types` / `codetracer_trace_writer`;
# the two move together. After changing it, copy the `nim-stew` and
# `nim-results` revisions out of that revision's `flake.lock`.
#
# Any of the three can be overridden for one run through the environment
# (e.g. `TRACE_FORMAT_NIM_REV=<sha> just trace-format-nim`); to build against
# a local checkout instead, set `CODETRACER_TRACE_FORMAT_NIM_DIR` yourself,
# which takes precedence over `.cargo/config.toml`.

set -euo pipefail

TRACE_FORMAT_NIM_REPO="${TRACE_FORMAT_NIM_REPO:-https://github.com/metacraft-labs/codetracer-trace-format-nim}"
TRACE_FORMAT_NIM_REV="${TRACE_FORMAT_NIM_REV:-63b67093d877f852030ea0d102ecda6cb60064d6}"

NIM_STEW_REPO="${NIM_STEW_REPO:-https://github.com/status-im/nim-stew}"
NIM_STEW_REV="${NIM_STEW_REV:-1a5d0b99209f50ff055d9b5216849ba0365f8cf5}"

NIM_RESULTS_REPO="${NIM_RESULTS_REPO:-https://github.com/arnetheduck/nim-results}"
NIM_RESULTS_REV="${NIM_RESULTS_REV:-b319652e98a198fa881ca70a76754c2dd6f09804}"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
deps_dir="${repo_root}/.codetracer-deps"

# fetch_at <url> <rev> <dir>: make <dir> a checkout of <url> at exactly <rev>.
fetch_at() {
	local url="$1" rev="$2" dir="$3"
	if [[ -d "${dir}/.git" ]] && [[ "$(git -C "${dir}" rev-parse HEAD 2>/dev/null)" == "${rev}" ]]; then
		echo "  ${dir##*/} already at ${rev:0:12}"
		return 0
	fi
	echo "  ${dir##*/} <- ${url} @ ${rev:0:12}"
	if [[ ! -d "${dir}/.git" ]]; then
		rm -rf "${dir}"
		git init --quiet "${dir}"
		git -C "${dir}" remote add origin "${url}"
	else
		git -C "${dir}" remote set-url origin "${url}"
	fi
	git -C "${dir}" fetch --quiet --depth 1 origin "${rev}"
	git -C "${dir}" -c advice.detachedHead=false checkout --quiet --force FETCH_HEAD
	local got
	got="$(git -C "${dir}" rev-parse HEAD)"
	if [[ "${got}" != "${rev}" ]]; then
		echo "fetch-trace-format-nim: ${dir} is at ${got}, expected ${rev}" >&2
		exit 1
	fi
}

mkdir -p "${deps_dir}"
echo "Provisioning codetracer-trace-format-nim into ${deps_dir}"
fetch_at "${TRACE_FORMAT_NIM_REPO}" "${TRACE_FORMAT_NIM_REV}" "${deps_dir}/codetracer-trace-format-nim"
fetch_at "${NIM_STEW_REPO}" "${NIM_STEW_REV}" "${deps_dir}/nim-stew"
fetch_at "${NIM_RESULTS_REPO}" "${NIM_RESULTS_REV}" "${deps_dir}/nim-results"

# The stew/results pins must be the ones the Nim repository itself locks.
flake_lock="${deps_dir}/codetracer-trace-format-nim/flake.lock"
if [[ -f "${flake_lock}" ]] && command -v python3 >/dev/null 2>&1; then
	python3 - "${flake_lock}" "${NIM_STEW_REV}" "${NIM_RESULTS_REV}" <<-'EOF'
		import json, sys
		nodes = json.load(open(sys.argv[1]))["nodes"]
		want = {"nim-stew": sys.argv[2], "nim-results": sys.argv[3]}
		bad = [
		    f"{name}: pinned {rev[:12]}, flake.lock locks {nodes[name]['locked']['rev'][:12]}"
		    for name, rev in want.items()
		    if name in nodes and nodes[name]["locked"]["rev"] != rev
		]
		if bad:
		    sys.exit("fetch-trace-format-nim: dependency pins disagree with "
		             "codetracer-trace-format-nim's flake.lock:\n  " + "\n  ".join(bad))
	EOF
fi

# `$config` is the directory holding this file, so the paths stay correct
# wherever the repository is checked out.
cat >"${deps_dir}/nim.cfg" <<'EOF'
# Generated by scripts/fetch-trace-format-nim.sh. Supplies the `requires` of
# codetracer-trace-format-nim without a nimble package store.
--path:"$config/nim-stew"
--path:"$config/nim-results"
EOF

echo "Done. CODETRACER_TRACE_FORMAT_NIM_DIR=${deps_dir}/codetracer-trace-format-nim"
