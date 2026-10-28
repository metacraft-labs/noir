"""Record the real capability-tour limits package repeatedly, without editing CT bytes.

Usage: fixture-recording-rich.py NARGO CT_PRINT LIMITS_SOURCE_DIR
The source package belongs to BlockTracer; this integration test consumes it as-is.
"""

import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

nargo, reader, source = sys.argv[1:]
baseline = None
with tempfile.TemporaryDirectory() as scratch:
    scratch = pathlib.Path(scratch)
    for run in range(12):
        package = scratch / str(run)
        shutil.copytree(source, package, ignore=shutil.ignore_patterns("target", "*.ct"))
        subprocess.run(
            [nargo, "trace", "--out-dir", "out", "--recording-id",
             "01949fcc-7d92-7e9c-8000-000000000061", "--recording-workdir",
             "/blocktracer/fixtures/trace/tour/limits"],
            cwd=package, check=True, capture_output=True,
        )
        container = package / "out/tour_limits.ct"
        raw = container.read_bytes()
        decoded = json.loads(subprocess.check_output([reader, "--full", str(container)]))
        steps = [event for event in decoded["events"]
                 if event.get("kind") == "step" and event.get("path") == "src/main.nr"
                 and event.get("line") == 109]
        assert steps, "the real limits program did not reach its shadowed bounds use"
        for step in steps:
            highs = [variable["value"]["field_values"][1]["i"]
                     for variable in step["vars"] if variable["varname"] == "bounds"]
            assert highs == [8, 508], f"run {run}: shadowed bounds order {highs}; visible high must be 508"
        digest = hashlib.sha256(raw).hexdigest()
        print(f"run {run}: {digest}, outer high 8 then active inner high 508", flush=True)
        if baseline is None:
            baseline = raw
        else:
            assert raw == baseline, f"run {run}: fixed-identity limits recording changed bytes"

print("rich limits: 12 byte-identical recordings preserve the active shadowed binding")
