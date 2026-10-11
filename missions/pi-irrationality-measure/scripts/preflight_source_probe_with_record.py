"""Run the frozen legacy source-probe runner and preserve its actual JSON result.

The legacy runner only writes latest-preflight.json. This separate wrapper keeps
each successful/failed attempt and an exact per-file sidecar without changing
the producer that the 875-module extraction already pins.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if len(sys.argv) != 2:
        raise ValueError("Expected one .lean path relative to verification")
    source = (VERIFICATION / sys.argv[1]).resolve()
    if not source.is_relative_to(VERIFICATION.resolve()) or not source.is_file() or source.suffix != ".lean":
        raise ValueError("Expected an existing mission-local verification Lean file")
    runner = TASK / "scripts/preflight_logged.py"
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
    attempts = VERIFICATION / "source-probe-attempts"
    attempts.mkdir(exist_ok=True)
    prefix = attempts / (source.stem + "_" + stamp)
    input_sha, runner_sha = sha(source), sha(runner)
    runtime = VERIFICATION / "lean-runtime.json"
    runtime_sha = sha(runtime)
    command = [sys.executable, str(runner), "--verification",
               source.relative_to(VERIFICATION).as_posix(), "--timeout-seconds", "300"]
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, check=False)
    prefix.with_suffix(".stdout").write_bytes(completed.stdout)
    prefix.with_suffix(".stderr").write_bytes(completed.stderr)
    results = []
    for line in completed.stdout.decode("utf-8", "replace").splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and "source" in value and "exit_code" in value:
            results.append(value)
    if len(results) != 1:
        raise ValueError("Actual runner stdout did not contain exactly one result; attempt output preserved")
    result = results[0]
    if (result["source"] != source.relative_to(ROOT).as_posix()
            or result.get("source_sha256") != input_sha or sha(source) != input_sha
            or sha(runner) != runner_sha or sha(runtime) != runtime_sha
            or result.get("runtime_sha256") != runtime_sha):
        raise ValueError("Actual runner result does not bind the stable source/runner/runtime")
    raw = (json.dumps(result, indent=2) + "\n").encode("utf-8")
    prefix.with_suffix(".result.json").write_bytes(raw)
    source.with_suffix(source.suffix + ".preflight.json").write_bytes(raw)
    log = ROOT / result["log"]
    witness = dict(wrapper_sha256=sha(Path(__file__)), runner_sha256=runner_sha,
                   command=command, cwd=str(ROOT), actual_result_sha256=hashlib.sha256(raw).hexdigest(),
                   stdout_sha256=sha(prefix.with_suffix(".stdout")),
                   stderr_sha256=sha(prefix.with_suffix(".stderr")), compiler_log_sha256=sha(log))
    prefix.with_suffix(".witness.json").write_text(json.dumps(witness, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))
    return completed.returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as exc:
        raise SystemExit("source-probe wrapper refused: " + str(exc))
