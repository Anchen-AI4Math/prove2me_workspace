"""Resume only unfinished steps after verifying completed source/log artifacts.

Does not rerun the 23 upstream source modules or change mathematical sources.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from datetime import datetime, timezone

OUT = Path(__file__).resolve().parent
PROJECT = OUT / "project"

def sha(data):
    return hashlib.sha256(data).hexdigest()

manifest = json.loads((OUT / "prepared-source-manifest.json").read_text(encoding="utf-8-sig"))
for row in manifest["sources"]:
    assert sha((PROJECT / row["path"]).read_bytes()) == row["sha256"], row["path"]
prior_data = (OUT / "sequential-build.log").read_bytes()
prior = prior_data.decode("utf-8-sig")
completed = []
for part in prior.split("COMMAND: ")[1:]:
    command = part.splitlines()[0].strip().split()
    assert command[:3] == ["lake", "--no-cache", "build"]
    assert "Build completed successfully" in part and "error:" not in part, command
    completed.append({"module": command[3], "command": command, "exit_code": 0,
                      "evidence": "earlier sequential-build.log successful completion diagnostic"})
assert len(completed) == 31, len(completed)

closure = json.loads((PROJECT / "audit/upstream-pnt/kernel-source-manifest.json").read_text(encoding="utf-8-sig"))
assert len(closure["sources"]) == 23
assert {row["module"] for row in closure["sources"]} == {row["module"] for row in completed[:23]}
artifacts = []
for row in closure["sources"]:
    source = PROJECT / row["path"]
    assert sha(source.read_bytes()) == row["sha256"]
    base = PROJECT / ".lake/build/lib/lean" / Path(row["path"]).with_suffix("")
    for suffix in [".olean", ".ilean", ".trace"]:
        artifact = Path(str(base) + suffix)
        data = artifact.read_bytes()
        artifacts.append({"module": row["module"], "path": artifact.relative_to(PROJECT).as_posix(),
                          "bytes": len(data), "sha256": sha(data)})

remaining = [
    "missions.zeta9.formalization.HarmonicAsymptotic",
    "missions.zeta9.formalization.PNTTransfer",
    "missions.zeta9.formalization.ShortZeroCoefficient",
    "Audit.Kernel", "Audit.C3Signed", "Audit.C3Nonzero", "Audit.NativeC3", "Audit.PNT",
]
environment = os.environ.copy()
environment.pop("LEAN_PATH", None)
steps = []
with (OUT / "resumed-build.log").open("wb") as stream:
    for module in remaining:
        command = ["lake", "--no-cache", "build", module]
        result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
        stream.write(("\nCOMMAND: " + " ".join(command) + "\n").encode())
        stream.write(result.stdout + result.stderr)
        stream.flush()
        steps.append({"module": module, "command": command, "exit_code": result.returncode})
        print(json.dumps(steps[-1]), flush=True)
        (OUT / "resumed-build-steps.json").write_text(json.dumps(steps, indent=2) + "\n", encoding="utf-8")
        if result.returncode:
            break
    if len(steps) == len(remaining) and all(step["exit_code"] == 0 for step in steps):
        command = ["lake", "--no-cache", "build", "Audit", "Theorems"]
        result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
        stream.write(("\nCOMMAND: " + " ".join(command) + "\n").encode())
        stream.write(result.stdout + result.stderr)
        stream.flush()
        steps.append({"module": "final Audit Theorems", "command": command, "exit_code": result.returncode})
        print(json.dumps(steps[-1]), flush=True)

success = len(steps) == len(remaining) + 1 and all(step["exit_code"] == 0 for step in steps)
exit_code = 0 if success else 1
(OUT / "resumed-build-exit.txt").write_text(str(exit_code) + "\n", encoding="utf-8")
receipt = {
    "status": "PASS" if success else "FAIL", "checked_at": datetime.now(timezone.utc).isoformat(),
    "completed_earlier_steps": completed, "new_steps": steps, "aggregate_exit_code": exit_code,
    "earlier_sequential_log_sha256": sha(prior_data),
    "new_log_sha256": sha((OUT / "resumed-build.log").read_bytes()),
    "upstream_modules_successfully_built_in_this_project": 23,
    "upstream_modules_rebuilt_during_resume": 0,
    "external_PNT_binary_cache_borrowed": False,
    "existing_same_project_artifacts_checked": artifacts,
    "earlier_initial_parallel_attempt_exit": 1,
    "earlier_sequential_run_final_receipt_missing_because_interrupted": True,
    "mathematical_source_changes": [], "network_API_credential_operations": False,
    "platform_acceptance_claimed": False,
}
(OUT / "resumed-build-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
(OUT / "combined-build.log").write_bytes(prior_data + (OUT / "resumed-build.log").read_bytes())
raise SystemExit(exit_code)
