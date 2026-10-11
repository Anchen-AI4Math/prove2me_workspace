"""Compile the exact f4 frontier serially, preserving each actual response."""
from pathlib import Path
import json
import subprocess
import sys

TASK = Path(__file__).resolve().parents[1]
STEM = "OAI_PiExponent_FormalLogTruncation_formalLog_packets_surjective_iff_truncated"
NAMES = ["Thm_" + STEM + ".lean", "Sol_" + STEM + ".lean",
         "SnapshotOriginal.lean", "SnapshotGeneratedWithRefs.lean"]
for index, name in enumerate(NAMES, 1):
    command = [sys.executable, str(TASK / "scripts/preflight_staged_module.py"),
               "flp3/f4/" + name, "--root", "flp3/f4", "--imports-manifest",
               "flp3/f4/c" + str(index) + ".json", "--timeout-seconds", "300"]
    result = subprocess.run(command, cwd=TASK, capture_output=True, check=False)
    (TASK / "verification" / ("flp3-f4-" + str(index) + "-console.json")).write_bytes(result.stdout)
    (TASK / "verification" / ("flp3-f4-" + str(index) + "-stderr.txt")).write_bytes(result.stderr)
    print(json.dumps({"file": name, "exit_code": result.returncode}), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
