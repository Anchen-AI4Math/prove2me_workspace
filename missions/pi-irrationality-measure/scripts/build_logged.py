"""Run the mission build, retaining full diagnostics and its real exit code."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"
DEST.mkdir(exist_ok=True)
stamp = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
log_path = DEST / f"build-{stamp}.log"
started = time.monotonic()
with log_path.open("w", encoding="utf-8") as log:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    print("Build log:", log_path.relative_to(ROOT), flush=True)
    process = subprocess.Popen(
        [sys.executable, "scripts/workspace.py", "build", "pi-irrationality-measure"],
        cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding="utf-8", errors="replace")
    assert process.stdout is not None
    for line in process.stdout:
        log.write(line)
        log.flush()
        if line.startswith(("✔", "✖", "⚠", "error:", "pi-irrationality-measure:")):
            print(line.rstrip(), flush=True)
    exit_code = process.wait()
record = {"exit_code": exit_code, "seconds": time.monotonic() - started,
          "log": str(log_path.relative_to(ROOT))}
(DEST / "latest-build.json").write_text(json.dumps(record, indent=2), encoding="utf-8")
print(json.dumps(record))
lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
print("\n".join(line for line in lines[-100:] if not line.startswith("trace:")))
sys.exit(exit_code)
