"""Same-version Linux preflight, reusing existing portable Lean artifacts."""
import json
from pathlib import Path
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
PORT = TASK / "port/lean/OAI/NumberTheory/PiExponent"
source = (PORT / sys.argv[1]).resolve()
if not source.is_relative_to(PORT.resolve()) or not source.is_file():
    raise SystemExit("Expected a source file inside this mission's port")
linux_root = "/mnt/d/users/self_projects/prove2me_workspace"
runtime = linux_root + "/missions/pi-irrationality-measure/runtime/lean-4.33.1-linux"
search = [p / ".lake/build/lib/lean" for p in (ROOT / ".lake/packages").iterdir()
          if p.is_dir() and (p / ".lake/build/lib/lean").is_dir()]
search.append(ROOT / ".lake/build/lib/lean")
lean_path = ":".join(linux_root + "/" + p.relative_to(ROOT).as_posix() for p in search)
stamp = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
log = TASK / "verification" / f"preflight-linux-{source.stem}-{stamp}.log"
print("Linux preflight log:", log.relative_to(ROOT), flush=True)
started = time.monotonic()
with log.open("w", encoding="utf-8") as out:
    process = subprocess.Popen(
        ["wsl.exe", "-d", "Ubuntu", "--cd", linux_root, "--", "env",
         "LEAN_PATH=" + lean_path, "LEAN_NUM_THREADS=1", runtime + "/bin/lean",
         "-DautoImplicit=false", source.relative_to(ROOT).as_posix()],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", errors="replace")
    assert process.stdout is not None
    for line in process.stdout:
        out.write(line)
        out.flush()
        print(line.rstrip(), flush=True)
    code = process.wait()
record = {"source": source.relative_to(ROOT).as_posix(), "exit_code": code,
          "seconds": time.monotonic() - started, "runtime": "Linux Lean 4.33.1",
          "log": log.relative_to(ROOT).as_posix()}
(TASK / "verification/latest-preflight-linux.json").write_text(
    json.dumps(record, indent=2), encoding="utf-8")
print(json.dumps(record), flush=True)
sys.exit(code)
