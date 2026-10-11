"""Compile only new task-local modules and actual import/type/value reporters."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PLAN = json.loads((OUT / "target-plan.json").read_text(encoding="utf-8"))
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
SOURCE = TASK / "formalization/CoefficientMap.lean"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(SOURCE) == EXPECTED
staged_cache = OUT / "build/staged"
original_cache = OUT / "build/original"

def run(label, source, output=None, original=False):
    cache = original_cache if original else staged_cache
    wrapper = OUT / (label + ".ps1")
    command = f'$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean '
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        command += '-o "' + output.as_posix() + '" '
    command += '"' + source.as_posix() + '"\nexit $LASTEXITCODE\n'
    wrapper.write_text(command, encoding="utf-8")
    invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
    p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
    log = OUT / (label + ".log")
    log.write_bytes(p.stdout + p.stderr)
    exitfile = OUT / (label + "-exit.txt")
    exitfile.write_text(str(p.returncode) + "\n", encoding="utf-8")
    assert sha(SOURCE) == EXPECTED
    row = {"label": label, "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode,
           "source": source.relative_to(TASK).as_posix(), "source_sha256": sha(source),
           "log": log.relative_to(OUT).as_posix(), "log_sha256": sha(log),
           "exit_file": exitfile.name, "exit_file_sha256": sha(exitfile),
           "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper),
           "olean_prefix": cache.relative_to(OUT).as_posix(),
           "output": output.relative_to(OUT).as_posix() if output else None,
           "output_sha256": sha(output) if output and output.exists() else None}
    print(label + ": exit " + str(p.returncode), flush=True)
    if p.returncode != 0:
        print(log.read_text(encoding="utf-8-sig"), flush=True)
    return row

rows = []
definition = PLAN["local_definition"]
rows.append(run("build-definition", OUT / "staged" / definition, staged_cache / Path(definition).with_suffix(".olean")))
assert rows[-1]["exit_code"] == 0
jobs = []
for i, target in enumerate(PLAN["targets"]):
    for kind in ["solution", "reference"]:
        path = target["local_" + kind]
        jobs.append((f"build-{i}-{kind}", OUT / "staged" / path, staged_cache / Path(path).with_suffix(".olean")))
with ThreadPoolExecutor(max_workers=2) as pool:
    rows.extend(pool.map(lambda args: run(*args), jobs))
if all(row["exit_code"] == 0 for row in rows):
    reports = [("types-original", OUT / "types_original.lean", None, True),
               ("types-definition", OUT / "types_definition.lean", None, False)]
    reports += [(f"types-{i}-{kind}", OUT / f"types_{i}_{kind}.lean", None, False)
                for i in range(3) for kind in ["solution", "reference"]]
    with ThreadPoolExecutor(max_workers=2) as pool:
        rows.extend(pool.map(lambda args: run(*args), reports))
receipt = {"source_sha256": EXPECTED, "source_unchanged": sha(SOURCE) == EXPECTED,
           "complete": len(rows) == 15 and all(row["exit_code"] == 0 for row in rows),
           "all_exit_codes_actually_observed": True,
           "shared_root_writes": False, "API_called": False, "rows": rows}
(OUT / "staged-compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
assert receipt["complete"], "See actual retained failure logs and receipt."
print("Complete: 7 task-local builds and 8 actual import/type/value reports.", flush=True)
