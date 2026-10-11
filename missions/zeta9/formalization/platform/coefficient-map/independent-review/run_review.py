"""Independent offline integration replay. All writes stay in this review directory."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
HERE = Path(__file__).resolve().parent
BATCH = HERE.parent
TASK = BATCH.parents[2]
ROOT = TASK.parents[1]
PROJECT = HERE / "project"
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
NS = "ZetaNine.CoefficientMap"

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def write(p, s):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8", newline="\n")

def rows(p):
    return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]

assert sha(TASK / "formalization/CoefficientMap.lean") == EXPECTED
PROJECT.mkdir(parents=True, exist_ok=True)
write(PROJECT / "lakefile.lean", f'''import Lake
open Lake DSL
package zeta9CoefficientMapIntegrationIndependent
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMap]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for filename in ["lake-manifest.json", "lean-toolchain"]:
    (PROJECT / filename).write_bytes((ROOT / filename).read_bytes())
(PROJECT / ".lake").mkdir(exist_ok=True)
if not (PROJECT / ".lake/packages").exists():
    p = subprocess.run(["cmd", "/c", "mklink", "/J", str(PROJECT / ".lake/packages"), str(ROOT / ".lake/packages")], capture_output=True)
    assert p.returncode == 0, (p.stdout + p.stderr).decode(errors="replace")
original_rel = "missions/zeta9/formalization/CoefficientMap.lean"
(PROJECT / original_rel).parent.mkdir(parents=True, exist_ok=True)
(PROJECT / original_rel).write_bytes((TASK / "formalization/CoefficientMap.lean").read_bytes())
plan = json.loads((BATCH / "root-copy-plan.json").read_text(encoding="utf-8-sig"))
files = plan["files"]
for f in files:
    source = TASK / f["staged_task_relative"]
    dest = PROJECT / f["root_relative_destination"]
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(source.read_bytes())
    assert sha(dest) == f["sha256"]

# Only the output paths of the already configured official oracles change.
for filename, old, new in [
    ("extract_decl_graph.lean", "missions/zeta9/formalization/platform/coefficient-map/decl_graph.jsonl", "../decl_graph.jsonl"),
    ("extract_sketch_info.lean", "missions/zeta9/formalization/platform/coefficient-map/oracle-input.lean", "../oracle-input.lean")]:
    text = (BATCH / filename).read_text(encoding="utf-8-sig")
    assert text.count(old) == 1
    write(PROJECT / filename, text.replace(old, new))
reporters = ["types_original.lean", "types_definition.lean"] + [f"types_{i}_{kind}.lean" for i in range(3) for kind in ["solution", "reference"]]
for filename in reporters:
    (PROJECT / filename).write_bytes((BATCH / filename).read_bytes())

# Audit every original helper rather than only the three selected wrappers.
graph = rows(BATCH / "decl_graph.jsonl")
for i, f in enumerate([f for f in files if f["root_relative_destination"].startswith("Solutions/")]):
    root = f["root_relative_destination"].removesuffix(".lean").replace("/", ".")
    selected = root.split("Sol_ZetaNine_CoefficientMap_")[1]
    names = [g["name"] for g in graph if g["kind"] == "theorem" and g["startLine"] > 0]
    names = [NS + ".checked_" + selected if n == NS + "." + selected else n for n in names]
    template = (BATCH / "types_original.lean").read_text(encoding="utf-8-sig")
    header = template.split('  emit "')[0].replace("import missions.zeta9.formalization.CoefficientMap", "import " + root)
    write(PROJECT / f"helpers_{i}.lean", header + "".join(f'  emit "{n}" `{n}\n' for n in names) + '  emit "solution" `solution\n')

env = os.environ.copy()
env.pop("LEAN_PATH", None)
receipt = {"source_sha256": EXPECTED, "mathlib_rev": REV, "lean_toolchain": (PROJECT / "lean-toolchain").read_text().strip(), "root_writes": False, "API_called": False, "rows": []}
def run(label, command, stdout_file=None):
    p = subprocess.run(command, cwd=PROJECT, env=env, capture_output=True)
    log = HERE / (label + ".log")
    log.write_bytes(p.stdout + p.stderr)
    write(HERE / (label + "-exit.txt"), str(p.returncode) + "\n")
    if stdout_file:
        (HERE / stdout_file).write_bytes(p.stdout)
        (HERE / (label + "-stderr.log")).write_bytes(p.stderr)
    row = {"label": label, "command": command, "working_directory": str(PROJECT), "exit_code": p.returncode, "log": log.name, "log_sha256": sha(log)}
    receipt["rows"].append(row)
    write(HERE / "compile-receipt.json", json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(label + ": exit " + str(p.returncode), flush=True)
    assert sha(TASK / "formalization/CoefficientMap.lean") == EXPECTED
    if p.returncode:
        print(log.read_text(encoding="utf-8-sig"), flush=True)
    assert p.returncode == 0

run("toolchain", ["lake", "env", "lean", "--version"])
run("build-original", ["lake", "--no-cache", "build", "missions.zeta9.formalization.CoefficientMap"])
run("stage1-extract", ["lake", "env", "lean", "extract_decl_graph.lean"])
run("stage2-extract", ["lake", "env", "lean", "--run", "extract_sketch_info.lean", original_rel, NS], "sketch_info.jsonl")
for i, f in enumerate(files):
    module = f["root_relative_destination"].removesuffix(".lean").replace("/", ".")
    run("build-staged-" + str(i), ["lake", "--no-cache", "build", module])
for filename in reporters:
    run(filename.removesuffix(".lean"), ["lake", "env", "lean", filename])
for i in range(3):
    run("helpers_" + str(i), ["lake", "env", "lean", f"helpers_{i}.lean"])
receipt["complete"] = True
receipt["all_exit_codes_observed"] = True
write(HERE / "compile-receipt.json", json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
print("Independent exact-source, seven-module, oracle and eleven-report replay complete.", flush=True)
