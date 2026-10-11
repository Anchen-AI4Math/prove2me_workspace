"""Native types for every true source proof required by the actual Stage1 closure."""
from pathlib import Path
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
CACHE = OUT / "cache/native/build"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
graph = [json.loads(s) for s in (OUT / "native-decl-graph.jsonl").read_text(encoding="utf-8").splitlines() if s.startswith("{")]
byname = {r["name"]: r for r in graph}
core = [r for r in graph if r["module"].endswith(".CoefficientMapPartialFractions") and r["startLine"] > 0]
reached, work = set(), [r["name"] for r in core] + [r["name"] for r in graph if r["isInstance"]]
while work:
    name = work.pop()
    if name in reached: continue
    reached.add(name)
    work.extend(byname[name]["typeDeps"] + byname[name]["valueDeps"])
proofs = sorted(r["name"] for r in graph if r["name"] in reached and r["kind"] == "theorem" and r["startLine"] > 0)
assert len(proofs) == 42
template = (BATCH / "types_original.lean").read_text(encoding="utf-8-sig").split('  emit "')[0]
source = OUT / "types_native_helpers.lean"
source.write_text(template + ''.join('  emit "' + name + '" `' + name + '\n' for name in proofs), encoding="utf-8")
wrapper = OUT / "types_native_helpers.ps1"
wrapper.write_text(f'$env:LEAN_PATH = "{CACHE.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean "{source.as_posix()}"\nexit $LASTEXITCODE\n', encoding="utf-8")
command = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
p = subprocess.run(command, cwd=ROOT, capture_output=True)
log, exitfile = OUT / "types_native_helpers.log", OUT / "types_native_helpers-exit.txt"
log.write_bytes(p.stdout + p.stderr)
exitfile.write_text(str(p.returncode) + "\n", encoding="utf-8")
write(OUT / "native-helper-compile-receipt.json", {"label": "native42_actual_required_proof_types", "command": command,
    "working_directory": str(ROOT), "exit_code": p.returncode, "source_root_relative": source.relative_to(ROOT).as_posix(),
    "source_sha256": sha(source), "log": log.name, "log_sha256": sha(log), "exit_file": exitfile.name,
    "exit_file_sha256": sha(exitfile), "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper),
    "actual_graph_proof_names": proofs, "all_exit_codes_actually_observed": True, "root_writes": False})
assert p.returncode == 0, log.read_text(encoding="utf-8-sig")
print("Native42 helper type audit exit0")
