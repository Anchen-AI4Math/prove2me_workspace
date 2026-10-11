"""Independent actual five-source native replay, without FiniteSum imports."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
CACHE = OUT / "independent/build"
EXPECTED = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a",
    "CoefficientMapReflection": "8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def unchanged(): return all(sha(TASK / "formalization" / (name + ".lean")) == h for name,h in EXPECTED.items())
assert unchanged()
rows = []
if "--boundary" in sys.argv:
    rows = json.loads((OUT / "independent-compile-receipt.json").read_text(encoding="utf-8"))["rows"]

def run(label, source, output=None):
    wrapper = OUT / (label + ".ps1")
    command = f'$env:LEAN_PATH = "{CACHE.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean '
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
    rows.append({"label": label, "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode,
        "source": source.relative_to(TASK).as_posix(), "source_sha256": sha(source),
        "log": log.name, "log_sha256": sha(log), "exit_file": exitfile.name, "exit_file_sha256": sha(exitfile),
        "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper),
        "output": output.relative_to(OUT).as_posix() if output else None,
        "output_sha256": sha(output) if output and output.exists() else None})
    print(label + ": exit " + str(p.returncode), flush=True)
    assert unchanged()
    if p.returncode: print(log.read_text(encoding="utf-8-sig"), flush=True)
    return p.returncode

if "--boundary" not in sys.argv:
    for name in EXPECTED:
        if run("independent-native-" + name, TASK / "formalization" / (name + ".lean"), CACHE / "missions/zeta9/formalization" / (name + ".olean")): break
    if len(rows) == 5 and all(r["exit_code"] == 0 for r in rows): run("independent-author-type-replay", OUT / "type-audit.lean")
else:
    run("independent-boundary-audit", OUT / "independent-boundary-audit.lean")
receipt = {"review_role": "Independent native replay; reviewer is not Reflection author", "sources_sha256": EXPECTED,
    "fresh_native_cache": CACHE.relative_to(TASK).as_posix(), "rows": rows, "all_exit_codes_actually_observed": True,
    "sources_unchanged": unchanged(), "FiniteSum_imported": False, "root_scope_API_credentials_writes": False}
(OUT / "independent-compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
assert all(r["exit_code"] == 0 for r in rows), "Actual failure logs retained."
