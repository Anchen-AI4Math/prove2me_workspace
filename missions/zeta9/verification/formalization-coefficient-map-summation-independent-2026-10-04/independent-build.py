"""Independent native replay; new Summation requires the author's frozen hashes."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
AUTHOR = TASK / "verification/formalization-coefficient-map-summation-2026-10-04"
CACHE = OUT / "native/build"
EXPECTED = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a",
    "CoefficientMapFiniteSum": "b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97",
    "CoefficientMapReflection": "8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"}
PURE = ROOT / "Definitions/Def_ZetaNine_HarmonicStability.lean"
PURE_HASH = "5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def unchanged(): return sha(PURE) == PURE_HASH and all(sha(TASK / "formalization" / (name + ".lean")) == h for name,h in EXPECTED.items())
parser = argparse.ArgumentParser()
parser.add_argument("mode", choices=["dependencies", "frozen", "boundary"])
parser.add_argument("--source-sha256")
parser.add_argument("--receipt-sha256")
parser.add_argument("--manifest-sha256")
args = parser.parse_args()
assert unchanged()
rows, frozen = [], None
if args.mode != "dependencies":
    prior = load(OUT / "independent-compile-receipt.json")
    rows, frozen = prior["rows"], prior.get("author_frozen_hashes")
    assert all(r["exit_code"] == 0 for r in rows)
if args.mode == "frozen":
    assert len(rows) == 7
    frozen = {"source_sha256": args.source_sha256, "receipt_sha256": args.receipt_sha256, "manifest_sha256": args.manifest_sha256}
    assert all(isinstance(h, str) and len(h) == 64 for h in frozen.values())
if frozen:
    assert sha(TASK / "formalization/CoefficientMapSummation.lean") == frozen["source_sha256"]
    assert sha(AUTHOR / "compile-receipt.json") == frozen["receipt_sha256"]
    assert sha(AUTHOR / "SHA256SUMS.txt") == frozen["manifest_sha256"]
    for line in (AUTHOR / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
        if line.strip():
            h, path = line.split("  ", 1)
            assert sha(TASK / path) == h

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
        "source_root_relative": source.relative_to(ROOT).as_posix(), "source_sha256": sha(source),
        "log": log.name, "log_sha256": sha(log), "exit_file": exitfile.name, "exit_file_sha256": sha(exitfile),
        "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper), "output": output.relative_to(OUT).as_posix() if output else None,
        "output_sha256": sha(output) if output and output.exists() else None})
    print(label + ": exit " + str(p.returncode), flush=True)
    assert unchanged()
    if frozen: assert sha(TASK / "formalization/CoefficientMapSummation.lean") == frozen["source_sha256"]
    if p.returncode: print(log.read_text(encoding="utf-8-sig"), flush=True)
    return p.returncode

if args.mode == "dependencies":
    if run("native-HarmonicStabilityDefinition", PURE, CACHE / "Definitions/Def_ZetaNine_HarmonicStability.olean") == 0:
        for name in EXPECTED:
            if run("native-" + name, TASK / "formalization" / (name + ".lean"), CACHE / "missions/zeta9/formalization" / (name + ".olean")): break
elif args.mode == "frozen":
    if run("native-CoefficientMapSummation", TASK / "formalization/CoefficientMapSummation.lean", CACHE / "missions/zeta9/formalization/CoefficientMapSummation.olean") == 0:
        run("author-type-replay", AUTHOR / "type-audit.lean")
else:
    assert frozen and len(rows) == 9
    run("independent-boundary-audit", OUT / "independent-boundary-audit.lean")
receipt = {"review_role": "Independent native replay; reviewer is not Summation author", "sources_sha256": EXPECTED,
    "pure_definition_source": "Definitions/Def_ZetaNine_HarmonicStability.lean", "pure_definition_sha256": PURE_HASH,
    "author_frozen_hashes": frozen, "fresh_native_cache": CACHE.relative_to(TASK).as_posix(), "rows": rows,
    "all_exit_codes_actually_observed": True, "sources_unchanged": unchanged(), "root_scope_API_credentials_writes": False}
write(OUT / "independent-compile-receipt.json", receipt)
assert all(r["exit_code"] == 0 for r in rows), "Actual failure logs retained."
