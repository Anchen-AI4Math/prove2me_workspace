"""Independent preparation only: four native originals and three pure Def dependencies."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
NATIVE = OUT / "cache/native/build"
PLATFORM = OUT / "cache/platform/build"
ORIGINAL = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a"}
DEFS = {
    "Def_ZetaNine_CoefficientMap": "b6d156b04e2cd14511c73ac4c2de12fedc811d6efe85af7341dad060f497edff",
    "Def_ZetaNine_CoefficientMapJet": "4941f0b3dae94c6beef98dc2c1504e9eb514a601939a74fa0f1a48fa405a91e2",
    "Def_ZetaNine_CoefficientMapInjectivity": "d7f71b43ed4f4ac8f1994ecf80dad165f4008960f6a304efcd45ebc60342b1b1"}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def unchanged():
    return all(sha(TASK / "formalization" / (name + ".lean")) == h for name,h in ORIGINAL.items()) and all(sha(ROOT / "Definitions" / (name + ".lean")) == h for name,h in DEFS.items())
assert unchanged()
rows = []
def run(label, source, cache, output):
    wrapper = OUT / (label + ".ps1")
    output.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(f'$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean -o "{output.as_posix()}" "{source.as_posix()}"\nexit $LASTEXITCODE\n', encoding="utf-8")
    invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
    p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
    log = OUT / (label + ".log")
    log.write_bytes(p.stdout + p.stderr)
    exitfile = OUT / (label + "-exit.txt")
    exitfile.write_text(str(p.returncode) + "\n", encoding="utf-8")
    rows.append({"label": label, "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode,
        "source_root_relative": source.relative_to(ROOT).as_posix(), "source_sha256": sha(source),
        "log": log.name, "log_sha256": sha(log), "exit_file": exitfile.name, "exit_file_sha256": sha(exitfile),
        "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper), "cache": cache.relative_to(OUT).as_posix(),
        "output": output.relative_to(OUT).as_posix(), "output_sha256": sha(output) if output.exists() else None})
    print(label + ": exit " + str(p.returncode), flush=True)
    assert unchanged()
    if p.returncode: print(log.read_text(encoding="utf-8-sig"), flush=True)
    return p.returncode

for name in ORIGINAL:
    if run("native-" + name, TASK / "formalization" / (name + ".lean"), NATIVE, NATIVE / "missions/zeta9/formalization" / (name + ".olean")): break
if len(rows) == 4 and all(r["exit_code"] == 0 for r in rows):
    for name in DEFS:
        if run("pure-" + name, ROOT / "Definitions" / (name + ".lean"), PLATFORM, PLATFORM / "Definitions" / (name + ".olean")): break
receipt = {"status": "DEPENDENCY_PREPARATION_ONLY_NOT_FINAL_INTEGRATION_VERDICT", "review_role": "Independent PF platform integration reviewer; not platform batch author",
    "original_sources_sha256": ORIGINAL, "existing_pure_Def_sources_sha256": DEFS, "rows": rows,
    "all_exit_codes_actually_observed": True, "sources_unchanged": unchanged(), "root_scope_API_credentials_writes": False,
    "staged_batch_compiled_or_audited": False, "author_unfrozen_records_used_as_final_evidence": False}
write(OUT / "prepare-compile-receipt.json", receipt)
assert len(rows) == 7 and all(r["exit_code"] == 0 for r in rows), "Actual failure logs retained."
