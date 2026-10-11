"""Independent fresh Reflection source and pure-definition compilation."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
NATIVE = OUT / "cache/native/build"
PLATFORM = OUT / "cache/platform/build"
ORIGINAL = {
    "CoefficientMap": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
    "CoefficientMapJet": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a",
    "CoefficientMapInjectivity": "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095",
    "CoefficientMapPartialFractions": "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a",
    "CoefficientMapReflection": "8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"}
DEFS = {
    "Def_ZetaNine_CoefficientMap": "b6d156b04e2cd14511c73ac4c2de12fedc811d6efe85af7341dad060f497edff",
    "Def_ZetaNine_CoefficientMapJet": "4941f0b3dae94c6beef98dc2c1504e9eb514a601939a74fa0f1a48fa405a91e2",
    "Def_ZetaNine_CoefficientMapInjectivity": "d7f71b43ed4f4ac8f1994ecf80dad165f4008960f6a304efcd45ebc60342b1b1",
    "Def_ZetaNine_CoefficientMapPartialFractions": "74904aff5266f68b9d9f5c3013fb636f48d0cadda75e872093419845f9b666e5"}
CONTROLS = {
    "author-audit.json": "7d48c5b7197fc9d9543b35063c256aa73bea606a59866ea81df227f731105651",
    "root-copy-plan.json": "d8a5022833267eba1884f519a2f61b80343dfae4f53820e80ae57c2c9a6e5ad6",
    "source-manifest.json": "fe3ec5bf2de4944eb186c72ad299c1b52e51fbe04f9b68f512253d4e34d9812a",
    "SHA256SUMS.txt": "d7e497dd9e6d69f538dd77390b4b516c0ec8ecdbcb93cdc1eb5a3490e93eaba3"}

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def unchanged():
    assert all(sha(TASK / "formalization" / (name + ".lean")) == h for name,h in ORIGINAL.items())
    assert all(sha(ROOT / "Definitions" / (name + ".lean")) == h for name,h in DEFS.items())
    assert all(sha(BATCH / name) == h for name,h in CONTROLS.items())
    for row in load(BATCH / "source-manifest.json")["files"]:
        p = TASK / row["task_relative"]
        assert sha(p) == row["sha256"] and p.stat().st_size == row["bytes"]
unchanged()
assert not NATIVE.exists() and not PLATFORM.exists(), "Fresh independent cache required."
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
    rows.append({"label":label, "command":invocation, "working_directory":str(ROOT), "exit_code":p.returncode,
        "source_root_relative":source.relative_to(ROOT).as_posix(), "source_sha256":sha(source),
        "log":log.name, "log_sha256":sha(log), "exit_file":exitfile.name, "exit_file_sha256":sha(exitfile),
        "wrapper":wrapper.name, "wrapper_sha256":sha(wrapper), "cache":cache.relative_to(OUT).as_posix(),
        "output":output.relative_to(OUT).as_posix(), "output_sha256":sha(output) if output.exists() else None})
    write(OUT / "prepare-compile-receipt.json", {"status":"DEPENDENCY_PREPARATION_ONLY_NOT_FINAL_VERDICT", "rows":rows,
        "original_sources_sha256":ORIGINAL,"existing_pure_Def_sources_sha256":DEFS,"author_frozen_controls":CONTROLS,
        "all_exit_codes_actually_observed":True,"native_and_staged_objects_borrowed":False,"complete":False})
    print(label + ": exit " + str(p.returncode), flush=True)
    unchanged()
    if p.returncode: print(log.read_text(encoding="utf-8-sig"), flush=True)
    assert p.returncode == 0, "Actual failed evidence is retained."

for name in ORIGINAL:
    run("native-" + name, TASK / "formalization" / (name + ".lean"), NATIVE, NATIVE / "missions/zeta9/formalization" / (name + ".olean"))
for name in DEFS:
    run("pure-" + name, ROOT / "Definitions" / (name + ".lean"), PLATFORM, PLATFORM / "Definitions" / (name + ".olean"))
write(OUT / "prepare-compile-receipt.json", {"status":"DEPENDENCY_PREPARATION_ONLY_NOT_FINAL_VERDICT", "rows":rows,
    "original_sources_sha256":ORIGINAL,"existing_pure_Def_sources_sha256":DEFS,"author_frozen_controls":CONTROLS,
    "all_exit_codes_actually_observed":True,"native_and_staged_objects_borrowed":False,"complete":True,
    "root_scope_API_credentials_writes":False})
assert len(rows) == 9 and all(row["exit_code"] == 0 for row in rows)
