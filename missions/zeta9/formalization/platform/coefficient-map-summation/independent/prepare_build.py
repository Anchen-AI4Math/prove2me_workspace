"""Independent Summation preparation; run only after parent/author frozen handoff."""
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
NATIVE = OUT / "cache/n"
PLATFORM = OUT / "cache/p"
ORIGINAL = {'CoefficientMap': 'e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03', 'CoefficientMapJet': 'e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a', 'CoefficientMapInjectivity': 'ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095', 'CoefficientMapPartialFractions': 'eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a', 'CoefficientMapReflection': '8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707', 'CoefficientMapFiniteSum': 'b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97', 'CoefficientMapSummation': 'c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d'}
DEFS = {'Def_ZetaNine_HarmonicStability': '5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92', 'Def_ZetaNine_CoefficientMap': 'b6d156b04e2cd14511c73ac4c2de12fedc811d6efe85af7341dad060f497edff', 'Def_ZetaNine_CoefficientMapJet': '4941f0b3dae94c6beef98dc2c1504e9eb514a601939a74fa0f1a48fa405a91e2', 'Def_ZetaNine_CoefficientMapInjectivity': 'd7f71b43ed4f4ac8f1994ecf80dad165f4008960f6a304efcd45ebc60342b1b1', 'Def_ZetaNine_CoefficientMapPartialFractions': '74904aff5266f68b9d9f5c3013fb636f48d0cadda75e872093419845f9b666e5', 'Def_ZetaNine_CoefficientMapReflection': '4b15dc1616c4252cffe303f34c502e4373c657f287ed3d6663755f1b0cb539d7', 'Def_ZetaNine_CoefficientMapFiniteSum': 'd1b41541e0fc7e359f96d51e4190206deb4656468896d871b95d449cddcd7fc5'}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def write(path,obj): path.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
enrollment = load(OUT / "frozen-controls.json")
assert enrollment["status"] == "PARENT_FROZEN_AUTHOR_HANDOFF"
CONTROLS = enrollment["controls"]
assert set(CONTROLS) == {"author-audit.json","root-copy-plan.json","source-manifest.json","SHA256SUMS.txt"}
def unchanged():
    assert all(sha(TASK/"formalization"/(n+".lean")) == h for n,h in ORIGINAL.items())
    assert all(sha(ROOT/"Definitions"/(n+".lean")) == h for n,h in DEFS.items())
    assert all(sha(BATCH/n) == h for n,h in CONTROLS.items())
    for row in load(BATCH/"source-manifest.json")["files"]:
        p = TASK/row["task_relative"]
        assert sha(p) == row["sha256"] and p.stat().st_size == row["bytes"]
unchanged()
assert not NATIVE.exists() and not PLATFORM.exists(), "New independent caches required."
rows = []
def run(label,source,cache,output):
    wrapper = OUT/(label+".ps1")
    output.parent.mkdir(parents=True,exist_ok=True)
    wrapper.write_text(f'$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean -o "{output.as_posix()}" "{source.as_posix()}"\nexit $LASTEXITCODE\n',encoding="utf-8")
    invocation = ["lake","env","pwsh","-NoProfile","-ExecutionPolicy","Bypass","-File",str(wrapper)]
    p = subprocess.run(invocation,cwd=ROOT,capture_output=True)
    log = OUT/(label+".log"); log.write_bytes(p.stdout+p.stderr)
    exitfile = OUT/(label+"-exit.txt");exitfile.write_text(str(p.returncode)+"\n",encoding="utf-8")
    rows.append({"label":label,"command":invocation,"working_directory":str(ROOT),"exit_code":p.returncode,
        "source_root_relative":source.relative_to(ROOT).as_posix(),"source_sha256":sha(source),"log":log.name,"log_sha256":sha(log),
        "exit_file":exitfile.name,"exit_file_sha256":sha(exitfile),"wrapper":wrapper.name,"wrapper_sha256":sha(wrapper),
        "cache":cache.relative_to(OUT).as_posix(),"output":output.relative_to(OUT).as_posix(),"output_sha256":sha(output) if output.exists() else None})
    write(OUT/"prepare-compile-receipt.json",{"status":"PREPARATION_ONLY_NOT_FINAL_VERDICT","rows":rows,"complete":False,
        "original_sources_sha256":ORIGINAL,"existing_pure_Def_sources_sha256":DEFS,"author_frozen_controls":CONTROLS,
        "all_exit_codes_actually_observed":True,"native_and_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False})
    print(label+": exit "+str(p.returncode),flush=True)
    unchanged()
    if p.returncode:print(log.read_text(encoding="utf-8-sig"),flush=True)
    assert p.returncode == 0,"Actual failure logs are retained."

run("native-HarmonicStabilityDefinition",ROOT/"Definitions/Def_ZetaNine_HarmonicStability.lean",NATIVE,NATIVE/"Definitions/Def_ZetaNine_HarmonicStability.olean")
for name in ORIGINAL:
    run("native-"+name,TASK/"formalization"/(name+".lean"),NATIVE,NATIVE/"missions/zeta9/formalization"/(name+".olean"))
for name in DEFS:
    run("pure-"+name,ROOT/"Definitions"/(name+".lean"),PLATFORM,PLATFORM/"Definitions"/(name+".olean"))
write(OUT/"prepare-compile-receipt.json",{"status":"PREPARATION_ONLY_NOT_FINAL_VERDICT","rows":rows,"complete":True,
    "original_sources_sha256":ORIGINAL,"existing_pure_Def_sources_sha256":DEFS,"author_frozen_controls":CONTROLS,
    "all_exit_codes_actually_observed":True,"native_and_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False})
assert len(rows) == 15 and all(row["exit_code"] == 0 for row in rows)
