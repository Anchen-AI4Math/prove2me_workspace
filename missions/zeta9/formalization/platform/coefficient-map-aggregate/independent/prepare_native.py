"""Independent pre-freeze Aggregate preparation, not an integration verdict."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent
BATCH=OUT.parent
TASK=OUT.parents[3]
ROOT=TASK.parents[1]
PROJECT=OUT/"project"
NATIVE,PLATFORM=OUT/"cache/n",OUT/"cache/p"
SUM=TASK/"formalization/platform/coefficient-map-summation/independent"
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def write(p,d):p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
assert sha(SUM/"independent-integration-review.json")=="83d08d7146f472a2674f48158dd1154803ace82e2890506797d735b12041822e"
ORIGINAL={**load(SUM/"prepare-compile-receipt.json")["original_sources_sha256"],
    "CoefficientMapAggregate":"e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299"}
DEFS={**load(SUM/"prepare-compile-receipt.json")["existing_pure_Def_sources_sha256"],
    "Def_ZetaNine_CoefficientMapSummation":"469d4c0ba2f3849ad48c764f5e3a56c09f19a726c4ad9b9ba080ec69a853962c"}
MATH=TASK/"verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-review.json"
MATH_SHA="d2f50aa65f5dec147e632642c78cd27aaa7d8b7ba554067b389d5cc669002ddc"
STAGED_DEF=BATCH/"staged/Definitions/Def_ZetaNine_CoefficientMapAggregate.lean"
STAGED_DEF_SHA="ef491f5136c5a98d976ff9faf73df3b65393bb2caf50772dccafd213c8302079"
def unchanged():
    assert sha(MATH)==MATH_SHA
    assert sha(STAGED_DEF)==STAGED_DEF_SHA and STAGED_DEF.stat().st_size==4920
    for name,h in ORIGINAL.items():
        assert sha(TASK/"formalization"/(name+".lean"))==h
        if (PROJECT/"missions/zeta9/formalization"/(name+".lean")).exists():
            assert sha(PROJECT/"missions/zeta9/formalization"/(name+".lean"))==h
    for name,h in DEFS.items():
        assert sha(ROOT/"Definitions"/(name+".lean"))==h
        if (PROJECT/"Definitions"/(name+".lean")).exists():
            assert sha(PROJECT/"Definitions"/(name+".lean"))==h
unchanged()
assert len(ORIGINAL)==len(DEFS)==8
assert not NATIVE.exists() and not PLATFORM.exists(),"Fresh independent caches required"
for name,h in ORIGINAL.items():
    p=PROJECT/"missions/zeta9/formalization"/(name+".lean");p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes((TASK/"formalization"/(name+".lean")).read_bytes());assert sha(p)==h
for name,h in DEFS.items():
    p=PROJECT/"Definitions"/(name+".lean");p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes((ROOT/"Definitions"/(name+".lean")).read_bytes());assert sha(p)==h
write(OUT/"preparation-enrollment.json",{"status":"PREFREEZE_SOURCE_PREPARATION_ONLY","actual_sources_sha256":ORIGINAL,
    "existing_pure_Definitions_sha256":DEFS,"new_staged_Def_sha256":STAGED_DEF_SHA,"native_math_review_sha256":MATH_SHA,
    "author_controls_not_yet_frozen":True,"root_aggregate_not_yet_installed":True,"independent_PASS_not_claimed":True})
rows=[]
def run(label,source,cache,output):
    wrapper=OUT/(label+".ps1");output.parent.mkdir(parents=True,exist_ok=True)
    wrapper.write_text(f'$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{PROJECT.as_posix()}"\nSet-Location -LiteralPath "{PROJECT.as_posix()}"\n& lean -o "{output.as_posix()}" "{source.as_posix()}"\nexit $LASTEXITCODE\n',encoding="utf-8")
    cmd=["lake","env","pwsh","-NoProfile","-ExecutionPolicy","Bypass","-File",str(wrapper)]
    p=subprocess.run(cmd,cwd=ROOT,capture_output=True)
    log=OUT/(label+".log");log.write_bytes(p.stdout+p.stderr)
    ex=OUT/(label+"-exit.txt");ex.write_text(str(p.returncode)+"\n",encoding="utf-8")
    rows.append({"label":label,"command":cmd,"lake_env_working_directory":str(ROOT),"lean_working_directory":str(PROJECT),
        "exit_code":p.returncode,"source_root_relative":source.relative_to(ROOT).as_posix(),"source_sha256":sha(source),
        "log":log.name,"log_sha256":sha(log),"exit_file":ex.name,"exit_file_sha256":sha(ex),
        "wrapper":wrapper.name,"wrapper_sha256":sha(wrapper),"cache":cache.relative_to(OUT).as_posix(),
        "output":output.relative_to(OUT).as_posix(),"output_sha256":sha(output) if output.exists() else None})
    write(OUT/"prepare-compile-receipt.json",{"status":"PREFREEZE_PREPARATION_NOT_FINAL_VERDICT","rows":rows,"complete":False,
        "original_sources_sha256":ORIGINAL,"existing_pure_Def_sources_sha256":DEFS,"new_Def_sha256":STAGED_DEF_SHA,
        "source_copies_byte_identical":True,"native_and_staged_objects_borrowed":False,"Mathlib_root_environment_only_reused":True,
        "root_scope_API_credentials_writes":False})
    print(label+": exit "+str(p.returncode),flush=True);unchanged()
    if p.returncode: print(log.read_text(encoding="utf-8-sig"),flush=True)
    assert p.returncode==0,"Actual failure source, logs and receipt retained."
run("native-HarmonicStabilityDefinition",PROJECT/"Definitions/Def_ZetaNine_HarmonicStability.lean",NATIVE,NATIVE/"Definitions/Def_ZetaNine_HarmonicStability.olean")
for name in ORIGINAL:
    run("native-"+name,PROJECT/"missions/zeta9/formalization"/(name+".lean"),NATIVE,NATIVE/"missions/zeta9/formalization"/(name+".olean"))
for name in DEFS:
    run("pure-"+name,PROJECT/"Definitions"/(name+".lean"),PLATFORM,PLATFORM/"Definitions"/(name+".olean"))
write(OUT/"prepare-compile-receipt.json",{"status":"PREFREEZE_PREPARATION_NOT_FINAL_VERDICT","rows":rows,"complete":True,
    "original_sources_sha256":ORIGINAL,"existing_pure_Def_sources_sha256":DEFS,"new_Def_sha256":STAGED_DEF_SHA,
    "source_copies_byte_identical":True,"native_and_staged_objects_borrowed":False,"Mathlib_root_environment_only_reused":True,
    "root_scope_API_credentials_writes":False})
assert len(rows)==17 and all(r["exit_code"]==0 for r in rows)
