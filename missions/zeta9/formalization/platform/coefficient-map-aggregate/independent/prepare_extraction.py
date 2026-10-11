"""Pre-freeze actual Aggregate graph/oracles from immutable prior official code."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[3];ROOT=TASK.parents[1]
PROJECT=OUT/"project";NATIVE=OUT/"cache/n"
RECIPE=TASK/"formalization/platform/coefficient-map-summation"
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def write(p,d):p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
prep=load(OUT/"prepare-compile-receipt.json")
assert prep["complete"] and len(prep["rows"])==17 and all(r["exit_code"]==0 for r in prep["rows"])
assert sha(RECIPE/"author-audit.json")=="eed4d2dc0cd429401cf7b7bbffd34cb556cc2159f773c57dcdb8fe9cbee37a79"
def fixed():
    for n,h in prep["original_sources_sha256"].items():assert sha(PROJECT/"missions/zeta9/formalization"/(n+".lean"))==h
    for n,h in prep["existing_pure_Def_sources_sha256"].items():assert sha(PROJECT/"Definitions"/(n+".lean"))==h
fixed();rows=[]
def run(label,source,args=None,stdout_copy=None):
    wrapper=OUT/(label+".ps1")
    cmd=f'$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "{NATIVE.as_posix()};" + $env:LEAN_PATH + ";{PROJECT.as_posix()}"\nSet-Location -LiteralPath "{PROJECT.as_posix()}"\n& lean '
    if args:cmd+='--run '
    cmd+='"'+source.as_posix()+'"'+''.join(' "'+a+'"' for a in args or [])+'\nexit $LASTEXITCODE\n'
    wrapper.write_text(cmd,encoding="utf-8")
    invocation=["lake","env","pwsh","-NoProfile","-ExecutionPolicy","Bypass","-File",str(wrapper)]
    p=subprocess.run(invocation,cwd=ROOT,capture_output=True)
    log=OUT/(label+".log");log.write_bytes(p.stdout+p.stderr)
    ex=OUT/(label+"-exit.txt");ex.write_text(str(p.returncode)+"\n",encoding="utf-8")
    if stdout_copy:stdout_copy.write_bytes(p.stdout)
    rows.append({"label":label,"command":invocation,"lake_env_working_directory":str(ROOT),"lean_working_directory":str(PROJECT),
        "exit_code":p.returncode,"source_root_relative":source.relative_to(ROOT).as_posix(),"source_sha256":sha(source),
        "log":log.name,"log_sha256":sha(log),"exit_file":ex.name,"exit_file_sha256":sha(ex),
        "wrapper":wrapper.name,"wrapper_sha256":sha(wrapper),"cache":"cache/n","output":None,"output_sha256":None,
        "stdout_copy":stdout_copy.name if stdout_copy else None,"stdout_sha256":sha(stdout_copy) if stdout_copy else None})
    write(OUT/"actual-extraction-receipt.json",{"status":"PREFREEZE_EXTRACTION_NOT_FINAL_VERDICT","rows":rows,"complete":False,
        "source_copies_byte_identical":True,"native_and_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False})
    print(label+": exit "+str(p.returncode),flush=True);fixed()
    if p.returncode:print(log.read_text(encoding="utf-8-sig"),flush=True)
    assert p.returncode==0,"Actual failed extraction evidence retained"
graph=(RECIPE/"extract_decl_graph.lean").read_text(encoding="utf-8-sig")
assert graph.count('import missions.zeta9.formalization.CoefficientMapSummation')==1
assert graph.count('IO.FS.writeFile "../decl_graph.jsonl"')==1
graph=graph.replace('import missions.zeta9.formalization.CoefficientMapSummation','import missions.zeta9.formalization.CoefficientMapAggregate')
graph=graph.replace('IO.FS.writeFile "../decl_graph.jsonl"','IO.FS.writeFile "'+(OUT/"native-decl-graph.jsonl").as_posix()+'"')
source=OUT/"extract-native-graph.lean";source.write_text(graph,encoding="utf-8");run("actual-stage1",source)
template=(RECIPE/"extract_CoefficientMapSummation_sketch.lean").read_text(encoding="utf-8-sig")
assert template.count('../CoefficientMapSummation-oracle-input.lean')==1
for n in list(prep["original_sources_sha256"])+["HarmonicStability"]:
    code=template.replace('../CoefficientMapSummation-oracle-input.lean',(OUT/(n+"-native-snapshot.lean")).as_posix())
    source=OUT/("extract-native-"+n+".lean");source.write_text(code,encoding="utf-8")
    actual=PROJECT/"Definitions/Def_ZetaNine_HarmonicStability.lean" if n=="HarmonicStability" else PROJECT/"missions/zeta9/formalization"/(n+".lean")
    run("actual-stage2-"+n,source,[actual.as_posix(),"ZetaNine"],OUT/(n+"-native-facts.jsonl"))
source=OUT/"extract-native-header.lean";source.write_bytes((RECIPE/"extract_header.lean").read_bytes())
run("actual-stage2-header",source,[(PROJECT/"missions/zeta9/formalization/CoefficientMapAggregate.lean").as_posix()],OUT/"native-header.jsonl")
write(OUT/"actual-extraction-receipt.json",{"status":"PREFREEZE_EXTRACTION_NOT_FINAL_VERDICT","rows":rows,"complete":True,
    "source_copies_byte_identical":True,"native_and_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False})
assert len(rows)==11 and all(r["exit_code"]==0 for r in rows)
