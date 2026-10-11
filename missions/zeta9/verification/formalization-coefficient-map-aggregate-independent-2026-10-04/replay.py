"""Independent Aggregate replay with explicitly verified prior independent dependencies."""
from pathlib import Path
import hashlib,json,subprocess,sys,shutil
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
AUTHOR=TASK/"verification/formalization-coefficient-map-aggregate-2026-10-04"
PRIOR=TASK/"verification/formalization-coefficient-map-summation-independent-2026-10-04"
REUSED=PRIOR/"native/build"
CACHE=OUT/"native/build"
CONTROL={"source":"e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299",
 "receipt":"3470a09613a9e8e2ac2995c17ff93b4481ca4a18748292594f0086283efc92b6",
 "manifest":"19054108e5c8c315e4c873d815cea2cd9049e9d61a5d392d3eb052cf1f24ceea",
 "prior_receipt":"105b370b310afef6959210faf12d7e687c2c760f2363ca6e0c03f6063fafb0b7",
 "prior_review":"fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def write(p,o):p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
def frozen():
 assert sha(TASK/"formalization/CoefficientMapAggregate.lean")==CONTROL["source"]
 assert sha(AUTHOR/"compile-receipt.json")==CONTROL["receipt"]
 assert sha(AUTHOR/"SHA256SUMS.txt")==CONTROL["manifest"]
 lines=[s.split("  ",1) for s in (AUTHOR/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines() if s.strip()]
 assert len(lines)==35
 assert all(sha(TASK/n)==h for h,n in lines)
 assert sha(PRIOR/"independent-compile-receipt.json")==CONTROL["prior_receipt"]
 assert sha(PRIOR/"independent-review.json")==CONTROL["prior_review"]
 for r in reused:
  assert r["exit_code"]==int((PRIOR/r["exit_file"]).read_text().strip())==0
  assert sha(ROOT/r["source_root_relative"])==r["source_sha256"]
  for f in ["log","exit_file","wrapper","output"]: assert sha(PRIOR/r[f])==r[f+"_sha256"]
prior=load(PRIOR/"independent-compile-receipt.json")
reused=[r for r in prior["rows"] if r["output"]]
assert len(reused)==8
frozen()
copies=[]
for r in reused:
 src=PRIOR/r["output"]
 dst=CACHE/src.relative_to(REUSED)
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists(): assert sha(dst)==r["output_sha256"]
 else: shutil.copyfile(src,dst)
 assert sha(dst)==r["output_sha256"]
 copies.append({"prior_task_relative":src.relative_to(TASK).as_posix(),
  "independent_task_relative":dst.relative_to(TASK).as_posix(),"sha256":sha(dst),"bytes":dst.stat().st_size})
write(OUT/"dependency-reuse.json",{"role":"Reuse reviewer-owned, previously fresh verified immutable actual dependencies only",
 "prior_review_sha256":CONTROL["prior_review"],"prior_receipt_sha256":CONTROL["prior_receipt"],
 "reused_native_sources":7,"reused_pure_Definitions":1,"cache_task_relative":REUSED.relative_to(TASK).as_posix(),
 "native_dependency_rows":reused,"byte_identical_cache_copies":copies,"author_cache_used":False,"native_root_cache_used":False,
 "cache_copy_reason":"Lean module lookup selects the first common directory prefix; cloning verified dependency objects into the new cache avoids partial prefix shadowing without rebuilding or using author objects."})
rows=[]
def run(label,source,output=None):
 wrapper=OUT/(label+".ps1")
 if output:output.parent.mkdir(parents=True,exist_ok=True)
 wrapper.write_text(f'$env:LEAN_PATH = "{CACHE.as_posix()};{REUSED.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean '+
  (('-o "'+output.as_posix()+'" ') if output else '')+'"'+source.as_posix()+'"\nexit $LASTEXITCODE\n',encoding="utf-8")
 cmd=["lake","env","pwsh","-NoProfile","-ExecutionPolicy","Bypass","-File",str(wrapper)]
 p=subprocess.run(cmd,cwd=ROOT,capture_output=True)
 log=OUT/(label+".log");log.write_bytes(p.stdout+p.stderr)
 ex=OUT/(label+"-exit.txt");ex.write_text(str(p.returncode)+"\n",encoding="utf-8")
 rows.append({"label":label,"command":cmd,"working_directory":str(ROOT),"exit_code":p.returncode,
  "source_root_relative":source.relative_to(ROOT).as_posix(),"source_sha256":sha(source),
  "log":log.name,"log_sha256":sha(log),"exit_file":ex.name,"exit_file_sha256":sha(ex),
  "wrapper":wrapper.name,"wrapper_sha256":sha(wrapper),"output":output.relative_to(OUT).as_posix() if output else None,
  "output_sha256":sha(output) if output and output.exists() else None})
 write(OUT/"independent-compile-receipt.json",{"review_role":"Independent Aggregate mathematical reviewer",
  "fixed_controls":CONTROL,"dependency_reuse_file":"dependency-reuse.json","dependency_reuse_sha256":sha(OUT/"dependency-reuse.json"),
  "rows":rows,"all_exit_codes_actually_observed":True,"root_scope_API_credentials_writes":False})
 print(label+": exit "+str(p.returncode),flush=True)
 frozen()
 assert p.returncode==0,log.read_text(encoding="utf-8-sig")
if "--boundary-only" not in sys.argv:
 run("native-Aggregate",TASK/"formalization/CoefficientMapAggregate.lean",CACHE/"missions/zeta9/formalization/CoefficientMapAggregate.olean")
 audit=OUT/"author-type-replay.lean";audit.write_bytes((AUTHOR/"type-audit.lean").read_bytes())
 run("author-type-replay",audit)
else:
 rows=load(OUT/"independent-compile-receipt.json")["rows"][:-1]
 assert len(rows)==2 and all(r["exit_code"]==0 for r in rows)
 for r in rows:
  assert sha(ROOT/r["source_root_relative"])==r["source_sha256"]
  for f in ["log","exit_file","wrapper","output"]:
   if r[f]:assert sha(OUT/r[f])==r[f+"_sha256"]
run("independent-boundary-audit",OUT/"independent-boundary-audit.lean")
