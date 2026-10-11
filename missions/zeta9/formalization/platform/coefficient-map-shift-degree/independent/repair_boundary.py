"""Resume only the two own audit controls after actual expression-normalization failure."""
from pathlib import Path
import ast,hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;PROJECT=OUT/"p"
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def dump(p,d):p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
snapshot=load(OUT/"same-fresh-project-boundary-resume.json")
assert snapshot["actual_successful_prefix_calls"]==27
for f in snapshot["files"]:assert sha(OUT/f["independent_relative"])==f["sha256"]
retained=OUT/"retained-attempt-02-negative-normalization"
def own_extra(p):
 tree=ast.parse(p.read_text(encoding="utf-8"))
 expr=[n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="extra" for t in n.targets)]
 assert len(expr)==1;return ast.literal_eval(expr[0])
old=own_extra(retained/"replay.py");new=own_extra(OUT/"replay.py")
s=(retained/"stage-boundary-audit.lean").read_text(encoding="utf-8");assert s.count(old)==1 and old!=new
s=s.replace(old,new)
for p in [OUT/"stage-boundary-audit.lean",PROJECT/"stage-boundary-audit.lean"]:p.write_text(s,encoding="utf-8",newline="\n")
receipt=load(retained/"independent-compile-receipt.json");assert len(receipt["rows"])==28 and receipt["rows"][-1]["exit_code"]==1
receipt["rows"]=receipt["rows"][:-1]
env=os.environ.copy();env.pop("LEAN_PATH",None);env["LEAN_NUM_THREADS"]="1"
p=subprocess.run(["lake","env","lean","stage-boundary-audit.lean"],cwd=PROJECT,env=env,capture_output=True)
log=OUT/"stage-boundary-audit.log";ex=OUT/"stage-boundary-audit-exit.txt";log.write_bytes(p.stdout+p.stderr);ex.write_text(str(p.returncode)+"\n",encoding="utf-8")
receipt["rows"].append({"label":"stage-boundary-audit","command":["lake","env","lean","stage-boundary-audit.lean"],"working_directory":str(PROJECT),"exit_code":p.returncode,"log":log.name,"log_sha256":sha(log),"exit_file":ex.name,"exit_file_sha256":sha(ex),"repair_scope":"Only two own added controls, no changes to native/author/old-boundary/platform proof code"})
receipt["same_fresh_project_actual_successful_prefix_reused"]=27
receipt["boundary_resume_snapshot_sha256"]=sha(OUT/"same-fresh-project-boundary-resume.json")
records=[json.loads(t) for t in p.stdout.decode("utf-8-sig").splitlines() if t.startswith("{")]
receipt["complete"]=p.returncode==0 and len(records)==46 and all(set(r["axioms"])<={"propext","Classical.choice","Quot.sound"} for r in records)
dump(OUT/"independent-compile-receipt.json",receipt)
print(json.dumps({"actual_boundary_exit":p.returncode,"records":len(records),"complete":receipt["complete"],"same_fresh_project_actual_successful_prefix_calls":27}),flush=True)
if p.returncode:print((p.stdout+p.stderr).decode("utf-8-sig"),flush=True)
assert receipt["complete"]
