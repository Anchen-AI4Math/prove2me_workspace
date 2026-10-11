"""Fresh independent FS graph/parser/header, seven staged modules and audits."""
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
NATIVE,PLATFORM = OUT/"cache/n",OUT/"cache/p"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def write(p,obj): p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
enrollment = load(OUT/"frozen-controls.json")
assert enrollment["status"] == "PARENT_FROZEN_AUTHOR_HANDOFF"
CONTROLS = enrollment["controls"]
def frozen():
    assert all(sha(BATCH/n) == h for n,h in CONTROLS.items())
    for row in load(BATCH/"source-manifest.json")["files"]:
        p = TASK/row["task_relative"]
        assert sha(p) == row["sha256"] and p.stat().st_size == row["bytes"]
frozen()
prep = load(OUT/"prepare-compile-receipt.json")
assert prep["complete"] and len(prep["rows"]) == 11 and all(row["exit_code"] == 0 for row in prep["rows"])
rows = []
def run(label,source,cache,output=None,args=None,stdout_copy=None):
    wrapper = OUT/(label+".ps1")
    cmd = f'$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean '
    if output:
        output.parent.mkdir(parents=True,exist_ok=True)
        cmd += '-o "'+output.as_posix()+'" '
    if args: cmd += '--run '
    cmd += '"'+source.as_posix()+'"'+''.join(' "'+a+'"' for a in args or [])+'\nexit $LASTEXITCODE\n'
    wrapper.write_text(cmd,encoding="utf-8")
    invocation = ["lake","env","pwsh","-NoProfile","-ExecutionPolicy","Bypass","-File",str(wrapper)]
    p = subprocess.run(invocation,cwd=ROOT,capture_output=True)
    log = OUT/(label+".log");log.write_bytes(p.stdout+p.stderr)
    if stdout_copy: stdout_copy.write_bytes(p.stdout)
    exitfile = OUT/(label+"-exit.txt");exitfile.write_text(str(p.returncode)+"\n",encoding="utf-8")
    rows.append({"label":label,"command":invocation,"working_directory":str(ROOT),"exit_code":p.returncode,
        "source_root_relative":source.relative_to(ROOT).as_posix(),"source_sha256":sha(source),"log":log.name,"log_sha256":sha(log),
        "exit_file":exitfile.name,"exit_file_sha256":sha(exitfile),"wrapper":wrapper.name,"wrapper_sha256":sha(wrapper),"cache":cache.relative_to(OUT).as_posix(),
        "output":output.relative_to(OUT).as_posix() if output else None,"output_sha256":sha(output) if output and output.exists() else None,
        "stdout_copy":stdout_copy.name if stdout_copy else None,"stdout_sha256":sha(stdout_copy) if stdout_copy else None})
    write(OUT/"replay-compile-receipt.json",{"review_role":"Independent FS transplant reviewer, not author","rows":rows,"complete":False,
        "author_frozen_controls":CONTROLS,"all_exit_codes_actually_observed":True,"native_and_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False})
    print(label+": exit "+str(p.returncode),flush=True)
    frozen()
    if p.returncode: print(log.read_text(encoding="utf-8-sig"),flush=True)
    assert p.returncode == 0,"Actual failed records retained."

graph = (BATCH/"extract_decl_graph.lean").read_text(encoding="utf-8-sig")
assert graph.count('IO.FS.writeFile "../decl_graph.jsonl"') == 1
graph = graph.replace('IO.FS.writeFile "../decl_graph.jsonl"','IO.FS.writeFile "'+(OUT/"native-decl-graph.jsonl").as_posix()+'"')
(OUT/"extract-native-graph.lean").write_text(graph,encoding="utf-8")
run("actual-stage1",OUT/"extract-native-graph.lean",NATIVE)
for name in list(prep["original_sources_sha256"])+["HarmonicStability"]:
    script = (BATCH/("extract_"+name+"_sketch.lean")).read_text(encoding="utf-8-sig")
    old = "../oracle-input.lean" if name == "CoefficientMapPartialFractions" else "../"+name+"-oracle-input.lean"
    assert script.count(old) == 1
    script = script.replace(old,(OUT/(name+"-native-snapshot.lean")).as_posix())
    extract = OUT/("extract-native-"+name+".lean")
    extract.write_text(script,encoding="utf-8")
    actual_source = ROOT/"Definitions/Def_ZetaNine_HarmonicStability.lean" if name == "HarmonicStability" else TASK/"formalization"/(name+".lean")
    run("actual-stage2-"+name,extract,NATIVE,args=[actual_source.as_posix(),"ZetaNine"],stdout_copy=OUT/(name+"-native-facts.jsonl"))
header = OUT/"extract-native-header.lean";header.write_bytes((BATCH/"extract_header.lean").read_bytes())
run("actual-stage2-header",header,NATIVE,args=[(TASK/"formalization/CoefficientMapFiniteSum.lean").as_posix()],stdout_copy=OUT/"native-header.jsonl")
for row in load(BATCH/"root-copy-plan.json")["files"]:
    source = TASK/row["staged_task_relative"]
    assert sha(source) == row["sha256"]
    destination = PLATFORM/(row["root_relative_destination"].removesuffix(".lean")+".olean")
    run("staged-"+source.stem,source,PLATFORM,output=destination)
audit_scripts = ["types_original.lean","types_definition.lean"]+[f"types_{i}_{kind}.lean" for i in range(3) for kind in ["solution","reference"]]+[f"helpers_{i}.lean" for i in range(3)]+["stage-boundary-audit.lean"]
for name in audit_scripts:
    source = OUT/name;source.write_bytes((BATCH/name).read_bytes())
    run("replay-"+source.stem,source,NATIVE if name == "types_original.lean" else PLATFORM)
run("independent-new-boundary",OUT/"new-boundary-audit.lean",PLATFORM)
graph_rows = [json.loads(line) for line in (OUT/"native-decl-graph.jsonl").read_text(encoding="utf-8-sig").splitlines() if line.startswith("{")]
by_name = {r["name"]:r for r in graph_rows}
core = [r for r in graph_rows if r["module"].endswith(".CoefficientMapFiniteSum") and r["startLine"] > 0]
assert len(core) == 11
reached,work = set(),[r["name"] for r in core]+[r["name"] for r in graph_rows if r["isInstance"]]
while work:
    name = work.pop()
    if name in reached:continue
    reached.add(name);work.extend(by_name[name]["typeDeps"]+by_name[name]["valueDeps"])
proof_names = sorted(name for name in reached if by_name[name]["kind"] == "theorem" and by_name[name]["startLine"] > 0)
text = '''import missions.zeta9.formalization.CoefficientMapFiniteSum
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  for name in [
'''+",\n".join("    `"+name for name in proof_names)+'''] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString))]).compress
'''
native_audit = OUT/"independent-native-required-proofs.lean";native_audit.write_text(text,encoding="utf-8")
run("independent-native-required-proofs",native_audit,NATIVE)
write(OUT/"replay-compile-receipt.json",{"review_role":"Independent FS transplant reviewer, not author","rows":rows,"complete":True,
    "author_frozen_controls":CONTROLS,"all_exit_codes_actually_observed":True,"native_and_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False,
    "native_actual_proof_names":proof_names})
