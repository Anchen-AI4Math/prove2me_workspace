"""Replay actual native author/independent boundaries against the staged Solution.

Additional genuine HasSum parent helpers are copied by graph/parser spans into
this audit alone. They do not enlarge the seven published staged source files.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT/"project"
NS="ZetaNine.CoefficientMapAggregate";STD={"propext","Classical.choice","Quot.sound"}
FIXTURES={
 "author":TASK/"verification/formalization-coefficient-map-aggregate-2026-10-04/type-audit.lean",
 "independent":TASK/"verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-boundary-audit.lean",
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.write_bytes(s if isinstance(s,bytes) else s.encode("utf-8"))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
def rows(p):return [json.loads(x) for x in p.read_text(encoding="utf-8-sig").splitlines() if x.startswith("{")]
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):
  assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
env=os.environ.copy();env.pop("LEAN_PATH",None);env["LEAN_NUM_THREADS"]="1"
receipt={"role":"author staged boundary replay","rows":[],"complete":False}
def run(label,args,stdout_file=None):
 p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
 log=OUT/(label+".log");write(log,p.stdout+p.stderr);write(OUT/(label+"-exit.txt"),str(p.returncode)+"\n")
 if stdout_file:write(OUT/stdout_file,p.stdout)
 receipt["rows"].append({"label":label,"command":args,"exit_code":p.returncode,"log":log.name,"log_sha256":sha(log),"exit_file":label+"-exit.txt","exit_file_sha256":sha(OUT/(label+"-exit.txt"))})
 dump(OUT/"boundary-compile-receipt.json",receipt)
 print(label+": exit "+str(p.returncode),flush=True)
 if p.returncode:print(log.read_text(encoding="utf-8-sig"),flush=True)
 assert p.returncode==0

main=json.loads((OUT/"compile-receipt.json").read_text(encoding="utf-8"));assert main["complete"] and all(r["exit_code"]==0 for r in main["rows"])
prov=json.loads((OUT/"integration-provenance.json").read_text(encoding="utf-8"))
graph=rows(OUT/"decl_graph.jsonl");byname={g["name"]:g for g in graph}
sources={n:(OUT/("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in main["source_sha256"]}
facts={n:rows(OUT/("sketch_info.jsonl" if n.endswith("PartialFractions") else n+"-sketch_info.jsonl")) for n in sources}
def declaration(g):
 n=g["module"].split(".")[-1]
 ds=[f for f in facts[n] if f["kind"]=="decl" and f["declStart"]["line"]<=g["startLine"]<=f["declEnd"]["line"]]
 assert g["startLine"]>0 and len(ds)==1;return ds[0]
def closure(seeds):
 seen=set();todo=list(seeds)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if n in byname:todo.extend(byname[n]["typeDeps"]+byname[n]["valueDeps"])
 return seen

parser=(OUT/"extract_CoefficientMapAggregate_sketch.lean").read_text(encoding="utf-8-sig")
fixture_facts={};fixture_sources={}
for label,original in FIXTURES.items():
 write(PROJECT/("boundary-"+label+"-input.lean"),original.read_bytes())
 code=parser.replace("../CoefficientMapAggregate-oracle-input.lean","../boundary-"+label+"-oracle-input.lean")
 assert code!=parser
 write(OUT/("extract_boundary_"+label+".lean"),code);write(PROJECT/("extract_boundary_"+label+".lean"),code)
 # No prefix filter: retain the global audit theorem binding references too.
 run("stage2-boundary-"+label,["lake","env","lean","--run","extract_boundary_"+label+".lean","boundary-"+label+"-input.lean"],"boundary-"+label+"-sketch_info.jsonl")
 fixture_facts[label]=rows(OUT/("boundary-"+label+"-sketch_info.jsonl"))
 fixture_sources[label]=(OUT/("boundary-"+label+"-oracle-input.lean")).read_bytes()
 assert fixture_sources[label]==original.read_bytes()

selected=NS+".aggregate_zero_all_rho"
provided=set(prov["inline_helper_names"])|{g["name"] for g in graph if g["module"].endswith(".CoefficientMapAggregate") and g["kind"]=="theorem" and g["startLine"]>0}
seeds={f["const"] for fs in fixture_facts.values() for f in fs if f["kind"]=="ref" and f["const"] in byname}
extra=[byname[n] for n in closure(seeds) if n in byname and byname[n]["kind"]=="theorem" and byname[n]["startLine"]>0 and n not in provided]
extra.sort(key=lambda g:(list(sources).index(g["module"].split(".")[-1]),g["startLine"]))
bridge="";extra_facts=[];opens=[]
for module in sources:
 hs=[g for g in extra if g["module"].endswith("."+module)]
 if not hs:continue
 assert module!="CoefficientMapAggregate"
 bridge+="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
 first=min(g["startLine"] for g in graph if g["module"].endswith("."+module) and g["startLine"]>0)
 os_=[f for f in facts[module] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["line"]<first]
 for f in os_:
  bridge+=sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\n";opens.append({"module":module,"fact":f})
 if os_:bridge+="\n"
 for g in hs:
  f=declaration(g);bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n";extra_facts.append({"module":module,"name":g["name"],"fact":f})
 bridge+="end ZetaNine."+module+"\n\n"
write(OUT/"boundary-only-proof-bridge.lean.inc",bridge)
code="import Solutions.Sol_ZetaNine_CoefficientMapAggregate_aggregate_zero_all_rho\nimport Lean\nimport Mathlib.Tactic\n\n"+bridge
code+="open Lean Meta Polynomial Finset\nopen scoped BigOperators\nopen ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation\nset_option autoImplicit false\nset_option pp.fullNames true\nset_option pp.universes false\nset_option maxHeartbeats 2200000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n"
fixture_provenance={};closed_names=[]
for label in FIXTURES:
 b=fixture_sources[label];fs=fixture_facts[label];ds=[f for f in fs if f["kind"]=="decl"]
 expected=6 if label=="author" else 22;assert len(ds)==expected,(label,len(ds))
 renames=[]
 for f in ds:
  a,z=f["declStart"]["offset"],f["declEnd"]["offset"];v=f["valStart"]["offset"]
  # Global audit bindings are parser-owned declaration signature references.
  binding=[r for r in fs if r["kind"]=="ref" and a<=r["start"]["offset"]<v and r["const"].startswith("checked_" if label=="author" else "agg_ind_")]
  assert len(binding)==1,(label,binding);closed_names.append(binding[0]["const"])
  changes=[]
  for r in fs:
   if r["kind"]!="ref" or r["const"]!=selected:continue
   x,y=r["start"]["offset"],r["end"]["offset"]
   if a<=x<y<=z:
    old=b[x:y].decode();assert old in ["aggregate_zero_all_rho",selected]
    changes.append((x-a,y-a,("checked_aggregate_zero_all_rho" if old=="aggregate_zero_all_rho" else NS+".checked_aggregate_zero_all_rho").encode()));renames.append(r)
  code+=edit(b[a:z],changes).decode()+"\n\n"
 fixture_provenance[label]={"original_task_relative":FIXTURES[label].relative_to(TASK).as_posix(),"original_sha256":sha(FIXTURES[label]),"actual_declaration_facts":ds,"selected_actual_ref_renames":renames,"original_proof_body_other_changes":[]}
native_names=[g["name"] for g in graph if g["module"].endswith(".CoefficientMapAggregate") and g["startLine"]>0]
assert len(native_names)==26 and len(closed_names)==28
native_names=[NS+".checked_aggregate_zero_all_rho" if n==selected else n for n in native_names]
names=native_names+closed_names
code+='''run_meta do
  let emit (kind : String) (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let val ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("axioms",toJson (axs.toList.map Name.toString)),
      ("definitionValue",val)]).compress
'''
code+='  for name in ['+', '.join('`'+n for n in names)+'] do emit "native_exact_boundary" name\n'
code+='  for name in ['+', '.join('`'+g["name"] for g in extra)+'] do emit "boundary_only_genuine_helper" name\n'
write(OUT/"stage-boundary-audit.lean",code);write(PROJECT/"stage-boundary-audit.lean",code)
dump(OUT/"stage-boundary-provenance.json",{"fixtures":fixture_provenance,"additional_parent_proofs_only_in_audit":extra_facts,"additional_parent_open_context":opens,"extra_helpers_not_in_seven_platform_staged_files":True,"all_boundary_names":names,"extra_helper_names":[g["name"] for g in extra]})
run("stage-boundary-audit",["lake","env","lean","stage-boundary-audit.lean"])
rs=rows(OUT/"stage-boundary-audit.log");actual=[r for r in rs if r["kind"]=="native_exact_boundary"]
assert len(actual)==54 and all(set(r["axioms"])<=STD for r in rs)
dump(OUT/"stage-boundary-report.json",{"exit_code":0,"records":actual,"extra_helper_records":[r for r in rs if r["kind"]=="boundary_only_genuine_helper"],"all_standard_axioms":True,"log_sha256":sha(OUT/"stage-boundary-audit.log")})
receipt["complete"]=True;dump(OUT/"boundary-compile-receipt.json",receipt)
print(json.dumps({"actual_boundary_records":54,"extra_audit_only_parent_helpers":len(extra),"observed_exit_zero_runs":len(receipt["rows"])}),flush=True)
