"""Independent fresh-cache replay of the frozen ShiftDegree transplantation."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=BATCH.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/"project"
NS="ZetaNine.CoefficientMapShiftDegree";REV="0df444a360eaa60ab8c11dca51a86af692955474";STD={"propext","Classical.choice","Quot.sound"}
FIXED={"author-audit.json":"6139eee95fa63d6427a2bced0171b7ae9c5ec6917fcfa124802a995f32e06e18","root-copy-plan.json":"48edfb368179cb7ed0f746ca2acc4bbafc06103d5e6bc498cdc8b4e6e42e3cb9","source-manifest.json":"1b6cfe2801c068581b46172b156e0516c0cceda6c5b7143258f10d9f5d066278","SHA256SUMS.txt":"f393fbe26239c2743e8198e5fa5a9c212c0935b127566577992a6589b93510ce"}
SOURCE_SHA="96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953"
NATIVE="missions.zeta9.formalization.CoefficientMapShiftDegree"
TARGETS=["actual_shift_difference_coefficient","actual_shift_difference_degree_lower_bound","actual_shift_difference_small_degree_implies_zero"]
ARGS=["n H hH","n hn H hH hdeg","n hn H hdeg hsmall"]
DEFS=["shiftA","shiftB","shiftDifference"]
MATHLIB=["Mathlib.Algebra.Polynomial.Taylor","Mathlib.Algebra.Polynomial.Reverse","Mathlib.Tactic"]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode("utf-8"))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
for n,h in FIXED.items():assert sha(BATCH/n)==h
source=TASK/"formalization/CoefficientMapShiftDegree.lean";assert sha(source)==SOURCE_SHA
old_lines=(BATCH/"SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines();assert len(old_lines)==128
for l in old_lines:
 h,rel=l.split("  ",1);assert sha(BATCH/rel)==h
assert not (PROJECT/".lake/build").exists(),"The independent project must start with no project objects."
plan=load(BATCH/"target-plan.json");assert len(plan["targets"])==3 and not plan["existing_definitions"]
assert [t["theorem_name"] for t in plan["targets"]]==[NS+"."+n for n in TARGETS]
assert [t["wrapper_arguments"] for t in plan["targets"]]==ARGS
write(PROJECT/"lakefile.lean",f'''import Lake
open Lake DSL
package zeta9ShiftDegreeIndependentReview
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`{NATIVE}]
  globs := #[.one `{NATIVE}]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for name in ["lean-toolchain","lake-manifest.json"]:write(PROJECT/name,(ROOT/name).read_bytes())
(PROJECT/".lake").mkdir(exist_ok=True)
p=subprocess.run(["cmd","/c","mklink","/J",str(PROJECT/".lake/packages"),str(ROOT/".lake/packages")],capture_output=True);assert p.returncode==0
write(PROJECT/(NATIVE.replace(".","/")+".lean"),source.read_bytes())
for rel in [plan["local_definition"]]+[t[k] for t in plan["targets"] for k in ["local_solution","local_reference"]]:
 assert (ROOT/rel).read_bytes()==(BATCH/"staged"/rel).read_bytes();write(PROJECT/rel,(BATCH/"staged"/rel).read_bytes())
kit=TASK/"formalization/platform/coefficient-map-jet"
graph=(kit/"extract_decl_graph.lean").read_text(encoding="utf-8-sig").replace("import missions.zeta9.formalization.CoefficientMapJet","import "+NATIVE).replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")
parser=(kit/"extract_sketch_info.lean").read_text(encoding="utf-8-sig")
old_output="missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean"
for label,snapshot in [("source","source-oracle-input.lean"),("native-author","native-author-oracle-input.lean"),("native-independent","native-independent-oracle-input.lean")]:
 code=parser.replace(old_output,"../"+snapshot);assert code!=parser
 write(OUT/("parse-"+label+".lean"),code);write(PROJECT/("parse-"+label+".lean"),code)
write(OUT/"extract_decl_graph.lean",graph);write(PROJECT/"extract_decl_graph.lean",graph)
for dest in [OUT/"extract_header.lean",PROJECT/"extract_header.lean"]:write(dest,(kit/"extract_header.lean").read_bytes())
receipt={"review_role":"independent transplantation reviewer; not platform batch author","source_sha256":SOURCE_SHA,"fixed_platform_controls":FIXED,"native_or_staged_objects_borrowed":False,"only_Mathlib_package_cache_shared":True,"project_build_cache_absent_before_replay":True,"rows":[],"complete":False}
env=os.environ.copy();env.pop("LEAN_PATH",None);env["LEAN_NUM_THREADS"]="1"
def run(label,args,stdout_file=None):
 p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
 log=OUT/(label+".log");ex=OUT/(label+"-exit.txt");write(log,p.stdout+p.stderr);write(ex,str(p.returncode)+"\n")
 if stdout_file:write(OUT/stdout_file,p.stdout)
 r={"label":label,"command":args,"working_directory":str(PROJECT),"exit_code":p.returncode,"log":log.name,"log_sha256":sha(log),"exit_file":ex.name,"exit_file_sha256":sha(ex)}
 if args[:3]==["lake","--no-cache","build"]:
  mod=args[3];obj=PROJECT/".lake/build/lib/lean"/(mod.replace(".","/")+".olean");src=PROJECT/(mod.replace(".","/")+".lean")
  if p.returncode==0:
   assert obj.exists();r.update({"source_project_relative":src.relative_to(PROJECT).as_posix(),"source_sha256":sha(src),"object_project_relative":obj.relative_to(PROJECT).as_posix(),"object_sha256":sha(obj)})
 receipt["rows"].append(r);dump(OUT/"independent-compile-receipt.json",receipt)
 print(label+": actual exit "+str(p.returncode),flush=True)
 if p.returncode:print(log.read_text(encoding="utf-8-sig"),flush=True)
 assert p.returncode==0
 for n,h in FIXED.items():assert sha(BATCH/n)==h
 assert sha(source)==SOURCE_SHA
run("toolchain",["lake","env","lean","--version"])
run("native-source",["lake","--no-cache","build",NATIVE])
run("stage1",["lake","env","lean","extract_decl_graph.lean"])
run("stage2-source",["lake","env","lean","--run","parse-source.lean",NATIVE.replace(".","/")+".lean","ZetaNine"],"sketch_info.jsonl")
run("source-header",["lake","env","lean","--run","extract_header.lean",NATIVE.replace(".","/")+".lean"],"header_info.jsonl")
grows=rows(OUT/"decl_graph.jsonl");core=[g for g in grows if g["startLine"]>0];assert len(grows)==18 and len(core)==15 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==12
def gen_report(filename,module,names):
 code="import "+module+"\nimport Lean\nopen Lean\nset_option pp.fullNames true\nset_option pp.universes false\n\n"
 code+='''run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let (val, raw) ← match ci with
      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty, some (reprStr d.value))
      | _ => pure (none, none)
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson val),("definition_expression_repr",toJson raw),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 code+="".join('  emit "'+label+'" `'+name+'\n' for label,name in names)
 write(OUT/filename,code);write(PROJECT/filename,code)
defs=[NS+"."+n for n in DEFS]
proofs=[g["name"] for g in sorted(core,key=lambda g:g["startLine"]) if g["kind"]=="theorem"]
gen_report("types-native.lean",NATIVE,[(n,n) for n in defs+proofs])
gen_report("types-definition.lean",plan["local_definition"].removesuffix(".lean").replace("/","."),[(n,n) for n in defs])
for i,t in enumerate(plan["targets"]):
 for k in ["solution","reference"]:
  m=t["local_"+k].removesuffix(".lean").replace("/",".");gen_report(f"types-{i}-{k}.lean",m,[(n,n) for n in defs]+[(t["theorem_name"],"solution" if k=="solution" else t["theorem_name"])])
 names=[NS+".checked_"+TARGETS[i] if n==t["theorem_name"] else n for n in proofs]+["solution"]
 gen_report(f"proofs-{i}.lean",t["local_solution"].removesuffix(".lean").replace("/","."),[(n,n) for n in names])
run("definition",["lake","--no-cache","build",plan["local_definition"].removesuffix(".lean").replace("/",".")])
for i,t in enumerate(plan["targets"]):
 for k in ["solution","reference"]:run(f"stage-{i}-{k}",["lake","--no-cache","build",t["local_"+k].removesuffix(".lean").replace("/",".")])
for label in ["types-native","types-definition"]+[f"types-{i}-{k}" for i in range(3) for k in ["solution","reference"]]+[f"proofs-{i}" for i in range(3)]:run(label,["lake","env","lean",label+".lean"])
fixtures={"native-author":TASK/"verification/formalization-coefficient-map-shift-degree-2026-10-04/type-audit.lean","native-independent":TASK/"verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-boundary-audit.lean"}
fixture_facts={};fixture_bytes={}
for label,f in fixtures.items():
 write(PROJECT/(label+".lean"),f.read_bytes());write(OUT/(label+".lean"),f.read_bytes())
 run(label,["lake","env","lean",label+".lean"])
 run("stage2-"+label,["lake","env","lean","--run","parse-"+label+".lean",label+".lean"],label+"-sketch_info.jsonl")
 fixture_facts[label]=rows(OUT/(label+"-sketch_info.jsonl"));fixture_bytes[label]=(OUT/(label+"-oracle-input.lean")).read_bytes()
 assert fixture_bytes[label]==f.read_bytes().replace(b"\r\n",b"\n")
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
low=TARGETS[2];selected=NS+"."+low;closed=[];fp={}
boundary="import "+plan["targets"][2]["local_solution"].removesuffix(".lean").replace("/",".")+"\nimport Lean\nopen Lean Meta Polynomial\nopen "+NS+"\nset_option autoImplicit false\nset_option pp.fullNames true\nset_option pp.universes false\nset_option maxHeartbeats 2200000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n"
for label,expected in [("native-author",7),("native-independent",17)]:
 fs=fixture_facts[label];b=fixture_bytes[label];ds=[f for f in fs if f["kind"]=="decl"];assert len(ds)==expected
 renames=[]
 for d in ds:
  a,z=d["declStart"]["offset"],d["declEnd"]["offset"];v=d["valStart"]["offset"]
  bindings=[r for r in fs if r["kind"]=="ref" and a<=r["start"]["offset"]<v and r["const"].startswith("checked_" if label=="native-author" else "shift_ind_")]
  assert len(bindings)==1;closed.append(bindings[0]["const"]);es=[]
  for r in fs:
   if r["kind"]!="ref" or r["const"]!=selected:continue
   x,y=r["start"]["offset"],r["end"]["offset"]
   if a<=x<y<=z:
    old=b[x:y].decode();assert old in [low,selected];es.append((x-a,y-a,("checked_"+low if old==low else NS+".checked_"+low).encode()));renames.append(r)
  boundary+=edit(b[a:z],es).decode()+"\n\n"
 fp[label]={"source_task_relative":fixtures[label].relative_to(TASK).as_posix(),"source_sha256":sha(fixtures[label]),"snapshot_sha256":sha(OUT/(label+"-oracle-input.lean")),"normalization":"exact official CRLF to LF normalization","actual_decl_facts":ds,"actual_selected_ref_renames":renames,"other_original_proof_edits":[]}
extra='''
theorem shift_review_zero_solution (n : ℕ) (hn : 1 ≤ n) : (0 : ℚ[X]) = 0 :=
  solution n hn 0 (by simp) (by simp [shiftDifference])

theorem shift_review_zero_degree (n : ℕ) :
    (shiftDifference n (0 : ℚ[X])).degree = ⊥ ∧
    (shiftDifference n (0 : ℚ[X])).natDegree = 0 := by
  simp [shiftDifference]

theorem shift_review_nonmonic_n_zero : (shiftDifference 0 (C (-2 : ℚ))).coeff 10 = 4 := by
  have h := actual_shift_difference_coefficient 0 (C (-2 : ℚ)) (by norm_num)
  norm_num at h
  exact h

theorem shift_review_negative_n_two : (shiftDifference 2 (C (-3 : ℚ) * X ^ 11)).coeff 21 = -3 := by
  have hC : (C (-3 : ℚ) : ℚ[X]) ≠ 0 := by norm_num
  have hX : (X ^ 11 : ℚ[X]) ≠ 0 := pow_ne_zero 11 X_ne_zero
  have hd : (C (-3 : ℚ) * X ^ 11 : ℚ[X]).natDegree = 11 := by
    rw [natDegree_mul hC hX]; simp
  have hl : (C (-3 : ℚ) * X ^ 11 : ℚ[X]).leadingCoeff = -3 := by simp [leadingCoeff_mul]
  have h := actual_shift_difference_coefficient 2 (C (-3 : ℚ) * X ^ 11) (mul_ne_zero hC hX)
  norm_num [hd,hl] at h
  exact h

theorem shift_review_resonance_and_actual_eval :
    (shiftDifference 1 (X ^ 5 : ℚ[X])).coeff 15 = 0 ∧
    ¬ (X ^ 5 : ℚ[X]).natDegree ≤ 7 * 1 - 3 ∧
    (shiftDifference 1 (X ^ 5 : ℚ[X])).eval 1 = -1152 := by
  refine ⟨shift_ind_resonance_n_one.1,shift_ind_resonance_n_one.2,?_⟩
  exact shift_ind_resonance_operator_still_nonzero

theorem shift_review_resonance_nonzero : shiftDifference 1 (X ^ 5 : ℚ[X]) ≠ 0 := by
  intro h
  have hv := congrArg (fun P : ℚ[X] => P.eval 1) h
  rw [shift_ind_resonance_operator_still_nonzero] at hv
  norm_num at hv

theorem shift_review_eval_n_zero (H : ℚ[X]) (t : ℚ) :
    (shiftDifference 0 H).eval t =
      (t - 1) * t ^ 10 * H.eval t - t ^ 10 * (t + 1) * H.eval (t + 1) := by
  simp [shiftDifference,shiftA,shiftB,eval_comp]

'''
extra_names=["shift_review_zero_solution","shift_review_zero_degree","shift_review_nonmonic_n_zero","shift_review_negative_n_two","shift_review_resonance_and_actual_eval","shift_review_resonance_nonzero","shift_review_eval_n_zero"]
boundary+=extra
boundary+='''run_meta do
  let emit (kind : String) (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let val ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("definitionValue",val),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
exact_names=[NS+".checked_"+low if n==selected else n for n in defs+proofs]+closed
assert len(exact_names)==39
boundary+='  for name in ['+', '.join('`'+n for n in exact_names)+'] do emit "native_exact" name\n'
boundary+='  for name in ['+', '.join('`'+n for n in extra_names)+'] do emit "new_independent_control" name\n'
write(OUT/"stage-boundary-audit.lean",boundary);write(PROJECT/"stage-boundary-audit.lean",boundary)
dump(OUT/"boundary-provenance.json",{"fixtures":fp,"original_native_records":39,"new_independent_controls":extra_names,"exact_names":exact_names,"only_actual_parser_proof_spans_and_selected_refs_changed":True})
run("stage-boundary-audit",["lake","env","lean","stage-boundary-audit.lean"])
rs=rows(OUT/"stage-boundary-audit.log");assert len(rs)==46 and all(set(r["axioms"])<=STD for r in rs)
receipt["complete"]=True;dump(OUT/"independent-compile-receipt.json",receipt)
print(json.dumps({"independent_actual_exit_zero_calls":len(receipt["rows"]),"fresh_native_and_staged_objects":8,"proof_records":39,"definition_comparisons_expected":21,"native_boundary_replay":39,"new_controls":7}),flush=True)
