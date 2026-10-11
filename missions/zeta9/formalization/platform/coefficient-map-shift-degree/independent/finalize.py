"""Independent integration review from observed replay and original parser facts."""
from pathlib import Path
import hashlib,json,os,subprocess,datetime,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=BATCH.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/"p"
NS="ZetaNine.CoefficientMapShiftDegree";STD={"propext","Classical.choice","Quot.sound"};REV="0df444a360eaa60ab8c11dca51a86af692955474"
FIXED={"author-audit.json":"6139eee95fa63d6427a2bced0171b7ae9c5ec6917fcfa124802a995f32e06e18","root-copy-plan.json":"48edfb368179cb7ed0f746ca2acc4bbafc06103d5e6bc498cdc8b4e6e42e3cb9","source-manifest.json":"1b6cfe2801c068581b46172b156e0516c0cceda6c5b7143258f10d9f5d066278","SHA256SUMS.txt":"f393fbe26239c2743e8198e5fa5a9c212c0935b127566577992a6589b93510ce"}
SOURCE_SHA="96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953"
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,s):p.write_bytes(s if isinstance(s,bytes) else s.encode("utf-8"))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
checks=[]
def check(name,p,detail=None):
 checks.append({"name":name,"pass":bool(p),"detail":detail});assert p,name
receipt=load(OUT/"independent-compile-receipt.json");plan=load(BATCH/"target-plan.json");author=load(BATCH/"author-audit.json");copy=load(BATCH/"root-copy-plan.json");aprov=load(BATCH/"integration-provenance.json")
check("fixed_author_controls_24_checks_and_leaf_source",all(sha(BATCH/n)==h for n,h in FIXED.items()) and author["verdict"]=="PASS" and len(author["checks"])==24 and all(c["pass"] for c in author["checks"]) and sha(TASK/"formalization/CoefficientMapShiftDegree.lean")==SOURCE_SHA,{"controls":FIXED,"independent_review_not_inferred_from_author_PASS":True})
author_members=[]
for line in (BATCH/"SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
 h,rel=line.split("  ",1);assert sha(BATCH/rel)==h;author_members.append(BATCH/rel)
check("all_128_frozen_author_members_hashes_unchanged",len(author_members)==128)
check("fresh_independent_project_no_native_or_stage_object_reuse",receipt["complete"] and receipt["native_or_staged_objects_borrowed"] is False and receipt["only_Mathlib_package_cache_shared"] and receipt["project_build_cache_absent_before_replay"],{"native_source_rebuilt":True,"eight_native_and_staged_modules_fresh":True,"old_own_math_cache_reused":False,"platform_author_objects_reused":False})
attempt=load(OUT/"retained-long-path-failure.json")
check("retained_Windows_long_path_write_failure_excluded_new_short_project_fresh",attempt["failure_used_for_final_PASS"] is False and attempt["actual_failed_exit_code"]==1 and attempt["source_or_kernel_error"] is False and attempt["old_own_or_author_objects_reused_in_final"] is False and receipt["project"]=="p" and receipt["build_directory"]=="b" and all(sha(OUT/f["independent_relative"])==f["sha256"] if f["retained_copy"] is None else sha(OUT/f["retained_copy"])==f["sha256"] for f in attempt["files"]),{"initial_attempt_actual_successes":10,"initial_failed_module_source_compiled_std3_but_object_write_failed":True,"final_proof_cache_objects_fresh_not_resumed":True})
negative_attempt=load(OUT/"retained-boundary-negative-normalization-failure.json");resume=load(OUT/"same-fresh-project-boundary-resume.json")
check("own_negative_control_error_placeholders_excluded_27_actual_successes_same_fresh_cache_bound",negative_attempt["failure_used_for_final_PASS"] is False and negative_attempt["actual_exit_code"]==1 and negative_attempt["original_source_or_staged_platform_issue"] is False and negative_attempt["Lean_error_placeholders_sorryAx_in_failed_audit_excluded"] and receipt["same_fresh_project_actual_successful_prefix_reused"]==27 and receipt["boundary_resume_snapshot_sha256"]==negative_attempt["resume_snapshot_sha256"]==sha(OUT/"same-fresh-project-boundary-resume.json") and all(sha(OUT/f["independent_relative"])==f["sha256"] for f in resume["files"]) and all(sha(OUT/f["independent_relative"])==f["sha256"] for f in negative_attempt["retained_files"]),{"repair":"Only two new independent negative-polynomial controls add map_neg/neg_mul normalization; no original or staged proof edited.","failed_audit_actual_exit":1,"failed_sorryAx_records_used_for_PASS":False})
check("all_28_independent_observed_calls_actual_exit_zero",len(receipt["rows"])==28 and all(r["exit_code"]==0 and sha(OUT/r["log"])==r["log_sha256"] and sha(OUT/r["exit_file"])==r["exit_file_sha256"] and (OUT/r["exit_file"]).read_text().strip()=="0" for r in receipt["rows"]),{"native_source_build":1,"stage_modules":7,"type_and_proof_reports":11,"actual_source_graph_parser_header":3,"two_native_boundary_replays_and_two_actual_parsers":4,"staged_boundary_with_new_controls":1,"version_probe":1})
objects=[]
for r in receipt["rows"]:
 if "object_project_relative" not in r:continue
 src=PROJECT/r["source_project_relative"];obj=PROJECT/r["object_project_relative"]
 assert sha(src)==r["source_sha256"] and sha(obj)==r["object_sha256"];objects.append(obj)
check("eight_real_fresh_compiled_objects_and_source_receipts_bound",len(objects)==8,{"objects":[r for r in receipt["rows"] if "object_project_relative" in r]})
env=os.environ.copy();env.pop("LEAN_PATH",None)
p=subprocess.run(["git","-C",str(ROOT/".lake/packages/mathlib"),"rev-parse","HEAD"],capture_output=True,env=env)
write(OUT/"mathlib-revision.log",p.stdout+p.stderr)
check("actual_Lean_4_33_1_and_fixed_Mathlib_revision",p.returncode==0 and p.stdout.decode().strip()==REV and "version 4.33.1" in (OUT/"toolchain.log").read_text(encoding="utf-8-sig"))
old_math_path=TASK/"verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-review.json";old_math=load(old_math_path)
check("prior_independent_native_mathematics_review_fixed_only_context_not_cache_reuse",sha(old_math_path)=="d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df" and old_math["verdict"]=="PASS" and len(old_math["checks"])==16 and len(old_math["stable_files"])==54,{"actual_new_source_recompile":True,"old_native_or_stage_objects_not_reused":True,"prior_report_sha256":sha(old_math_path)})
native={r["label"]:r for r in rows(OUT/"types-native.log")};definitions=[NS+"."+n for n in ["shiftA","shiftB","shiftDifference"]]
contexts=["types-definition"]+[f"types-{i}-{k}" for i in range(3) for k in ["solution","reference"]]
rs={c:{r["label"]:r for r in rows(OUT/(c+".log"))} for c in contexts}
dc=[]
for n in definitions:
 for c in contexts:
  a=native[n];b=rs[c][n]
  dc.append({"declaration":n,"context":c,"type_equal":a["type"]==b["type"],"pretty_value_equal":a["value"]==b["value"],"full_type_Expr_repr_equal":a["type_expression_repr"]==b["type_expression_repr"],"full_value_Expr_repr_equal":a["definition_expression_repr"]==b["definition_expression_repr"],"axioms":b["axioms"]})
check("three_pure_Def_types_values_and_full_Expr_exact_21_comparisons",len(dc)==21 and all(d["type_equal"] and d["pretty_value_equal"] and d["full_type_Expr_repr_equal"] and d["full_value_Expr_repr_equal"] and set(d["axioms"])<=STD for d in dc),{"actual_Definitions":definitions,"no_proof_field_PP_elision_issue":True,"contexts":7})
targets=[]
for i,t in enumerate(plan["targets"]):
 n=t["theorem_name"];a=native[n];s=rs[f"types-{i}-solution"][n];r=rs[f"types-{i}-reference"][n]
 targets.append({"theorem":n,"actual_original_type":a["type"],"original_solution_reference_type_equal":a["type"]==s["type"]==r["type"],"full_original_solution_reference_type_Expr_equal":a["type_expression_repr"]==s["type_expression_repr"]==r["type_expression_repr"],"original_axioms":a["axioms"],"solution_axioms":s["axioms"],"reference_axioms":r["axioms"]})
check("three_public_original_Solution_reference_types_exact_no_extra_hypotheses",all(t["original_solution_reference_type_equal"] and t["full_original_solution_reference_type_Expr_equal"] for t in targets),targets)
check("three_complete_Solutions_and_native_targets_only_standard_three_axioms",all(set(t["original_axioms"])==STD and set(t["solution_axioms"])==STD for t in targets))
proofs=[rows(OUT/f"proofs-{i}.log") for i in range(3)]
check("all_12_original_proofs_and_wrapper_in_each_Sol_39_records_standard_axioms",all(len(r)==13 and all(set(x["axioms"])<=STD for x in r) for r in proofs),{"original_proofs_per_Sol":12,"wrappers":3,"total_records":39})
check("reference_stubs_intentional_sorryAx_not_used_as_proofs",all("sorryAx" in t["reference_axioms"] for t in targets))
stage_paths=[BATCH/"staged"/plan["local_definition"]]+[BATCH/"staged"/t["local_solution"] for t in plan["targets"]]
check("complete_Def_and_Sols_no_sorry_admit_axiom_or_native_theorem_boundary",all(not any(s in p.read_text(encoding="utf-8") for s in ["sorry","admit","axiom "]) and not any(l.startswith(("import missions.","import Theorems.","import Solutions.")) for l in p.read_text(encoding="utf-8").splitlines()) for p in stage_paths))
fresh_graph=rows(OUT/"decl_graph.jsonl");old_graph=rows(BATCH/"decl_graph.jsonl")
def canonical_graph(g):
 d=dict(g)
 for k in ["typeDeps","valueDeps"]:d[k]=sorted(d[k])
 return d
check("fresh_actual_Stage1_full_graph_matches_frozen_18_records",sorted(map(canonical_graph,fresh_graph),key=lambda g:g["name"])==sorted(map(canonical_graph,old_graph),key=lambda g:g["name"]) and len(fresh_graph)==18 and not any(g["kind"]=="axiom" for g in fresh_graph))
facts=rows(OUT/"sketch_info.jsonl");old_facts=rows(BATCH/"CoefficientMapShiftDegree-sketch_info.jsonl")
header=rows(OUT/"header_info.jsonl")[0];source=(OUT/"source-oracle-input.lean").read_bytes()
check("fresh_actual_Stage2_15decl_57ref_28command_spans_match_original",facts==old_facts and source==(TASK/"formalization/CoefficientMapShiftDegree.lean").read_bytes() and {k:sum(f["kind"]==k for f in facts) for k in ["decl","ref","command"]}=={"decl":15,"ref":57,"command":28})
check("actual_fresh_header_matches_three_real_Mathlib_imports",header==aprov["header"] and source[:header["end"]["offset"]].decode().strip().splitlines()==["import "+m for m in ["Mathlib.Algebra.Polynomial.Taylor","Mathlib.Algebra.Polynomial.Reverse","Mathlib.Tactic"]])
byname={g["name"]:g for g in fresh_graph}
def declaration(n):
 g=byname[n];ds=[f for f in facts if f["kind"]=="decl" and f["declStart"]["line"]<=g["startLine"]<=f["declEnd"]["line"]]
 assert len(ds)==1 and ds[0]["valStart"] is not None;return ds[0]
def_facts=[declaration(n) for n in definitions]
first=min(f["declStart"]["offset"] for f in def_facts)
opens=[f for f in facts if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["offset"]<first]
rebuilt="import Mathlib.Algebra.Polynomial.Taylor\nimport Mathlib.Algebra.Polynomial.Reverse\n\nset_option autoImplicit false\nnoncomputable section\nnamespace "+NS+"\n\n"
rebuilt+="\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in opens)+"\n\n"
rebuilt+="\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in def_facts)+"\n\nend "+NS+"\n"
check("pure_three_Definitions_reconstructed_from_fresh_actual_parser_spans",rebuilt.encode()==(BATCH/"staged"/plan["local_definition"]).read_bytes() and sha(BATCH/"staged"/plan["local_definition"])=="edc9d4969159b80c6943c76f032115f70cfbef50ce03359236450dd830a0b8e9")
check("self_contained_actual_graph_no_parent_proof_or_existing_Def_boundaries",not plan["existing_definitions"] and not copy["required_existing_Definitions"] and not aprov["inline_helper_names"] and not aprov["new_external_theorem_boundaries"] and (BATCH/"actual-proof-bridge.lean.inc").read_bytes()==b"" and all(g["module"]=="missions.zeta9.formalization.CoefficientMapShiftDegree" for g in fresh_graph))
refs=[f for f in facts if f["kind"]=="ref"];diagnostics=[f for f in facts if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in def_facts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,header["end"]["offset"],b"")]
request=load(BATCH/"problems-request.json");drequest=load(BATCH/"definitions-request.json")[0];splice=[];statements=[]
expectedargs=["n H hH","n hn H hH hdeg","n hn H hdeg hsmall"]
for i,t in enumerate(plan["targets"]):
 full=t["theorem_name"];short=full.split(".")[-1];d=declaration(full);a,v=d["declStart"]["offset"],d["valStart"]["offset"]
 binding=[r for r in refs if r["const"]==full and a<=r["start"]["offset"]<v];assert len(binding)==1
 bs,be=binding[0]["start"]["offset"],binding[0]["end"]["offset"];sig=source[be:v].decode();renames=[]
 for r in refs:
  if r["const"]!=full:continue
  x,y=r["start"]["offset"],r["end"]["offset"]
  if any(ca<=x and y<=cb for ca,cb,_ in cuts):continue
  raw=source[x:y].decode();assert raw in [short,full];renames.append((x,y,("checked_"+short if raw==short else NS+".checked_"+short).encode()))
 pre="import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\nimport Mathlib.Algebra.Polynomial.Taylor\nimport Mathlib.Algebra.Polynomial.Reverse\nimport Mathlib.Tactic\n\n"
 sol=pre+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+"\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+short+" "+expectedargs[i]+"\n\n#print axioms solution\n"
 splice.append(sol.encode()==(BATCH/"staged"/t["local_solution"]).read_bytes())
 edits=[(bs-a,be-a,full.encode())]
 if d["docstring"]:
  dc_=d["docstring"];edits.append((dc_["start"]["offset"]-a,dc_["end"]["offset"]-a,b""))
 formal=edit(source[a:v],edits).decode().strip()+":= by sorry"
 preamble="import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n\nset_option autoImplicit false\nopen Polynomial\nopen ZetaNine "+NS+"\n"
 statements.append(request["problems"][i]["formal_statement"]==formal and request["problems"][i]["preamble"]==preamble and (preamble+"\n"+formal+"\n").encode()==(BATCH/"staged"/t["local_reference"]).read_bytes())
check("three_complete_Solution_splices_exact_all_12_math_proof_bodies_retained",all(splice) and len(diagnostics)==5,{"only_edits":"3 actual Def spans/header/5 diagnostics removed, own target actual binding/ref spans renamed, exact original signature wrapper appended","proof_body_substitutions":[]})
check("three_statement_reference_preambles_and_parser_signatures_exact",all(statements))
df={"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"};tf={"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("strict_offline_API_payload_fields_and_exact_staged_Def_source",set(drequest)==df and set(request)=={"env","private","problems"} and all(set(p)==tf and len(p["theorem_title"])<=200 for p in request["problems"]) and request["env"]==drequest["env"]==REV and request["private"] is False and drequest["private"] is False and drequest["definition"].encode()==(BATCH/"staged"/plan["local_definition"]).read_bytes(),{"API_called":False,"current_API_spec":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md v0.11.7"})
check("metadata_preserves_coefficient_nonzero_input_and_two_degree_domain_conditions",all(text in request["problems"][i]["natural_language_statement"] for i,text in [(0,"nonzero rational polynomial"),(0,"(7n-2-d)"),(0,"only $H\\ne0$"),(1,"$n\\ge1$"),(1,"\\le7n-3"),(1,"$n=1,H=X^5$"),(1,"=-1152"),(2,"\\operatorname{natdeg}H\\le7n-3"),(2,"\\operatorname{natdeg}D_n(H)\\le8")]))
native_boundary=rows(OUT/"native-author.log")+rows(OUT/"native-independent.log");nb={r["declaration"]:r for r in native_boundary}
check("fresh_native_author_22_and_prior_independent_17_boundaries_closed_standard_axioms",len(native_boundary)==39 and len(nb)==39 and all(set(r["axioms"])<=STD for r in native_boundary))
brows=rows(OUT/"stage-boundary-audit.log");exact=[r for r in brows if r["kind"]=="native_exact"];extra=[r for r in brows if r["kind"]=="new_independent_control"];bcmp=[]
for r in exact:
 n=r["declaration"].replace(".checked_actual_shift_difference_small_degree_implies_zero",".actual_shift_difference_small_degree_implies_zero");o=nb[n]
 bcmp.append({"declaration":r["declaration"],"type_exact":o["type"]==r["type"],"value_exact":o["definitionValue"]==r["definitionValue"],"axioms":r["axioms"]})
check("all_39_exact_native_boundaries_against_staged_solution_and_seven_new_controls",len(exact)==39 and len(extra)==7 and all(c["type_exact"] and c["value_exact"] and set(c["axioms"])<=STD for c in bcmp) and all(set(r["axioms"])<=STD for r in extra),{"closed_staged_boundary_records":46,"new_controls":[r["declaration"] for r in extra],"native_zero_constants_nonmonic_n0_n1_resonance_eval_and_degree_retained":True})
check("native_boundary_parser_splices_only_resolved_low_degree_refs",load(OUT/"boundary-provenance.json")["only_actual_parser_proof_spans_and_selected_refs_changed"] and all(not f["other_original_proof_edits"] for f in load(OUT/"boundary-provenance.json")["fixtures"].values()))
root_data=[]
for f in copy["files"]:
 stage=TASK/f["staged_task_relative"];root=ROOT/f["root_relative_destination"];fresh=PROJECT/f["root_relative_destination"]
 root_data.append({"root_relative":f["root_relative_destination"],"sha256":sha(root),"stage_root_fresh_equal":stage.read_bytes()==root.read_bytes()==fresh.read_bytes(),"frozen_hash_match":sha(stage)==f["sha256"]})
check("all_seven_root_staged_fresh_module_bytes_exact_fixed_copy_plan",len(root_data)==7 and all(r["stage_root_fresh_equal"] and r["frozen_hash_match"] for r in root_data) and copy["source_sha256"]==SOURCE_SHA and not copy["overwrite_allowed"],root_data)
install=load(BATCH/"root-install-receipt.json");build=(BATCH/"task-build.log").read_text(encoding="utf-8-sig");checklog=(BATCH/"task-check.log").read_text(encoding="utf-8-sig")
check("retained_supported_root_build_actual_zero_3796jobs_three_std3_outputs",(BATCH/"task-build-exit.txt").read_text(encoding="utf-8-sig").strip()=="0" and "Build completed successfully (3796 jobs)." in build and build.count("'solution' depends on axioms: [propext, Classical.choice, Quot.sound]")>=3 and install["frozen_author_audit_sha256"]==FIXED["author-audit.json"] and install["frozen_root_copy_plan_sha256"]==FIXED["root-copy-plan.json"] and install["root_bytes_match_frozen_stage"],{"root_build_is_retained_parent_evidence":True,"independent_replay_does_not_claim_rebuilding_whole_task":True})
check("task_check_exit_one_only_prior_other_mission_Tao_unassigned",(BATCH/"task-check-exit.txt").read_text(encoding="utf-8-sig").strip()=="1" and len(checklog.splitlines())==2 and all(l.startswith("ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_") for l in checklog.splitlines()),{"actual_workspace_check_exit":1,"ShiftDegree_new_unassigned_solution":False,"shared_scope_or_other_mission_not_written":True})

stable=author_members+[BATCH/n for n in FIXED]+[TASK/"formalization/CoefficientMapShiftDegree.lean",old_math_path]
stable+=[ROOT/f["root_relative_destination"] for f in copy["files"]]
stable+=[BATCH/n for n in ["root-install-receipt.json","task-build.log","task-build-exit.txt","task-check.log","task-check-exit.txt"]]
stable+=[p for p in OUT.iterdir() if p.is_file() and p.name not in ["independent-integration-review.json","independent-integration-review.md","independent-SHA256SUMS.txt"]]
stable+=list(PROJECT.glob("*.lean"))+[PROJECT/"lean-toolchain",PROJECT/"lake-manifest.json"]+objects
stable+=list((OUT/"retained-attempt-01-long-path").iterdir())
stable+=list((OUT/"retained-attempt-02-negative-normalization").iterdir())
stable+=[OUT/f["independent_relative"] for f in attempt["files"] if f["retained_copy"] is None]
stable+=[PROJECT/"missions/zeta9/formalization/CoefficientMapShiftDegree.lean"]
for sub in ["Definitions","Solutions","Theorems"]:stable+=list((PROJECT/sub).glob("*.lean"))
stable=list(dict.fromkeys(stable))
bindings=[{"task_relative":p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,"root_relative":p.relative_to(ROOT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)} for p in sorted(stable)]
findings=[{"severity":"informational","message":"Initial fresh project hit a Windows long-path object-write failure after the longest Solution printed standard axioms. Its actual exit1 and ten prior actual successes are retained and excluded from the final successful replay. The shorter p/b project rebuilt every native/staged object fresh; no namespace or theorem name changed."},{"severity":"informational","message":"Reference modules contain intentional sorryAx and only state the registered original theorem types. All complete staged proofs were freshly compiled separately with standard axioms."},{"severity":"informational","message":"The supported workspace check retains exit1 solely for two pre-existing Tao solutions outside this mission. ShiftDegree seven root sources match frozen staged bytes and its retained 3796-job task build is actual exit0."},{"severity":"scope","message":"This batch proves the actual rational polynomial shift obstruction. It does not import or establish a rational telescoper bridge, full coefficient-map inverse or zeta irrationality. Both original quotient degree and low operator degree hypotheses remain exact."}]
findings.insert(1,{"severity":"informational","message":"Two newly added negative-polynomial controls initially needed map_neg/neg_mul normalization after norm_num. The failed audit's actual exit1 and elaborator sorryAx placeholders are retained and excluded. Only these own controls were corrected;27 successful calls and8fresh compiled objects are hash-checked in the same p/b project before the final actual0/46-record audit."})
report={"schema_version":1,"review_role":"independent platform transplantation reviewer; not ShiftDegree platform author","verdict":"PASS","checked_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),"source_sha256":SOURCE_SHA,"author_controls":FIXED,"environment":{"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_rev":REV},"checks":checks,"targets":targets,"definition_comparisons":dc,"all_proof_records":proofs,"boundary_comparisons":bcmp,"new_independent_boundary_records":extra,"native_and_staged_objects_borrowed":False,"actual_native_source_freshly_rebuilt":True,"actual_exit_zero_Lean_calls":28,"fresh_project_compiled_objects":8,"stage_proof_records":39,"closed_native_boundary_records":39,"closed_stage_boundary_records":46,"required_existing_Definitions":[],"root_module_byte_bindings":root_data,"findings":findings,"retained_failures_excluded_from_PASS":[attempt,negative_attempt],"actual_polynomial_shift_closed":True,"rational_telescoper_relation_reviewed":False,"full_F_inverse_reviewed":False,"zeta_irrationality_claimed":False,"root_scope_API_credential_writes":False,"stable_files":bindings}
dump(OUT/"independent-integration-review.json",report)
write(OUT/"independent-integration-review.md","# Independent ShiftDegree platform review\n\nPASS: all frozen author controls and128members unchanged; actual self-contained source and seven staged modules compile in a new independent cache with no native/author proof-object reuse.28 final observed Lean exits are0 and8source/object receipts are bound. Initial Windows long-path object-write failure (actual1, ten earlier actual successes) is retained separately and excluded; new short p/b cache rebuilt all objects fresh, preserving theorem names.\n\nFresh Stage1=18records, Stage2=15decl/57refs/28commands and3-import header exactly match frozen original evidence. Three pure Definition spans and all12 proof bodies are mechanically reconstructed from these actual fresh parser facts. Three public original/Solution/reference types match exactly, including full Expr representation;3Defs in7contexts give21 exact full type/value comparisons.39 complete proof records use standard axioms. Reference stubs alone contain intentional sorryAx.\n\nNative author22 and prior independent17 boundaries are freshly recompiled, then39exact records plus7new controls are proved against the staged low-degree Solution. H0 degree/natDegree, rational negative nonmonic constants, n0 actual evaluation, n2 edge degree, n1X5 resonance coefficient15=0 and eval1=-1152 all retain their genuine meaning. A zero coefficient is not a zero operator; the quotient degree bound is preserved.\n\nSeven root sources equal frozen stage/fresh bytes. Parent-supported3796-job task build is retained actual0 with3standard-axiom Solution outputs. Saved check exit1 concerns only two prior Tao files outside this mission. No root/scope/API/credential writes. No rational telescoper relation, aggregate inverse or irrationality claim follows from this platform batch.\n")
write(OUT/"independent-SHA256SUMS.txt","".join(sha(p)+"  "+p.relative_to(ROOT).as_posix()+"\n" for p in sorted(stable+[OUT/"independent-integration-review.json",OUT/"independent-integration-review.md"])))
for row in bindings:assert sha(ROOT/row["root_relative"])==row["sha256"]
print(json.dumps({"verdict":"PASS","checks":len(checks),"stable_bindings":len(bindings),"actual_exit_zero_Lean_calls":28,"fresh_objects":8,"definition_comparisons":21,"stage_proof_records":39,"native_boundary_records":39,"stage_boundary_records":46,"report_sha256":sha(OUT/"independent-integration-review.json"),"SHA256SUMS_sha256":sha(OUT/"independent-SHA256SUMS.txt")},ensure_ascii=False),flush=True)
