"""Author offline source integration gate; separate independent review required."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/"project"
NS="ZetaNine.CoefficientMapAggregate";STD={"propext","Classical.choice","Quot.sound"}
MAPS={NS+"."+n for n in ["aggregateLinearMap","coordinateLinearMap","quarticAggregateLinearMap"]}
REV="0df444a360eaa60ab8c11dca51a86af692955474"
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(x) for x in p.read_text(encoding="utf-8-sig").splitlines() if x.startswith("{")]
def write(p,s):p.write_bytes(s if isinstance(s,bytes) else s.encode("utf-8"))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):
  assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
checks=[]
def check(name,okay,evidence=None):
 checks.append({"name":name,"pass":bool(okay),"evidence":evidence});assert okay,name

receipt=load(OUT/"compile-receipt.json");plan=load(OUT/"target-plan.json");prov=load(OUT/"integration-provenance.json")
source_hashes=receipt["source_sha256"]
check("eight_frozen_actual_native_sources_unchanged",len(source_hashes)==8 and all(sha(TASK/("formalization/"+n+".lean"))==h==sha(PROJECT/("missions/zeta9/formalization/"+n+".lean")) for n,h in source_hashes.items()),source_hashes)
math_review=TASK/"verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-review.json";math=load(math_review)
check("prior_independent_native_math_review_bound",sha(math_review)=="d2f50aa65f5dec147e632642c78cd27aaa7d8b7ba554067b389d5cc669002ddc" and math["verdict"]=="PASS" and len(math["checks"])==15,{"task_relative":math_review.relative_to(TASK).as_posix(),"sha256":sha(math_review),"distinct_from_platform_author_review":True})
check("fifty_observed_author_runs_all_actual_exit_zero",receipt.get("complete") is True and len(receipt["rows"])==50 and all(r["exit_code"]==0 and sha(OUT/r["log"])==r["log_sha256"] and (OUT/(r["label"]+"-exit.txt")).read_text().strip()=="0" for r in receipt["rows"]),{"observed_runs":50,"native_sources_plus_pure_Def":9,"official_graph_parser_header":11,"embedded_helper_type_oracle":1,"existing_and_new_staged_modules":15,"actual_type_helper_reports":11,"native_alias_value_compilation_and_report":2,"toolchain":1})
env=os.environ.copy();env.pop("LEAN_PATH",None)
p=subprocess.run(["git","-C",str(ROOT/".lake/packages/mathlib"),"rev-parse","HEAD"],capture_output=True,env=env)
write(OUT/"mathlib-revision.log",p.stdout+p.stderr)
check("actual_pinned_Lean_and_Mathlib",p.returncode==0 and p.stdout.decode().strip()==REV and "version 4.33.1" in (OUT/"toolchain.log").read_text(encoding="utf-8-sig"))
original={r["label"]:r for r in rows(OUT/"types_original.log")}
reports={context:{r["label"]:r for r in rows(OUT/(context+".log"))} for context in ["types_definition"]+[f"types_{i}_{k}" for i in range(3) for k in ["solution","reference"]]}
definitions=[r for r in original.values() if r["value"] is not None]
comparisons=[]
for d in definitions:
 for context,rs in reports.items():
  got=rs[d["label"]]
  comparisons.append({"declaration":d["declaration"],"context":context,"type_equal":got["type"]==d["type"],"literal_raw_value_equal":got["value"]==d["value"],"staged_definition_raw_value_equal":got["value"]==reports["types_definition"][d["label"]]["value"],"proof_fields_expected_raw_difference":d["declaration"] in MAPS and not d["declaration"].endswith(".quarticAggregateLinearMap"),"axioms":got["axioms"]})
ordinary=[r for r in comparisons if r["declaration"] not in MAPS];map_comps=[r for r in comparisons if r["declaration"] in MAPS]
check("all_49_actual_definition_types_exact_across_seven_contexts",len(definitions)==49 and len(comparisons)==343 and all(r["type_equal"] and set(r["axioms"])<=STD for r in comparisons),{"Base":9,"Jet":9,"Injectivity":7,"PF":5,"FS":4,"Reflection":4,"Summation":3,"Aggregate":6,"Harmonic":2,"type_comparisons":343})
check("46_ordinary_definition_raw_values_exact_322_comparisons",len(ordinary)==322 and all(r["literal_raw_value_equal"] for r in ordinary),{"ordinary_definition_count":46,"literal_value_comparisons":322})
check("actual_pretty_values_and_proof_elision_honestly_distinguished",len(map_comps)==21 and sum(not r["literal_raw_value_equal"] for r in map_comps)==7 and all(r["literal_raw_value_equal"] == (not r["declaration"].endswith(".coordinateLinearMap")) and r["staged_definition_raw_value_equal"] for r in map_comps),{"three_definition_names":sorted(MAPS),"coordinateLinearMap_pretty_raw_value_different":7,"aggregateLinearMap_pretty_raw_value_equal_with_elided_proof_fields":7,"quartic_composition_pretty_raw_value_equal":7,"all_contexts_match_exact_new_Def_pretty_value":True,"pp_proofs_in_original_type_reports":False,"reason":"Actual ppExpr pretty strings are retained verbatim. aggregateLinearMap's two changed proof fields print as elided dots, while coordinateLinearMap's proof constants change explicitly. Pretty-string equality is not full-expression equality. Full kernel equality and unelided Expr repr are checked in a separate native comparison report."})
details=load(OUT/"native-value-details-receipt.json")
check("supplementary_proof_visible_actual_value_report_preserves_main_evidence",details["actual_exit_code"]==0 and details["record_count"]==15 and details["pp_proofs_enabled"] and details["actual_Expr_repr_retained"] and sha(OUT/details["source"])==details["source_sha256"] and sha(OUT/details["log"])==details["log_sha256"] and sha(OUT/details["exit_file"])==details["exit_file_sha256"] and sha(OUT/"native-value-comparison.log")==details["prior_main_report_sha256"],details)
kernel=rows(OUT/"native-value-details.log");values=[r for r in kernel if r["kind"]=="kernel_definition_value"];proof_values=[r for r in kernel if r["kind"]=="rfl_or_data_equality"]
check("all_six_whole_native_definition_values_kernel_equal_and_nine_real_equality_proofs",len(values)==6 and len(proof_values)==9 and {r["declaration"] for r in values}=={NS+"."+n for n in ["aggregate","coordinatePolynomial","polynomialCoordinates","aggregateLinearMap","coordinateLinearMap","quarticAggregateLinearMap"]} and all(r["type_kernel_equal"] and r["full_value_kernel_equal"] and r["pp_proofs_enabled"] and r["original_expression_repr"] and r["comparison_expression_repr"] and set(r["axioms"])<=STD for r in values) and all(set(r["axioms"])<=STD for r in proof_values),{"alias_namespace":"ZetaNine.CoefficientMapAggregateValueComparison","whole_function_rfl_equalities":6,"additional_toFun_data_equalities":3,"Meta_isDefEq_values":6,"pp_proofs_true_and_full_Expr_repr_bound":True,"all_parent_43_definition_type_and_raw_values_exact":all(r["literal_raw_value_equal"] for r in ordinary if not r["declaration"].startswith(NS+".")),"comparison_is_not_just_sample_evaluations":True})
targets=[]
for i,t in enumerate(plan["targets"]):
 full=t["theorem_name"];o=original[full];s=reports[f"types_{i}_solution"][full];r=reports[f"types_{i}_reference"][full]
 targets.append({"theorem":full,"actual_original_type":o["type"],"original_solution_reference_type_equal":o["type"]==s["type"]==r["type"],"original_axioms":o["axioms"],"solution_axioms":s["axioms"],"reference_axioms":r["axioms"]})
check("three_original_Solution_reference_types_exact_no_extra_hypotheses",all(t["original_solution_reference_type_equal"] for t in targets) and all(not p["extra_hypotheses"] for p in prov["targets"].values()),targets)
check("three_native_and_complete_solution_endpoints_standard_three_axioms",all(set(t["original_axioms"])==STD and set(t["solution_axioms"])==STD for t in targets))
helpers=[rows(OUT/f"helpers_{i}.log") for i in range(3)];per=21+len(prov["inline_helper_names"])
check("all_twenty_original_proofs_required_parent_closure_and_wrappers_standard_axioms",all(len(rs)==per and all(set(r["axioms"])<=STD for r in rs) for rs in helpers),{"proofs_per_Sol":per,"total_proof_records":3*per,"original_Aggregate_proofs_per_Sol":20,"actual_parent_helper_count":len(prov["inline_helper_names"]),"inline_parent_names":prov["inline_helper_names"]})
check("reference_stubs_are_explicit_statement_only_sorryAx",all("sorryAx" in t["reference_axioms"] for t in targets))
stage_sources=[OUT/"staged"/plan["local_definition"]]+[OUT/"staged"/t["local_solution"] for t in plan["targets"]]
check("complete_Def_and_Solutions_no_sorry_admit_axiom_or_external_proof_boundary",not prov["new_external_theorem_boundaries"] and all(not any(tok in p.read_text(encoding="utf-8") for tok in ["sorry","admit","axiom "]) and not any(line.startswith(("import Theorems.","import Solutions.","import missions.")) for line in p.read_text(encoding="utf-8").splitlines()) for p in stage_sources))
check("actual_Aggregate_26_source_declarations_6_defs_20_proofs",prov["source_declarations"]==26 and prov["source_defs"]==6 and prov["source_proofs"]==20 and len(prov["definition_facts"])==6)
req=load(OUT/"problems-request.json");dreq=load(OUT/"definitions-request.json")[0]
dfields={"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"};tfields={"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("documented_v0117_offline_API_fields_only",set(dreq)<=dfields and set(req)=={"problems","env","private"} and req["env"]==dreq["env"]==REV and req["private"] is False and dreq["private"] is False and all(set(t)<=tfields and t["formal_statement"].endswith(":= by sorry") and len(t["theorem_title"])<=200 for t in req["problems"]),{"current_API_reference":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md","API_called":False})
check("definition_request_exact_staged_source",dreq["definition"].encode()==(OUT/"staged"/plan["local_definition"]).read_bytes())
check("genuine_five_output_domain_and_actual_even_strong_condition_prose",all(txt in req["problems"][i]["natural_language_statement"] for i,txt in [(0,"arbitrary rational polynomials"),(0,"$n=0$"),(1,"natural degree at most four"),(1,"zero polynomial"),(1,"nonmonic"),(2,"even natural"),(2,"2n+2"),(2,"$1\\le s\\le9$"),(2,"$\\rho_{0,1}=1$"),(2,"does not infer $W=0$")]) and "complete $(n+1)$-by-9" in dreq["natural_language_statement"])
check("eight_existing_Definition_dependencies_stage_project_root_exact",len(plan["existing_definitions"])==8 and all(sha(ROOT/d["root_relative"])==d["sha256"]==sha(TASK/d["task_relative"])==sha(PROJECT/d["root_relative"]) for d in plan["existing_definitions"]),plan["existing_definitions"])
check("exact_fixed_Summation_parent_Def",next(d["sha256"] for d in plan["existing_definitions"] if "Def_ZetaNine_CoefficientMapSummation" in d["root_relative"])=="469d4c0ba2f3849ad48c764f5e3a56c09f19a726c4ad9b9ba080ec69a853962c")
check("pure_Harmonic_raw_CRLF_and_actual_parser_LF_snapshot_distinct_exact",prov["pure_HarmonicStability_sha256"]=="5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92" and prov["pure_HarmonicStability_parser_decl_count"]==2 and sha(OUT/"HarmonicStability-oracle-input.lean")==prov["pure_HarmonicStability_parser_normalization"]["parser_normalized_sha256"] and (OUT/"HarmonicStability-oracle-input.lean").read_bytes()==(OUT/"dependencies/Definitions/Def_ZetaNine_HarmonicStability.lean").read_bytes().replace(b"\r\n",b"\n"))
old_counts={"coefficient-map":96,"coefficient-map-jet":111,"coefficient-map-injectivity":134,"coefficient-map-partial-fractions":174,"coefficient-map-reflection":172,"coefficient-map-finite-sum":220,"coefficient-map-summation":199};old_members=0
for slug,count in old_counts.items():
 old=TASK/"formalization/platform"/slug;ls=(old/"SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines();assert len(ls)==count
 for line in ls:
  h,rel=line.split("  ",1);assert sha(old/rel)==h;old_members+=1
check("all_1106_old_author_frozen_members_unchanged",old_members==1106,old_counts)
graph=rows(OUT/"decl_graph.jsonl");byname={g["name"]:g for g in graph};sources={n:(TASK/("formalization/"+n+".lean")).read_bytes() for n in source_hashes}
check("actual_cross8source_graph_no_axiom",len(graph)==prov["graph_records"] and len(graph)==246 and not any(g["kind"]=="axiom" for g in graph))
bridge=""
for module in list(source_hashes)[:-1]:
 hs=[h for h in prov["inline_helper_facts"] if h["module"]==module]
 if not hs:continue
 bridge+="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
 os_=[r["fact"] for r in prov["bridge_open_context_facts"] if r["module"]==module]
 for f in os_:bridge+=sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\n"
 if os_:bridge+="\n"
 for h in hs:
  f=h["fact"];bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n"
 bridge+="end ZetaNine."+module+"\n\n"
check("actual_parent_proof_and_namespace_open_spans_exact",bridge.encode()==(OUT/"actual-proof-bridge.lean.inc").read_bytes() and digest(bridge.encode())==prov["bridge_sha256"])
source=sources["CoefficientMapAggregate"];fs=rows(OUT/"CoefficientMapAggregate-sketch_info.jsonl");refs=[f for f in fs if f["kind"]=="ref"]
check("actual_Aggregate_parser_snapshot_selected",{k:sum(f["kind"]==k for f in fs) for k in ["decl","ref","command"]}==prov["source_fact_counts"] and prov["source_fact_counts"]["decl"]==26,"CoefficientMapAggregate-sketch_info.jsonl")
he=prov["header"]["end"]["offset"];mathlib=["Mathlib.Algebra.Polynomial.Eval.SMul","Mathlib.Algebra.Polynomial.BigOperators"]
check("actual_leaf_header_exact_three_real_imports",source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapSummation"]+["import "+m for m in mathlib])
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in prov["definition_facts"]]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in prov["deleted_diagnostic_facts"]]+[(0,he,b"")]
opens="open ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability\n"
stage_replays=[];reference_replays=[]
for i,t in enumerate(plan["targets"]):
 full=t["theorem_name"];name=full.split(".")[-1];pr=prov["targets"][full];changes=[]
 for r in refs:
  if r["const"]!=full:continue
  a,z=r["start"]["offset"],r["end"]["offset"]
  if any(x<=a and z<=y for x,y,_ in cuts):continue
  old=source[a:z].decode();assert old in [name,full]
  changes.append((a,z,("checked_"+name if old==name else NS+".checked_"+name).encode()))
 prefix="import Definitions.Def_ZetaNine_CoefficientMapAggregate\nimport Mathlib.Tactic\n"+"\n".join("import "+m for m in mathlib)+"\n\n"+bridge
 rebuilt=prefix+"\n"+edit(source,cuts+changes).decode()+"\n\n"+opens+"\ntheorem solution"+pr["original_signature"]+":= by\n  exact "+NS+".checked_"+name+" "+t["wrapper_arguments"]+"\n\n#print axioms solution\n"
 stage_replays.append(rebuilt.encode()==(OUT/"staged"/t["local_solution"]).read_bytes())
 d=pr["declaration_fact"];a,v=d["declStart"]["offset"],d["valStart"]["offset"];binding=pr["binding_fact"];bs,be=binding["start"]["offset"],binding["end"]["offset"]
 es=[(bs-a,be-a,full.encode())]
 if d["docstring"]:
  dc=d["docstring"];es.append((dc["start"]["offset"]-a,dc["end"]["offset"]-a,b""))
 formal=edit(source[a:v],es).decode().strip()+":= by sorry"
 reference_replays.append(req["problems"][i]["formal_statement"]==formal and (req["problems"][i]["preamble"]+"\n"+formal+"\n").encode()==(OUT/"staged"/t["local_reference"]).read_bytes())
check("all_twenty_original_proofs_complete_parser_splices_and_exact_wrappers",all(stage_replays) and len(prov["deleted_diagnostic_facts"])==6,{"moved_defs":6,"original_proofs_retained":20,"deleted_diagnostics":6,"extra_hypotheses":[]})
check("all_three_reference_signatures_and_request_statements_original_parser_exact",all(reference_replays))
fields=load(OUT/"embedded-field-provenance.json");type_rows={r["declaration"]:r for r in rows(OUT/"embedded-types.log")}
check("ten_actual_constructor_helpers_original_typed_proofs_no_global_assumption",fields["field_count"]==4 and len(fields["actual_original_helpers"])==10 and not fields["new_global_helper_theorems"] and fields["ordinary_data_defs_unchanged"]==3 and fields["data_value_kernel_comparison_pending"] is False and fields["actual_value_comparison_log_sha256"]==sha(OUT/"native-value-comparison.log") and set(type_rows)==set(fields["actual_original_helpers"]) and all(set(r["axioms"])<=STD for r in type_rows.values()))
def defprefix(namespace,native=False):
 parent="missions.zeta9.formalization.CoefficientMapAggregate" if native else "Definitions.Def_ZetaNine_CoefficientMapSummation"
 text="\n".join("import "+m for m in [parent]+mathlib+["Mathlib.Tactic.FinCases","Mathlib.Tactic.Ring"])
 text+="\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+namespace+"\n\n"
 text+="\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in prov["definition_open_context_facts"])
 return text+"\n\n"
defnames=["aggregate","coordinatePolynomial","polynomialCoordinates","aggregateLinearMap","coordinateLinearMap","quarticAggregateLinearMap"]
def rebuild_def(namespace,alias=False):
 spans=[]
 for name,d in zip(defnames,prov["definition_facts"]):
  a,z=d["declStart"]["offset"],d["declEnd"]["offset"];es=[]
  for field in fields["fields"]:
   if field["definition"]!=NS+"."+name:continue
   assert field["data_fields_edited"] is False
   r=field["reference_fact"];x,y=r["start"]["offset"],r["end"]["offset"];assert a<=x<y<=z and r in refs
   assert source[x:y].decode()==field["actual_proof_callee"].split(".")[-1]
   chunks=[]
   for h in field["helper_facts"]:
    f=h["declaration_fact"];ha,hz=f["declStart"]["offset"],f["declEnd"]["offset"];p=h["binding_fact"]["start"]["offset"]
    assert source[ha:p].decode().strip()=="theorem" and h["only_prefix_change"]=={"start":ha,"end":p,"replacement":"have "}
    chunks.append("\n".join("    "+line for line in edit(source[ha:hz],[(0,p-ha,b"have ")]).decode().splitlines()))
   full=field["actual_proof_callee"];typ=type_rows[full]["alias_type" if alias else "original_type"]
   term="((by\n"+"\n".join(chunks)+"\n    exact "+full.split(".")[-1]+") :\n    ("+typ.replace("\n","\n    ")+"))"
   if not alias:assert term==field["replacement_proof_term"]
   es.append((x-a,y-a,term.encode()))
  spans.append(edit(source[a:z],es).decode())
 return defprefix(namespace,alias)+"\n\n".join(spans)+"\n\nend "+namespace+"\n"
check("six_actual_Def_spans_only_four_true_proof_refs_changed_data_untouched",rebuild_def(NS).encode()==(OUT/"staged"/plan["local_definition"]).read_bytes() and len(fields["fields"])==4,{"embedded_global_lemmas":0,"genuine_local_helpers":10,"actual_edited_reference_count":4,"all_data_fields_edited":False,"current_rule":"v0.11.7 contribute definition module helpers necessary for construction; constructor Prop fields are closed genuine proofs","historical_mechanical_playbook":"references/upload_full_project.md Phase2 only; not current API authority"})
alias="ZetaNine.CoefficientMapAggregateValueComparison"
check("native_value_alias_exact_same_generated_six_Def_proof_fields",rebuild_def(alias,True).encode()==(OUT/"native-value-comparison-definition.lean").read_bytes()==(PROJECT/"NativeValueComparisonDefinition.lean").read_bytes(),{"only_native_comparison_changes":"actual native import and new namespace; helper type expression namespace semantically remapped by real Lean Expr.const oracle","proof_irrelevance_justification":"Only constructor Prop proof fields differ; native whole-value rfl/Meta comparisons succeeded."})
boundary=load(OUT/"stage-boundary-report.json");br=load(OUT/"boundary-compile-receipt.json")
native_rs=load(TASK/"verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-original-types.json")+load(TASK/"verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-boundary-types.json")
native={r["declaration"]:r for r in native_rs};bcomp=[]
for r in boundary["records"]:
 n=r["declaration"].replace(".checked_aggregate_zero_all_rho",".aggregate_zero_all_rho");o=native[n]
 bcomp.append({"declaration":r["declaration"],"native_type_exact":r["type"]==o["type"],"native_literal_raw_value_exact":r["definitionValue"]==o["definitionValue"],"proof_field_value_kernel_equality":n in MAPS,"axioms":r["axioms"]})
check("54_original_closed_coordinate_kernel_boundaries_actual_staged_compile",boundary["exit_code"]==0 and len(bcomp)==54 and len(br["rows"])==3 and br["complete"] is True and all(r["exit_code"]==0 and sha(OUT/r["log"])==r["log_sha256"] and sha(OUT/r["exit_file"])==r["exit_file_sha256"] for r in br["rows"]) and all(r["native_type_exact"] and (r["native_literal_raw_value_exact"] or r["proof_field_value_kernel_equality"]) and set(r["axioms"])<=STD for r in bcomp),{"original_author_records":32,"prior_independent_records":22,"n0_X4_actual_F_zero_W_nonzero_rho1_one_notStrong_divergent":True,"zero_nonmonic_quartic_roundtrips":True,"HasSum_boundaries_have_original_Even_and_Strong":True})
bp=load(OUT/"stage-boundary-provenance.json")
check("additional_HasSum_parent_proofs_are_real_audit_only_not_public_endpoint_assumptions",bp["extra_helpers_not_in_seven_platform_staged_files"] and all(set(r["axioms"])<=STD for r in boundary["extra_helper_records"]) and len(boundary["extra_helper_records"])==len(bp["extra_helper_names"]),{"extra_helpers":bp["extra_helper_names"],"public_endpoint_scope_unchanged":True})
normalization_failure=load(OUT/"retained-boundary-parser-normalization-failure.json")
resume=load(OUT/"boundary-same-fresh-project-parser-resume.json")
check("retained_Python_CRLF_boundary_gate_failure_excluded_same_project_actual_parser_resume",normalization_failure["observed_python_driver_exit_code"]==1 and normalization_failure["not_a_Lean_failure"] is True and normalization_failure["actual_author_parser_exit_code"]==0 and normalization_failure["failure_used_for_final_PASS"] is False and br["same_fresh_project_actual_author_parser_reused"] is True and br["resume_snapshot_sha256"]==sha(OUT/"boundary-same-fresh-project-parser-resume.json")==normalization_failure["same_fresh_project_resume_snapshot_sha256"] and all(sha(OUT/f["batch_relative"])==f["sha256"] for f in resume["files"]),normalization_failure)
check("fresh_project_no_actual_source_or_staged_objects_borrowed",receipt["native_and_staged_objects_borrowed"] is False and load(OUT/"preparation-state.json")["native_or_staged_objects_borrowed"] is False,{"native_8_plus_pure_Def_fresh":True,"only_shared_Mathlib_package_cache":True,"same_driver_serial":True})

field_plan_path=OUT/"definition-proof-field-plan.json"
initial_plan_path=OUT/"definition-proof-field-plan.before-actual-results.json"
if not initial_plan_path.exists():write(initial_plan_path,field_plan_path.read_bytes())
field_plan=load(field_plan_path)
field_plan["state"]="ACTUALLY_VERIFIED_CONSTRUCTOR_PROOFS_AND_WHOLE_VALUES"
field_plan["historical_initial_expectation_snapshot"]=initial_plan_path.name
field_plan["raw_value_equality"]="46 ordinary actual pretty values are literal equal across7contexts (322). Actual map pretty values: coordinateLinearMap differs (7), aggregateLinearMap prints changed proof fields as omitted dots and compares equal (7), quartic composition compares equal (7). These pretty equalities are not full Expr equality; actual unelided Expr repr is retained in native-value-details.log."
field_plan["actual_Lean_evidence_pending"]=False
field_plan["actual_type_comparisons"]=343
field_plan["actual_whole_native_definition_kernel_equal_count"]=6
field_plan["actual_whole_native_rfl_proofs"]=6
field_plan["actual_data_field_rfl_proofs"]=3
field_plan["kernel_comparison_scope"]="Native six definitions in main report and repeated proof-visible supplementary report; seven contexts propagate the same canonical staged Definition values. No claim of21 direct native kernel comparisons."
dump(field_plan_path,field_plan)

copyfiles=[]
for rel in [plan["local_definition"]]+[t[k] for t in plan["targets"] for k in ["local_solution","local_reference"]]:
 src=OUT/"staged"/rel;dest=ROOT/rel
 copyfiles.append({"staged_task_relative":src.relative_to(TASK).as_posix(),"root_relative_destination":rel,"bytes":src.stat().st_size,"sha256":sha(src),"destination_exists_at_author_freeze":dest.exists()})
 if dest.exists():assert sha(dest)==sha(src),"Parent must resolve differing existing root without overwrite."
dump(OUT/"root-copy-plan.json",{"source_sha256":source_hashes["CoefficientMapAggregate"],"sources_sha256":source_hashes,"required_existing_Definitions":plan["existing_definitions"],"author_scope":"task-local offline only; parent installs and builds","overwrite_allowed":False,"files":copyfiles,"scope_build_entrypoints_for_parent":[t["local_solution"].removesuffix(".lean").replace("/",".") for t in plan["targets"]]})
dump(OUT/"decl-plan.json",{"selected_public_endpoints":[t["theorem_name"] for t in plan["targets"]],"actual_graph_records":246,"source_declarations":26,"genuine_Definitions":6,"original_proofs":20,"core_closure":prov["cross_module_core_closure"],"inline_helpers":prov["inline_helper_names"],"generated_records":prov["generated_records"],"constructor_proof_fields":fields,"new_external_theorem_boundaries":[]})
limitations=["Actual F has five rational outputs (B,rho3,rho5,rho7,rho9), not the complete individual local coefficient array. Addition holds for all n and all rational polynomials. Quartic coordinate restoration retains natDegree<=4.","The all-nine totals endpoint retains Even n, actual StrongProperMultiplier and actual aggregate zero. It proves coefficient totals vanish and does not conclude W=0 or invert F.","The three linear maps have genuine proof fields, directly in two constructors and through their composition in the third. Four actual proof references are replaced by closed original local helper proofs; all data fields and first three data definitions are unchanged. Actual pretty values differ for coordinateLinearMap (7comparisons), while aggregateLinearMap prints changed proof fields as omitted dots (7comparisons) and quartic composition pretty value is unchanged (7comparisons). Pretty equality is not full expression equality. Whole-value kernel equality and rfl/data equalities pass for all six definitions.","n0X4 gives genuine F0, W nonzero, rho1=1, proper but not strongly proper, with the harmonic divergent series. Strict proper alone cannot support the nine-total conclusion or convergence.","Additional genuine Summation helpers are copied only for boundary replay audits, with original Even/Strong conditions. Public staged source contains only the actual required Aggregate proof closure, no theorem assumptions.","This author PASS is offline source integration only. Independent transplantation review, supported root build and platform acceptance remain separate parent operations. No root/scope/API/credential writes; references deliberately use sorryAx."]
write(OUT/"README.md","# Actual five rational aggregate offline author batch\n\nThree original endpoints: aggregate_add, polynomial_restore, aggregate_zero_all_rho. F=(B,rho3,rho5,rho7,rho9) is actual finite negative harmonic and weighted local coefficient data. No individual coefficient array, kernel triviality, inverse or irrationality claim. The all-nine-total endpoint keeps Even and actual StrongProperMultiplier.\n\nFresh native eight-source plus unchanged HarmonicStability compilation, official Stage1/Stage2/header, exact original types, all20 original proofs and genuine parent helper closure. Seven staged root modules require eight fixed existing Definitions. Constructor proof fields are locally closed from10 real helpers at four actual reference spans. No new global lemma or boundary assumption in Definition.\n\n49 actual definition types compare across7contexts (343).46 ordinary values compare literally (322). Actual pretty values differ for coordinateLinearMap (7); aggregateLinearMap elides changed proof fields as dots (7), and the third composition keeps its pretty value (7). These pretty equalities are not treated as full expression equality. All staged contexts match the new Definition. Native comparison enables pp.proofs and also records unelided Expr repr. A native comparison namespace uses the exact same six generated definitions with genuine native dependencies. Six whole-function rfl equalities, six actual Meta.isDefEq value comparisons and three additional data equalities confirm kernel equality. No sample-only equality shortcut.\n\n54 exact native coordinate and boundary records recompile against staged Solution, including n0X4 actual F0/Wnonzero/rho1=1/proper/notStrong/divergent and genuine zero/nonmonic quartic roundtrips. Real additional HasSum helper proofs live in audit-only code. Public endpoints retain exact hypotheses. Original20 proofs remain in each Solution; local constructor proofs never replace them.\n\nAll proof evidence has only standard axioms. References contain intentional sorryAx and are not proofs. Actual compiled objects, sources, logs and observed exits are hash-bound; only shared Mathlib package cache is reused. Previous1106 frozen author members remain unchanged. This is an author gate; independent platform review and root/platform actions remain separate.\n")
objects=[]
for r in receipt["rows"]:
 ex=OUT/(r["label"]+"-exit.txt");r["exit_file"]=ex.name;r["exit_file_sha256"]=sha(ex)
 if r["command"][:3]==["lake","--no-cache","build"]:
  module=r["command"][3];obj=PROJECT/".lake/build/lib/lean"/(module.replace(".","/")+".olean");src=PROJECT/(module.replace(".","/")+".lean")
 elif r["label"]=="build-native-value-alias":
  obj=PROJECT/".lake/build/lib/lean/NativeValueComparisonDefinition.olean";src=PROJECT/"NativeValueComparisonDefinition.lean"
 else:continue
 assert obj.exists() and src.exists()
 r["compiled_object_project_relative"]=obj.relative_to(PROJECT).as_posix();r["compiled_object_sha256"]=sha(obj)
 r["compiled_source_project_relative"]=src.relative_to(PROJECT).as_posix();r["compiled_source_sha256"]=sha(src);objects.append(obj)
receipt["observed_exit_files_and_compiled_objects_bound"]=True;dump(OUT/"compile-receipt.json",receipt)
stable=[p for p in OUT.iterdir() if p.is_file() and p.name not in ["author-audit.json","source-manifest.json","SHA256SUMS.txt"]]
stable+=list((OUT/"staged").rglob("*.lean"))+list((OUT/"dependencies").rglob("*.lean"))+list(dict.fromkeys(objects))
stable+=list(PROJECT.glob("*.lean"))+[PROJECT/"lake-manifest.json",PROJECT/"lean-toolchain"]
stable+=[PROJECT/("missions/zeta9/formalization/"+n+".lean") for n in source_hashes]
for d in ["Definitions","Solutions","Theorems"]:stable+=list((PROJECT/d).glob("*.lean"))
stable=list(dict.fromkeys(stable));assert len(set(objects))==24
manifest={"schema_version":1,"sources_sha256":source_hashes,"files":[{"task_relative":p.relative_to(TASK).as_posix(),"batch_relative":p.relative_to(OUT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)} for p in sorted(stable)],"required_existing_Definitions":plan["existing_definitions"],"prior_independent_native_review_sha256":sha(math_review),"old_batches_modified":False,"actual_compiled_unique_objects":24}
dump(OUT/"source-manifest.json",manifest)
audit={"schema_version":1,"review_role":"author offline integration gate; independent transplantation review remains required","verdict":"PASS","source_sha256":source_hashes["CoefficientMapAggregate"],"sources_sha256":source_hashes,"mathlib_rev":REV,"lean_toolchain":"leanprover/lean4:v4.33.1","checks":checks,"targets":targets,"definition_comparisons":comparisons,"raw_map_value_equality":False,"native_kernel_value_comparison_records":kernel,"constructor_field_provenance":fields,"all_proof_records":helpers,"boundary_comparisons":bcomp,"actual_cross_module_helpers":prov["inline_helper_names"],"limitations":limitations,"stable_files":manifest["files"],"platform_published":False,"platform_accepted":False,"root_installed_by_author":False,"independent_transplantation_review_claimed":False,"root_scope_API_credential_writes":False}
dump(OUT/"author-audit.json",audit)
freeze=stable+[OUT/"source-manifest.json",OUT/"author-audit.json"]
write(OUT/"SHA256SUMS.txt","".join(sha(p)+"  "+p.relative_to(OUT).as_posix()+"\n" for p in sorted(freeze)))
for line in (OUT/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
 h,rel=line.split("  ",1);assert sha(OUT/rel)==h
print(json.dumps({"author_verdict":"PASS","checks":len(checks),"source_fact_counts":prov["source_fact_counts"],"graph_records":246,"proof_records":3*per,"inline_helpers":len(prov["inline_helper_names"]),"definition_type_comparisons":343,"ordinary_raw_value_comparisons":322,"unchanged_quartic_composition_pretty_values":7,"different_coordinate_map_pretty_values":7,"actual_boundary_records":54,"actual_unique_compiled_objects":24,"frozen_files":len(freeze),"author_sha256":sha(OUT/"author-audit.json"),"copyplan_sha256":sha(OUT/"root-copy-plan.json"),"manifest_sha256":sha(OUT/"source-manifest.json"),"SHA256SUMS_sha256":sha(OUT/"SHA256SUMS.txt")},ensure_ascii=False),flush=True)
