"""Author-only offline gate; independent transplantation review remains separate."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT / "project"
NS="ZetaNine.CoefficientMapReflection";STD={"propext","Classical.choice","Quot.sound"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,s):p.write_text(s,encoding="utf-8",newline="\n")
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
checks=[]
def check(name,okay,evidence=None):
    checks.append({"name":name,"pass":bool(okay),"evidence":evidence});assert okay,name
receipt=load(OUT / "compile-receipt.json");plan=load(OUT / "target-plan.json");prov=load(OUT / "integration-provenance.json")
check("five_frozen_actual_sources_unchanged",all(sha(TASK / ("formalization/"+n+".lean"))==h for n,h in receipt["source_sha256"].items()),receipt["source_sha256"])
math_review=TASK / "verification/formalization-coefficient-map-reflection-2026-10-03/independent-review.json"
math=load(math_review)
check("prior_independent_native_math_review_bound",sha(math_review)=="ac3d8f135cb3c69b39074548bea712f418fa6d0273ad27e33805374c1db20123" and math["verdict"]=="PASS" and len(math["checks"])==17,{"task_relative":math_review.relative_to(TASK).as_posix(),"sha256":sha(math_review),"is_independent_transplantation_review":False})
check("all_thirty_one_actual_author_runs_exit_zero",receipt.get("complete") is True and len(receipt["rows"])==31 and all(r["exit_code"]==0 and sha(OUT / r["log"])==r["log_sha256"] for r in receipt["rows"]),{"runs":len(receipt["rows"]),"native_source_compilation":1,"official_graph_and_parser_and_header_runs":7,"staged_source_builds_including_actual_existing_Definitions":11,"actual_import_reports":11,"toolchain_probe":1})
env=os.environ.copy();env.pop("LEAN_PATH",None)
p=subprocess.run(["git","-C",str(ROOT / ".lake/packages/mathlib"),"rev-parse","HEAD"],capture_output=True,env=env)
write(OUT / "mathlib-revision.log",(p.stdout+p.stderr).decode("utf-8-sig"))
check("actual_pinned_Lean_Mathlib_environment","version 4.33.1" in (OUT / "toolchain.log").read_text(encoding="utf-8-sig") and p.returncode==0 and p.stdout.decode().strip()=="0df444a360eaa60ab8c11dca51a86af692955474")
original={r["label"]:r for r in rows(OUT / "types_original.log")}
contexts=["types_definition"]+[f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]
reports={label:{r["label"]:r for r in rows(OUT / (label+".log"))} for label in contexts}
definitions=[r for r in original.values() if r["value"] is not None]
comparisons=[]
for d in definitions:
    for context,r in reports.items():
        got=r[d["label"]]
        comparisons.append({"declaration":d["declaration"],"context":context,"type_equal":got["type"]==d["type"],"value_equal":got["value"]==d["value"],"axioms":got["axioms"]})
check("all_thirty_four_actual_definition_types_and_values_equal",len(definitions)==34 and len(comparisons)==238 and all(r["type_equal"] and r["value_equal"] and set(r["axioms"])<=STD for r in comparisons),{"Base":9,"Jet":9,"Injectivity":7,"PartialFractions":5,"Reflection":4,"exact_actual_comparisons":238})
targets=[]
for i,t in enumerate(plan["targets"]):
    full=t["theorem_name"];orig=original[full];sol=reports[f"types_{i}_solution"][full];ref=reports[f"types_{i}_reference"][full]
    targets.append({"theorem":full,"actual_original_type":orig["type"],"original_solution_reference_type_equal":orig["type"]==sol["type"]==ref["type"],"original_axioms":orig["axioms"],"solution_axioms":sol["axioms"],"reference_axioms":ref["axioms"]})
check("three_original_Solution_reference_types_exact_no_extra_hypotheses",all(t["original_solution_reference_type_equal"] for t in targets),targets)
check("complete_solution_endpoints_exact_standard_three_axioms",all(set(t["solution_axioms"])==STD and set(t["original_axioms"])==STD for t in targets),sorted(STD))
helpers=[rows(OUT / f"helpers_{i}.log") for i in range(3)]
per=31+len(prov["inline_helper_names"])
check("all_original_thirty_proofs_cross_module_closure_and_wrapper_standard_axioms",all(len(rs)==per and all(set(r["axioms"])<=STD for r in rs) for rs in helpers),{"proofs_per_solution":per,"total_proof_records":3*per,"cross_module_inline_names":prov["inline_helper_names"]})
check("no_external_Theorems_Solutions_or_native_proof_boundary",not prov["new_external_theorem_boundaries"] and all(not any(line.startswith(("import Theorems.","import Solutions.","import missions.")) for line in (OUT / "staged" / t["local_solution"]).read_text(encoding="utf-8").splitlines()) for t in plan["targets"]))
check("reference_stubs_explicitly_not_proofs",all("sorryAx" in t["reference_axioms"] for t in targets))
check("actual_source_core_and_Def_lightweight",prov["source_declarations"]==34 and prov["source_defs"]==4 and prov["source_proofs"]==30 and len(prov["definition_facts"])==4)
req=load(OUT / "problems-request.json");dreq=load(OUT / "definitions-request.json")[0]
dfields={"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"};tfields={"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("documented_offline_API_fields_only",set(dreq)<=dfields and set(req)=={"problems","env","private"} and all(set(t)<=tfields and t["formal_statement"].endswith(":= by sorry") and len(t["theorem_title"])<=200 for t in req["problems"]),{"schema_reference":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md","API_called":False})
check("definition_request_exact_staged_source",dreq["definition"].encode()==(OUT / "staged" / plan["local_definition"]).read_bytes())
check("Even_n_and_strong_bound_and_both_boundary_prose_faithful",all(text in req["problems"][i]["natural_language_statement"] for i,text in [(0,"$n$ is even"),(1,"$s$ even"),(1,"simple-pole total is one"),(2,"does not require Even n"),(2,"$n=1$"),(2,"proper but not StrongProper")]))
check("native_independent_exact_domains_and_open_limits_bound",math["actual_local_coefficient_reflection_closed"] is True and math["actual_even_rho_cancellation_closed"] is True and math["actual_rho_one_cancellation_under_stronger_bound_closed"] is True and math["rho1_zero_from_strict_proper_alone_closed"] is False and math["original_aggregate_F_injectivity_closed"] is False and math["original_aggregate_F_inverse_closed"] is False and math["infinite_sum_Eq4_closed"] is False and math["exact_L_closed"] is False)
check("four_actual_dependency_Def_stage_root_bytes_identical",len(plan["existing_definitions"])==4 and all(sha(ROOT / d["root_relative"])==d["sha256"]==sha(TASK / d["task_relative"])==sha(PROJECT / d["root_relative"]) for d in plan["existing_definitions"]),plan["existing_definitions"])

old_members=0
for name in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions"]:
    old=TASK / "formalization/platform" / name
    for line in (old / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
        h,rel=line.split("  ",1);assert sha(old / rel)==h;old_members+=1
check("all_515_old_author_frozen_members_unchanged",old_members==515,{"Base_frozen_members":96,"Jet_frozen_members":111,"Injectivity_frozen_members":134,"PartialFractions_frozen_members":174,"old_batches_written_by_author":False})
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
sources={n:(TASK / ("formalization/"+n+".lean")).read_bytes() for n in receipt["source_sha256"]}
check("real_graph_no_axiom_declaration_or_external_boundary",len(graph)==prov["graph_records"] and not any(g["kind"]=="axiom" for g in graph) and not prov["new_external_theorem_boundaries"])
bridge=""
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions"]:
    helpers=[f for f in prov["inline_helper_facts"] if f["module"]==module]
    if not helpers:continue
    bridge+="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
    opens=[r["fact"] for r in prov["bridge_open_context_facts"] if r["module"]==module]
    for f in opens:bridge+=sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\n"
    if opens:bridge+="\n"
    for h in helpers:
        f=h["fact"];bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n"
    bridge+="end ZetaNine."+module+"\n\n"
check("actual_cross_source_proof_spans_exact",bridge.encode()==(OUT / "actual-proof-bridge.lean.inc").read_bytes() and hashlib.sha256(bridge.encode()).hexdigest()==prov["bridge_sha256"])
source=sources["CoefficientMapReflection"];header_end=prov["header"]["end"]["offset"]
facts=rows(OUT / "CoefficientMapReflection-sketch_info.jsonl")
check("exact_Reflection_parser_snapshot_selected",{kind:sum(f["kind"]==kind for f in facts) for kind in ["decl","ref","command"]}==prov["source_fact_counts"]=={"decl":34,"ref":178,"command":56},"CoefficientMapReflection-sketch_info.jsonl")
refs=[f for f in facts if f["kind"]=="ref"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in prov["definition_facts"]]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in prov["deleted_diagnostic_facts"]]+[(0,header_end,b"")]
def edit(data,edits):
    edge=len(data)
    for a,b,v in sorted(set(edits),reverse=True):
        assert 0<=a<=b<=edge
        data=data[:a]+v+data[b:];edge=a
    return data
stage_replays=[]
for t in plan["targets"]:
    full=t["theorem_name"];name=full.split(".")[-1];pr=prov["targets"][full];changes=[]
    for r in refs:
        if r["const"]!=full:continue
        a,b=r["start"]["offset"],r["end"]["offset"]
        if any(x<=a and b<=y for x,y,_ in cuts):continue
        old=source[a:b].decode();assert old in [name,full]
        changes.append((a,b,("checked_"+name if old==name else NS+".checked_"+name).encode()))
    prefix="import Definitions.Def_ZetaNine_CoefficientMapReflection\nimport Mathlib.Tactic\n\n\n"+bridge
    reconstructed=prefix+"\n"+edit(source,cuts+changes).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\n\ntheorem solution"+pr["original_signature"]+":= by\n  exact "+NS+".checked_"+name+" "+t["wrapper_arguments"]+"\n\n#print axioms solution\n"
    stage_replays.append(reconstructed.encode()==(OUT / "staged" / t["local_solution"]).read_bytes())
check("complete_original_Reflection_proof_core_and_all_three_parser_splices_exact",all(stage_replays) and len(prov["definition_facts"])==4 and len(prov["deleted_diagnostic_facts"])==11,{"original_proofs_retained_per_Sol":30,"new_hypotheses":[]})
boundary=load(OUT / "stage-boundary-report.json")
native_boundary=load(TASK / "verification/formalization-coefficient-map-reflection-2026-10-03/independent-boundary-types.json")
native_byname={r["declaration"]:r for r in native_boundary}
boundary_comparisons=[]
for r in boundary["records"]:
    name=r["declaration"].replace(".checked_rho_one_zero_of_strong_proper",".rho_one_zero_of_strong_proper")
    orig=native_byname[name]
    boundary_comparisons.append({"declaration":r["declaration"],"native_type_exact":orig["type"]==r["type"],"native_definition_value_exact":orig["definitionValue"]==r["definitionValue"],"axioms":r["axioms"]})
check("actual_staged_n_zero_simple_pole_and_odd_n_boundaries_recompiled",boundary["exit_code"]==0 and (OUT / "stage-boundary-audit-exit.txt").read_text().strip()=="0" and len(boundary_comparisons)==59 and boundary["all_standard_axioms"] and all(r["native_type_exact"] and r["native_definition_value_exact"] for r in boundary_comparisons),{"records":59,"source_records":34,"exact_original_boundary_checks":25,"all_axioms":sorted(STD)})

definition="import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\n\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+NS+"\n\n"
definition+="\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in prov["definition_open_context_facts"])+"\n\n"
definition+="\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in prov["definition_facts"])+"\n\nend "+NS+"\n"
check("four_actual_Def_spans_and_parser_namespace_context_exact",definition.encode()==(OUT / "staged" / plan["local_definition"]).read_bytes(),{"proofs_in_new_Def":0,"source_defs":4})
check("fresh_new_native_and_staged_object_cache_not_borrowed",receipt["native_and_staged_objects_borrowed"] is False and not receipt.get("resumed_same_project_successful_steps"),{"project":"project","five_native_source_modules":True,"only_Mathlib_dependency_cache_shared":True})
failed_gate=load(OUT / "audit-gate-failed-attempt.json")
check("Python_splice_oracle_snapshot_failure_preserved",failed_gate["verdict"]=="FAIL" and failed_gate["error"]=="complete_original_Reflection_proof_core_and_all_three_parser_splices_exact" and sha(OUT / "audit_and_freeze.py.before-splice-oracle-fix")==failed_gate["original_audit_script_sha256"] and failed_gate["actual_proof_source_modified"] is False,{"retained":"audit-gate-failed-attempt.json","repair":"Select the actual executed Reflection parser snapshot instead of the PF generic snapshot; no mathematical or staged source change and no Lean recompilation."})

copyfiles=[]
for rel in [plan["local_definition"]]+[t[k] for t in plan["targets"] for k in ["local_solution","local_reference"]]:
    file=OUT / "staged" / rel;dest=ROOT / rel
    copyfiles.append({"staged_task_relative":file.relative_to(TASK).as_posix(),"root_relative_destination":rel,"bytes":file.stat().st_size,"sha256":sha(file),"destination_exists_at_author_freeze":dest.exists()})
    if dest.exists():assert sha(dest)==sha(file),"Existing root differs; parent must resolve without overwrite."
copyplan={"source_sha256":receipt["source_sha256"]["CoefficientMapReflection"],"sources_sha256":receipt["source_sha256"],"required_existing_Definitions":plan["existing_definitions"],"author_scope":"offline new task-local staged/project only; parent handles installation","overwrite_allowed":False,"files":copyfiles,"scope_build_entrypoints_for_parent":[t["local_solution"].removesuffix(".lean").replace("/",".") for t in plan["targets"]]}
dump(OUT / "root-copy-plan.json",copyplan)
dump(OUT / "decl-plan.json",{"selected_public_endpoints":[t["theorem_name"] for t in plan["targets"]],"actual_cross_module_graph_records":prov["graph_records"],"retained_Reflection_source_declarations":34,"moved_genuine_Definitions":4,"inline_original_Reflection_proofs":30,"actual_cross_module_core_closure":prov["cross_module_core_closure"],"inline_cross_module_helper_names":prov["inline_helper_names"],"generated_records":prov["generated_records"],"generated_helpers_regenerated_from_exact_Definitions":True,"new_external_theorem_boundaries":[]})
limitations=["The local coefficient sign reflection and the even-order rho cancellation keep the exact original Even n premise. Both concern genuine local formal coefficients for 1<=s<=9 and do not need properness. The rho_one endpoint needs the original StrongProperMultiplier degree condition and has no Even premise.","StrongProperMultiplier is 2*n+2*W.natDegree<=9*(n+1)-2. It is stronger than strict properness. The proof of rho1=0 uses the actual global PF polynomial identity and its coefficient at9*n+8, not a cancellation assumption.","For n=0,W=X^4 all even-order totals vanish but rho1=1, the actual weighted function is1/t, and StrongProper fails although strict properness holds. For n=1 all quartics are StrongProper and rho1=0 without Even n; even-n anti-reflection is not extended to odd n, with the original actual rational counterexample recompiled.","This batch is finite and formal over rational coefficients. It does not assert infinite Eq4/L convergence, a prescribed exact L, original five-dimensional aggregate F injectivity/inverse, denominator integrality, J or irrationality. Integer W does not automatically make every local rational coefficient an integer.","Reference stubs intentionally use sorryAx and are statements only. Complete solutions and inline helpers use only standard axioms. This author gate is separate from an independent transplantation review, parent root build and platform acceptance."]
readme="""# Actual reflection and coefficient totals offline author batch

Three exact frozen source endpoints are staged: local_coefficient_reflection, rho_even_order_zero and rho_one_zero_of_strong_proper. Lean4.33.1, Mathlib0df444a360eaa60ab8c11dca51a86af692955474. A prior independent native mathematical review is hash-bound; this author report does not claim independent transplantation review or platform acceptance.

Five original actual sources are freshly compiled in a new local project. The executed graph, five source parser/ref snapshots and Parser.parseHeader supply real source spans. Four unchanged actual definitions move to a lightweight Def importing the genuine Base/Jet/Injectivity/PF Def chain. Installed PF Def SHA74904aff5266f68b9d9f5c3013fb636f48d0cadda75e872093419845f9b666e5 is checked before project copy. All 30 original Reflection proofs are retained in each Solution; the genuine cross-source proof closure is inlined. Namespace open context comes from actual parser command spans. Only moved defs, diagnostics and mission header are removed; selected bindings/resolved references are renamed, then exact-signature wrappers are appended. No Theorems, Solutions or mission proof boundary is introduced.

All34 actual definition types/values agree across seven contexts (238 comparisons). Three original/Solution/reference endpoint types are identical, with no new binders or premises. Complete endpoints use propext, Classical.choice, Quot.sound. All source and inline helper proof records are separately checked for only standard axioms. Reference stubs deliberately contain sorryAx. compile-receipt.json retains actual exits/logs; any failed attempt is preserved rather than omitted.

The first two endpoints require Even n; their genuine local coefficient sign and even-order total cancellation need no properness. The rho1 endpoint requires StrongProper:2*n+2*W.natDegree<=9*(n+1)-2, without Even n. Its real proof uses the actual finite global PF polynomial identity. Original boundary statements are recompiled against the full staged rho1 Solution and compared exactly: n=0,W=X^4 has even totals0 but rho1=1/proper/notStrong/actual1/t; n=1 quartics are Strong with rho1=0, while the even-n anti-reflection claim fails for odd n. These conditions are kept in requests and theorem types.

No analytic formal-series evaluation, infinite Eq4/L convergence, prescribed exact L, original five-dimensional aggregate F injectivity/inverse, denominator integrality, J or irrationality is asserted by this finite batch. Only the new task-local batch/project is written. All prior four batches including PF frozen174files, mathematical sources, shared root and scope remain unchanged; API and credentials are not accessed. root-copy-plan.json provides source_sha256, seven new module sources and four genuine existing Def dependencies for the parent. Publication remains separate.

The first Python exact-splice gate selected the PF generic parser snapshot rather than the executed Reflection-specific snapshot. audit-gate-failed-attempt.json and the prior gate script retain that failed check and difference. The repair selects the correct actual Reflection parser file and verifies its34decl/178ref/56command counts. No source or staged proof byte changed, and all31Lean runs plus the59record boundary compilation had already passed.
"""

write(OUT / "README.md",readme)
# Source/config/oracle/log/request evidence only; never recurse through .lake packages.
stable=[p for p in OUT.iterdir() if p.is_file() and p.name not in ["author-audit.json","SHA256SUMS.txt","source-manifest.json"]]
stable+=list((OUT / "staged").rglob("*.lean"))
stable+=list(PROJECT.glob("*.lean"))+[PROJECT / "lake-manifest.json",PROJECT / "lean-toolchain"]
stable+=[PROJECT / ("missions/zeta9/formalization/"+n+".lean") for n in receipt["source_sha256"]]
stable+=list((PROJECT / "Definitions").glob("*.lean"))+list((PROJECT / "Solutions").glob("*.lean"))+list((PROJECT / "Theorems").glob("*.lean"))
stable=list(dict.fromkeys(stable))
manifest={"schema_version":1,"source_sha256":receipt["source_sha256"],"files":[{"task_relative":p.relative_to(TASK).as_posix(),"batch_relative":p.relative_to(OUT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)} for p in sorted(stable)],"existing_definition_dependencies":plan["existing_definitions"],"prior_native_independent_review_sha256":sha(math_review),"old_batches_modified":False}
dump(OUT / "source-manifest.json",manifest)
audit={"schema_version":1,"review_role":"author offline source-integration gate; independent review required separately","verdict":"PASS" if all(c["pass"] for c in checks) else "FAIL","source_sha256":receipt["source_sha256"]["CoefficientMapReflection"],"sources_sha256":receipt["source_sha256"],"mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474","lean_toolchain":"leanprover/lean4:v4.33.1","checks":checks,"targets":targets,"definition_comparisons":comparisons,"all_proof_records":helpers,"boundary_comparisons":boundary_comparisons,"actual_cross_module_helpers":prov["inline_helper_names"],"limitations":limitations,"platform_published":False,"platform_accepted":False,"root_installed_by_author":False,"independent_transplantation_review_claimed":False,"root_scope_API_credential_writes":False,"stable_files":manifest["files"]}
dump(OUT / "author-audit.json",audit)
freeze=stable+[OUT / "source-manifest.json",OUT / "author-audit.json"]
write(OUT / "SHA256SUMS.txt","".join(sha(p)+"  "+p.relative_to(OUT).as_posix()+"\n" for p in sorted(freeze)))
for line in (OUT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    h,rel=line.split("  ",1);assert sha(OUT / rel)==h
print(json.dumps({"author_verdict":audit["verdict"],"checks":len(checks),"graph_records":prov["graph_records"],"source_fact_counts":prov["source_fact_counts"],"inline_helpers":prov["inline_helper_names"],"proof_records":3*per,"definition_comparisons":len(comparisons),"frozen_files":len(freeze),"author_audit_sha256":sha(OUT / "author-audit.json"),"copyplan_sha256":sha(OUT / "root-copy-plan.json"),"manifest_sha256":sha(OUT / "source-manifest.json"),"SHA256SUMS_sha256":sha(OUT / "SHA256SUMS.txt")},ensure_ascii=False),flush=True)
