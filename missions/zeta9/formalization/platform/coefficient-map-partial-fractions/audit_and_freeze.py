"""Author-only offline gate; independent transplantation review remains separate."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT / "project"
NS="ZetaNine.CoefficientMapPartialFractions";STD={"propext","Classical.choice","Quot.sound"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,s):p.write_text(s,encoding="utf-8",newline="\n")
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
checks=[]
def check(name,okay,evidence=None):
    checks.append({"name":name,"pass":bool(okay),"evidence":evidence});assert okay,name
receipt=load(OUT / "compile-receipt.json");plan=load(OUT / "target-plan.json");prov=load(OUT / "integration-provenance.json")
check("four_frozen_actual_sources_unchanged",all(sha(TASK / ("formalization/"+n+".lean"))==h for n,h in receipt["source_sha256"].items()),receipt["source_sha256"])
math_review=TASK / "verification/formalization-coefficient-map-partial-fractions-2026-10-03/independent-review.json"
math=load(math_review)
check("prior_independent_native_math_review_bound",sha(math_review)=="df4d12de4529335fca0070e5d71294f396d8a00ef3fc9045cc74188f187ecea9" and math["verdict"]=="PASS" and len(math["checks"])==16,{"task_relative":math_review.relative_to(TASK).as_posix(),"sha256":sha(math_review),"is_independent_transplantation_review":False})
check("all_twenty_nine_actual_author_runs_exit_zero",receipt.get("complete") is True and len(receipt["rows"])==29 and all(r["exit_code"]==0 and sha(OUT / r["log"])==r["log_sha256"] for r in receipt["rows"]),{"runs":len(receipt["rows"]),"native_source_compilation":1,"official_graph_and_parser_and_header_runs":6,"staged_source_builds_including_actual_existing_Definitions":10,"actual_import_reports":11,"toolchain_probe":1})
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
check("all_thirty_actual_definition_types_and_values_equal",len(definitions)==30 and len(comparisons)==210 and all(r["type_equal"] and r["value_equal"] and set(r["axioms"])<=STD for r in comparisons),{"Base":9,"Jet":9,"Injectivity":7,"PartialFractions":5,"exact_actual_comparisons":210})
targets=[]
for i,t in enumerate(plan["targets"]):
    full=t["theorem_name"];orig=original[full];sol=reports[f"types_{i}_solution"][full];ref=reports[f"types_{i}_reference"][full]
    targets.append({"theorem":full,"actual_original_type":orig["type"],"original_solution_reference_type_equal":orig["type"]==sol["type"]==ref["type"],"original_axioms":orig["axioms"],"solution_axioms":sol["axioms"],"reference_axioms":ref["axioms"]})
check("three_original_Solution_reference_types_exact_no_extra_hypotheses",all(t["original_solution_reference_type_equal"] for t in targets),targets)
check("complete_solution_endpoints_exact_standard_three_axioms",all(set(t["solution_axioms"])==STD and set(t["original_axioms"])==STD for t in targets),sorted(STD))
helpers=[rows(OUT / f"helpers_{i}.log") for i in range(3)]
per=28+len(prov["inline_helper_names"])
check("all_original_twenty_seven_proofs_cross_module_closure_and_wrapper_standard_axioms",all(len(rs)==per and all(set(r["axioms"])<=STD for r in rs) for rs in helpers),{"proofs_per_solution":per,"total_proof_records":3*per,"cross_module_inline_names":prov["inline_helper_names"]})
check("no_external_Theorems_Solutions_or_native_proof_boundary",not prov["new_external_theorem_boundaries"] and all(not any(line.startswith(("import Theorems.","import Solutions.","import missions.")) for line in (OUT / "staged" / t["local_solution"]).read_text(encoding="utf-8").splitlines()) for t in plan["targets"]))
check("reference_stubs_explicitly_not_proofs",all("sorryAx" in t["reference_axioms"] for t in targets))
check("actual_source_core_and_Def_lightweight",prov["source_declarations"]==32 and prov["source_defs"]==5 and prov["source_proofs"]==27 and len(prov["definition_facts"])==5)
req=load(OUT / "problems-request.json");dreq=load(OUT / "definitions-request.json")[0]
dfields={"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"};tfields={"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("documented_offline_API_fields_only",set(dreq)<=dfields and set(req)=={"problems","env","private"} and all(set(t)<=tfields and t["formal_statement"].endswith(":= by sorry") and len(t["theorem_title"])<=200 for t in req["problems"]),{"schema_reference":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md","API_called":False})
check("definition_request_exact_staged_source",dreq["definition"].encode()==(OUT / "staged" / plan["local_definition"]).read_bytes())
check("proper_regular_Q_all_nine_and_both_n_zero_prose_limits_faithful",all(text in req["problems"][i]["natural_language_statement"] for i,text in [(0,"neither strict properness"),(1,"$X^{10}$"),(2,"rational"),(2,"$1/t$"),(2,"$W=X^5$")]))
check("native_independent_boundary_limits_bound",math["actual_global_polynomial_PF_closed"] is True and math["actual_global_regular_Q_PF_closed"] is True and math["original_aggregate_F_injectivity_closed"] is False and math["original_aggregate_F_inverse_closed"] is False and math["uniform_stronger_O_one_over_t_squared_closed"] is False and math["rho1_zero_closed"] is False and math["exact_L_closed"] is False and math["infinite_sum_convergence_closed"] is False)
check("three_actual_dependency_Def_stage_root_bytes_identical",len(plan["existing_definitions"])==3 and all(sha(ROOT / d["root_relative"])==d["sha256"]==sha(TASK / d["task_relative"])==sha(PROJECT / d["root_relative"]) for d in plan["existing_definitions"]),plan["existing_definitions"])

old_members=0
for name in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity"]:
    old=TASK / "formalization/platform" / name
    for line in (old / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
        h,rel=line.split("  ",1);assert sha(old / rel)==h;old_members+=1
check("all_341_old_author_frozen_members_unchanged",old_members==341,{"Base_frozen_members":96,"Jet_frozen_members":111,"Injectivity_frozen_members":134,"old_batches_written_by_author":False})
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
sources={n:(TASK / ("formalization/"+n+".lean")).read_bytes() for n in receipt["source_sha256"]}
check("real_graph_no_axiom_declaration_or_external_boundary",len(graph)==prov["graph_records"] and not any(g["kind"]=="axiom" for g in graph) and not prov["new_external_theorem_boundaries"])
bridge=""
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity"]:
    helpers=[f for f in prov["inline_helper_facts"] if f["module"]==module]
    if not helpers:continue
    bridge+="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
    for h in helpers:
        f=h["fact"];bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n"
    bridge+="end ZetaNine."+module+"\n\n"
check("actual_cross_source_proof_spans_exact",bridge.encode()==(OUT / "actual-proof-bridge.lean.inc").read_bytes() and hashlib.sha256(bridge.encode()).hexdigest()==prov["bridge_sha256"])
source=sources["CoefficientMapPartialFractions"];header_end=prov["header"]["end"]["offset"]
facts=rows(OUT / "sketch_info.jsonl")
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
    prefix="import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\nimport Mathlib.Tactic\nimport Mathlib.RingTheory.PowerSeries.Trunc\n\n"+bridge
    reconstructed=prefix+"\n"+edit(source,cuts+changes).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity\n\ntheorem solution"+pr["original_signature"]+":= by\n  exact "+NS+".checked_"+name+" "+t["wrapper_arguments"]+"\n\n#print axioms solution\n"
    stage_replays.append(reconstructed.encode()==(OUT / "staged" / t["local_solution"]).read_bytes())
check("complete_original_PF_proof_core_and_all_three_parser_splices_exact",all(stage_replays) and len(prov["definition_facts"])==5 and len(prov["deleted_diagnostic_facts"])==12,{"original_proofs_retained_per_Sol":27,"new_hypotheses":[]})
boundary=load(OUT / "stage-boundary-report.json")
native_boundary=load(TASK / "verification/formalization-coefficient-map-partial-fractions-2026-10-03/independent-boundary-types.json")
native_byname={r["declaration"]:r for r in native_boundary}
boundary_comparisons=[]
for r in boundary["records"]:
    name=r["declaration"].replace(".checked_actual_global_partial_fractions",".actual_global_partial_fractions")
    orig=native_byname[name]
    boundary_comparisons.append({"declaration":r["declaration"],"native_type_exact":orig["type"]==r["type"],"native_definition_value_exact":orig["definitionValue"]==r["definitionValue"],"axioms":r["axioms"]})
check("actual_staged_n_zero_simple_pole_and_nonproper_failure_recompiled",boundary["exit_code"]==0 and (OUT / "stage-boundary-audit-exit.txt").read_text().strip()=="0" and len(boundary_comparisons)==51 and boundary["all_standard_axioms"] and all(r["native_type_exact"] and r["native_definition_value_exact"] for r in boundary_comparisons),{"records":51,"source_records":32,"exact_original_boundary_checks":19,"all_axioms":sorted(STD)})

failed=load(OUT / "retained-failed-attempt.json")
check("earlier_namespace_wrapper_failure_preserved_and_resolution_restored",all(sha(OUT / r["preserved_batch_relative"])==r["sha256"] for r in failed["files"]) and load(OUT / "compile-receipt.json.before-namespace-context-fix")["rows"][-1]["exit_code"]==1 and receipt["retained_failed_attempt"]=="retained-failed-attempt.json" and len(receipt["resumed_same_project_successful_steps"])==12,{"failed_build_label":"build-0-solution","original_proof_core_modified":False,"repair":"Original ZetaNine name resolution restored by global open."})
copyfiles=[]
for rel in [plan["local_definition"]]+[t[k] for t in plan["targets"] for k in ["local_solution","local_reference"]]:
    file=OUT / "staged" / rel;dest=ROOT / rel
    copyfiles.append({"staged_task_relative":file.relative_to(TASK).as_posix(),"root_relative_destination":rel,"bytes":file.stat().st_size,"sha256":sha(file),"destination_exists_at_author_freeze":dest.exists()})
    if dest.exists():assert sha(dest)==sha(file),"Existing root differs; parent must resolve without overwrite."
copyplan={"source_sha256":receipt["source_sha256"]["CoefficientMapPartialFractions"],"sources_sha256":receipt["source_sha256"],"required_existing_Definitions":plan["existing_definitions"],"author_scope":"offline new task-local staged/project only; parent handles installation","overwrite_allowed":False,"files":copyfiles,"scope_build_entrypoints_for_parent":[t["local_solution"].removesuffix(".lean").replace("/",".") for t in plan["targets"]]}
dump(OUT / "root-copy-plan.json",copyplan)
dump(OUT / "decl-plan.json",{"selected_public_endpoints":[t["theorem_name"] for t in plan["targets"]],"actual_cross_module_graph_records":prov["graph_records"],"retained_PartialFractions_source_declarations":32,"moved_genuine_Definitions":5,"inline_original_PartialFractions_proofs":27,"actual_cross_module_core_closure":prov["cross_module_core_closure"],"inline_cross_module_helper_names":prov["inline_helper_names"],"generated_records":prov["generated_records"],"generated_helpers_regenerated_from_exact_Definitions":True,"new_external_theorem_boundaries":[]})
limitations=["Candidate local coefficient equality is for all nine actual coefficients, with j<=n and 1<=s<=9, without a properness premise. It uses the genuine shifted products and their formal unit denominator inverse; no arbitrary coefficient array or candidate match is assumed.","The global polynomial identity requires the exact strict proper condition 2*n+2*W.natDegree<9*(n+1). The rational finite partial-fraction equality additionally requires every t+k nonzero for rational t and k<=n. No formal series is evaluated analytically.","At n=0,W=X^4 the condition holds but the actual weighted function is 1/t and the simple-pole coefficient is one. At n=0,W=X^5 properness fails; the nine coefficients and partial numerator vanish while the actual function at the regular point t=1 equals one. These boundaries are retained and staged-compiled separately.","No infinite L-sum convergence, rho1 vanishing, uniform stronger O(1/t^2), prescribed exact L, original five-dimensional aggregate F injectivity/inverse, J or irrationality is asserted by this batch.","Reference theorem files intentionally use sorryAx and are statements only. All complete Solution proofs and inline actual helpers use only standard axioms. The author's offline gate is not an independent transplantation review or platform acceptance."]
readme="""# Actual finite partial-fractions offline author batch

Three exact frozen source endpoints are prepared: candidate_local_coefficients, actual_global_polynomial_partial_fractions and actual_global_partial_fractions. Environment: Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. The prior independent native mathematical review is hash-bound. This author batch still requires a separate independent transplantation review.

A fresh four-source native project supplies the actually executed cross-module declaration graph, four Lean parser/reference snapshots and the exact Parser.parseHeader span. Five unchanged real candidate definitions are moved to a lightweight Def importing the genuine Base/Jet/Injectivity Def chain. Each Solution retains all 27 original PF proofs and inlines the actual cross-source proof closure. Only the moved definition spans, diagnostic commands and original mission header are deleted. Selected theorem bindings/resolved references are renamed using actual parser spans; an exact original-signature wrapper is appended. Mathlib.Tactic preserves the source's transitive tactic import. There is no Theorems/Solutions/mission proof boundary or added hypothesis.

All 30 Base/Jet/Injectivity/PF definition types and values are compared in seven staged contexts (210 comparisons). The three original/Solution/reference statement types are exact. Complete endpoints use propext, Classical.choice and Quot.sound; helper proof records use only those standard axioms. Reference stubs deliberately contain sorryAx and are statements only. Real exits and logs remain in compile-receipt.json; no failed attempt is omitted.

The local nine-coefficient match does not require properness. The global polynomial identity requires 2*n+2*W.natDegree<9*(n+1). The finite rational-function identity additionally requires t+k nonzero for every k<=n, with t rational. Formal Q[[z]] coefficient identities do not imply analytic convergence. At n=0,W=X^4 the proper domain permits 1/t and simple-pole coefficient one; at n=0,W=X^5 the nine-order candidate vanishes while the actual function at regular t=1 equals one, and properness fails. Boundary source checks are recompiled against the complete staged Solution. No infinite L/convergence, rho1 vanishing, original five-dimensional aggregate F injectivity/inverse, prescribed exact L, J or irrationality is claimed.

The first appended global wrapper attempt lacked ZetaNine name resolution for the unchanged relative CoefficientMapJet/CoefficientMap names. Its failure logs, receipt and stage source bytes are preserved in retained-failed-attempt.json. The repair restores the original namespace resolution with an open command; it changes no proof or hypothesis. Twelve already successful fresh same-project native/oracle/Def steps are retained without rerunning; the final receipt records all 29 successful runs and the retained failed attempt separately.

Only this new task-local batch/project is written. Frozen mathematical sources, prior batches, shared root and scope are preserved. No API or credentials are accessed. root-copy-plan.json has the leaf source_sha256, seven proposed new modules, and all three genuine existing Def dependencies. Requests are offline only; independent review, installation and publication are separate parent actions.
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
audit={"schema_version":1,"review_role":"author offline source-integration gate; independent review required separately","verdict":"PASS" if all(c["pass"] for c in checks) else "FAIL","source_sha256":receipt["source_sha256"]["CoefficientMapPartialFractions"],"sources_sha256":receipt["source_sha256"],"mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474","lean_toolchain":"leanprover/lean4:v4.33.1","checks":checks,"targets":targets,"definition_comparisons":comparisons,"all_proof_records":helpers,"boundary_comparisons":boundary_comparisons,"actual_cross_module_helpers":prov["inline_helper_names"],"limitations":limitations,"platform_published":False,"platform_accepted":False,"root_installed_by_author":False,"independent_transplantation_review_claimed":False,"root_scope_API_credential_writes":False,"stable_files":manifest["files"]}
dump(OUT / "author-audit.json",audit)
freeze=stable+[OUT / "source-manifest.json",OUT / "author-audit.json"]
write(OUT / "SHA256SUMS.txt","".join(sha(p)+"  "+p.relative_to(OUT).as_posix()+"\n" for p in sorted(freeze)))
for line in (OUT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    h,rel=line.split("  ",1);assert sha(OUT / rel)==h
print(json.dumps({"author_verdict":audit["verdict"],"checks":len(checks),"graph_records":prov["graph_records"],"source_fact_counts":prov["source_fact_counts"],"inline_helpers":prov["inline_helper_names"],"proof_records":3*per,"definition_comparisons":len(comparisons),"frozen_files":len(freeze),"author_audit_sha256":sha(OUT / "author-audit.json"),"copyplan_sha256":sha(OUT / "root-copy-plan.json"),"manifest_sha256":sha(OUT / "source-manifest.json"),"SHA256SUMS_sha256":sha(OUT / "SHA256SUMS.txt")},ensure_ascii=False),flush=True)
