"""Author-only offline gate; independent transplantation review remains separate."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT / "project"
NS="ZetaNine.CoefficientMapInjectivity";STD={"propext","Classical.choice","Quot.sound"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,s):p.write_text(s,encoding="utf-8",newline="\n")
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
checks=[]
def check(name,okay,evidence=None):
    checks.append({"name":name,"pass":bool(okay),"evidence":evidence});assert okay,name
receipt=load(OUT / "compile-receipt.json");plan=load(OUT / "target-plan.json");prov=load(OUT / "integration-provenance.json")
check("three_frozen_actual_sources_unchanged",all(sha(TASK / ("formalization/"+n+".lean"))==h for n,h in receipt["source_sha256"].items()),receipt["source_sha256"])
math_review=TASK / "verification/formalization-coefficient-map-injectivity-2026-10-03/independent-review.json"
math=load(math_review)
check("prior_independent_native_math_review_bound",sha(math_review)=="a271a7c004845f9151f79c7779cea6c451337d65890922fd8a15dae9a5aea747" and math["verdict"]=="PASS" and len(math["checks"])==16,{"task_relative":math_review.relative_to(TASK).as_posix(),"sha256":sha(math_review),"is_independent_transplantation_review":False})
check("all_twenty_seven_actual_author_runs_exit_zero",receipt.get("complete") is True and len(receipt["rows"])==27 and all(r["exit_code"]==0 and sha(OUT / r["log"])==r["log_sha256"] for r in receipt["rows"]),{"runs":len(receipt["rows"]),"native_source_compilation":1,"official_graph_and_parser_and_header_runs":5,"staged_source_builds_including_actual_existing_Definitions":9,"actual_import_reports":11,"toolchain_probe":1})
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
check("all_twenty_five_actual_definition_types_and_values_equal",len(definitions)==25 and len(comparisons)==175 and all(r["type_equal"] and r["value_equal"] and set(r["axioms"])<=STD for r in comparisons),{"Base":9,"Jet":9,"Injectivity":7,"exact_actual_comparisons":175})
targets=[]
for i,t in enumerate(plan["targets"]):
    full=t["theorem_name"];orig=original[full];sol=reports[f"types_{i}_solution"][full];ref=reports[f"types_{i}_reference"][full]
    targets.append({"theorem":full,"actual_original_type":orig["type"],"original_solution_reference_type_equal":orig["type"]==sol["type"]==ref["type"],"original_axioms":orig["axioms"],"solution_axioms":sol["axioms"],"reference_axioms":ref["axioms"]})
check("three_original_Solution_reference_types_exact_no_extra_hypotheses",all(t["original_solution_reference_type_equal"] for t in targets),targets)
check("complete_solution_endpoints_exact_standard_three_axioms",all(set(t["solution_axioms"])==STD and set(t["original_axioms"])==STD for t in targets),sorted(STD))
helpers=[rows(OUT / f"helpers_{i}.log") for i in range(3)]
per=19+len(prov["inline_helper_names"])
check("all_original_eighteen_proofs_cross_module_closure_and_wrapper_standard_axioms",all(len(rs)==per and all(set(r["axioms"])<=STD for r in rs) for rs in helpers),{"proofs_per_solution":per,"total_proof_records":3*per,"cross_module_inline_names":prov["inline_helper_names"]})
check("no_external_Theorems_Solutions_or_native_proof_boundary",not prov["new_external_theorem_boundaries"] and all(not any(line.startswith(("import Theorems.","import Solutions.","import missions.")) for line in (OUT / "staged" / t["local_solution"]).read_text(encoding="utf-8").splitlines()) for t in plan["targets"]))
check("reference_stubs_explicitly_not_proofs",all("sorryAx" in t["reference_axioms"] for t in targets))
check("actual_source_core_and_Def_lightweight",prov["source_declarations"]==25 and prov["source_defs"]==7 and prov["source_proofs"]==18 and len(prov["definition_facts"])==7)
req=load(OUT / "problems-request.json");dreq=load(OUT / "definitions-request.json")[0]
dfields={"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"};tfields={"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("documented_offline_API_fields_only",set(dreq)<=dfields and set(req)=={"problems","env","private"} and all(set(t)<=tfields and t["formal_statement"].endswith(":= by sorry") and len(t["theorem_title"])<=200 for t in req["problems"]),{"schema_reference":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md","API_called":False})
check("definition_request_exact_staged_source",dreq["definition"].encode()==(OUT / "staged" / plan["local_definition"]).read_bytes())
check("properness_full_array_and_n_zero_prose_limits_faithful","complete" in req["problems"][0]["natural_language_statement"] and "five aggregated" in req["problems"][0]["natural_language_statement"] and "No surjectivity" in req["problems"][1]["natural_language_statement"] and "including zero" in req["problems"][2]["natural_language_statement"] and "$1/t$" in req["problems"][2]["natural_language_statement"])
check("native_independent_boundary_limits_bound",math["original_aggregated_F_injectivity_closed"] is False and math["original_aggregated_F_inverse_closed"] is False and math["stronger_uniform_O_one_over_t_squared_closed"] is False and math["rho1_zero_closed"] is False and math["exact_L_closed"] is False)
old_members=0
for name in ["coefficient-map","coefficient-map-jet"]:
    old=TASK / "formalization/platform" / name
    for line in (old / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
        h,rel=line.split("  ",1);assert sha(old / rel)==h;old_members+=1
check("all_207_old_author_frozen_members_unchanged",old_members==207,{"Base_frozen_members":96,"Jet_frozen_members":111,"old_batches_written_by_author":False})
copyfiles=[]
for rel in [plan["local_definition"]]+[t[k] for t in plan["targets"] for k in ["local_solution","local_reference"]]:
    file=OUT / "staged" / rel;dest=ROOT / rel
    copyfiles.append({"staged_task_relative":file.relative_to(TASK).as_posix(),"root_relative_destination":rel,"bytes":file.stat().st_size,"sha256":sha(file),"destination_exists_at_author_freeze":dest.exists()})
    if dest.exists():assert sha(dest)==sha(file),"Existing root differs; parent must resolve without overwrite."
copyplan={"sources_sha256":receipt["source_sha256"],"required_existing_Definitions":plan["existing_definitions"],"author_scope":"offline new task-local staged/project only; parent handles installation","overwrite_allowed":False,"files":copyfiles,"scope_build_entrypoints_for_parent":[t["local_solution"].removesuffix(".lean").replace("/",".") for t in plan["targets"]]}
dump(OUT / "root-copy-plan.json",copyplan)
dump(OUT / "decl-plan.json",{"selected_public_endpoints":[t["theorem_name"] for t in plan["targets"]],"actual_cross_module_graph_records":prov["graph_records"],"retained_Injectivity_source_declarations":25,"moved_genuine_Definitions":7,"inline_original_Injectivity_proofs":18,"actual_cross_module_core_closure":prov["cross_module_core_closure"],"inline_cross_module_helper_names":prov["inline_helper_names"],"generated_records":prov["generated_records"],"generated_helpers_regenerated_from_exact_Definitions":True,"new_external_theorem_boundaries":[]})
limitations=["Injectivity is of the complete (n+1)*9 genuine rational formal-jet array on the strict proper polynomial domain. It does not prove injectivity/surjectivity/invertibility of the original five-dimensional aggregate F.","ProperMultiplier is the exact source condition 2*n+2*W.natDegree<9*(n+1). Quartics satisfy it for all natural n including zero. It only gives strict proper degree/O(1/t), without a stronger O(1/t^2) or rho1=0 claim; n=0,W=X^4 has the actual regular-point weighted function 1/t and local simple-pole coefficient one.","No analytic convergence, numerical formal-series evaluation, exact infinite L-sum, J or irrationality is asserted. No abstract coefficient arrays or target conclusions are substituted or added as assumptions.","Reference theorem files intentionally use sorryAx and are statements only. All three complete Solution proofs use exactly standard axioms; actual proof dependencies are source-inlined.","This is the author's offline gate, not an independent transplantation review or platform acceptance. Source/request/stages are prepared for review and later installation/publication by the parent."]
readme="""# Injectivity full local-array offline author batch

This new batch prepares three exact endpoints from the frozen actual CoefficientMapInjectivity source: all_local_coefficients_zero_implies_zero, fullLocalCoefficientMap_injective and quartic_is_proper. It uses Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. The prior independent native mathematical review is hash-bound; this batch's author audit is separate from an independent transplantation review.

The lightweight Definition contains seven unchanged genuine definitions and imports the actual Base/Jet Definition chain. A freshly compiled actual three-module native project supplies the executed declaration graph, all three Lean parser/reference snapshots and exact Parser.parseHeader span. Each Solution retains all 18 original Injectivity proofs and the complete actual cross-module proof closure inline. Only the seven moved definition spans, diagnostic commands and mission header are removed; the selected theorem binding and resolved references are renamed and an exact-signature solution wrapper is appended. Mathlib.Tactic restores the original transitive tactic import. No Theorems/Solutions/mission proof boundary or new hypothesis is introduced.

All actual original, Definition and Solution/reference type-value environments are compared. Seven Injectivity, nine Jet and nine Base definition values/types agree, and all three original/Solution/reference statement types agree exactly. Complete Solutions have only propext, Classical.choice and Quot.sound; reference stubs deliberately contain sorryAx. All inline helper proofs are separately axiom-audited. Detailed actual exits/logs are in compile-receipt.json.

The result is injectivity of the full (n+1) by 9 local array on the strict proper domain, not injectivity or an inverse of the original five aggregated F outputs. Properness only requires strict degree/O(1/t); it does not imply stronger decay or rho1=0. For n=0,W=X^4 a simple pole 1/t is allowed. No analytic convergence, exact infinite L-sum, J or irrationality is claimed.

Author writes are confined to this new task-local batch/project. Frozen mathematical sources, previous batches, shared root and scope were not changed; no API or credentials were accessed. root-copy-plan.json lists seven new source modules and the genuine existing Definition dependencies for the parent. definitions-request.json/proble ms-request.json are offline requests only. Independent transplantation review and platform acceptance remain separate.
""".replace("proble ms-request","problems-request")
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
audit={"schema_version":1,"review_role":"author offline source-integration gate; independent review required separately","verdict":"PASS" if all(c["pass"] for c in checks) else "FAIL","source_sha256":receipt["source_sha256"]["CoefficientMapInjectivity"],"sources_sha256":receipt["source_sha256"],"mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474","lean_toolchain":"leanprover/lean4:v4.33.1","checks":checks,"targets":targets,"definition_comparisons":comparisons,"all_proof_records":helpers,"actual_cross_module_helpers":prov["inline_helper_names"],"limitations":limitations,"platform_published":False,"platform_accepted":False,"root_installed_by_author":False,"independent_transplantation_review_claimed":False,"root_scope_API_credential_writes":False,"stable_files":manifest["files"]}
dump(OUT / "author-audit.json",audit)
freeze=stable+[OUT / "source-manifest.json",OUT / "author-audit.json"]
write(OUT / "SHA256SUMS.txt","".join(sha(p)+"  "+p.relative_to(OUT).as_posix()+"\n" for p in sorted(freeze)))
for line in (OUT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    h,rel=line.split("  ",1);assert sha(OUT / rel)==h
print(json.dumps({"author_verdict":audit["verdict"],"checks":len(checks),"graph_records":prov["graph_records"],"source_fact_counts":prov["source_fact_counts"],"inline_helpers":prov["inline_helper_names"],"proof_records":3*per,"definition_comparisons":len(comparisons),"frozen_files":len(freeze),"author_audit_sha256":sha(OUT / "author-audit.json"),"copyplan_sha256":sha(OUT / "root-copy-plan.json"),"manifest_sha256":sha(OUT / "source-manifest.json"),"SHA256SUMS_sha256":sha(OUT / "SHA256SUMS.txt")},ensure_ascii=False),flush=True)
