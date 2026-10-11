"""Configure author gates for this new batch only; never edit the old frozen template."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[2]
old=TASK / "formalization/platform/coefficient-map-injectivity/audit_and_freeze.py"
s=old.read_text(encoding="utf-8-sig")
def replace(a,b):
    global s
    assert a in s,a
    s=s.replace(a,b)
replace('CoefficientMapInjectivity','CoefficientMapPartialFractions')
replace('coefficient-map-injectivity','coefficient-map-partial-fractions')
replace('three_frozen_actual_sources_unchanged','four_frozen_actual_sources_unchanged')
replace('a271a7c004845f9151f79c7779cea6c451337d65890922fd8a15dae9a5aea747','df4d12de4529335fca0070e5d71294f396d8a00ef3fc9045cc74188f187ecea9')
replace('all_twenty_seven_actual_author_runs_exit_zero','all_twenty_nine_actual_author_runs_exit_zero')
replace('len(receipt["rows"])==27','len(receipt["rows"])==29')
replace('"official_graph_and_parser_and_header_runs":5','"official_graph_and_parser_and_header_runs":6')
replace('"staged_source_builds_including_actual_existing_Definitions":9','"staged_source_builds_including_actual_existing_Definitions":10')
replace('all_twenty_five_actual_definition_types_and_values_equal','all_thirty_actual_definition_types_and_values_equal')
replace('len(definitions)==25 and len(comparisons)==175','len(definitions)==30 and len(comparisons)==210')
replace('"Base":9,"Jet":9,"Injectivity":7,"exact_actual_comparisons":175','"Base":9,"Jet":9,"Injectivity":7,"PartialFractions":5,"exact_actual_comparisons":210')
replace('per=19+len(prov["inline_helper_names"])','per=28+len(prov["inline_helper_names"])')
replace('all_original_eighteen_proofs_cross_module_closure_and_wrapper_standard_axioms','all_original_twenty_seven_proofs_cross_module_closure_and_wrapper_standard_axioms')
replace('prov["source_declarations"]==25 and prov["source_defs"]==7 and prov["source_proofs"]==18 and len(prov["definition_facts"])==7','prov["source_declarations"]==32 and prov["source_defs"]==5 and prov["source_proofs"]==27 and len(prov["definition_facts"])==5')
a=s.index('check("properness_full_array_and_n_zero_prose_limits_faithful"');b=s.index('\nold_members=0',a)
s=s[:a]+'''check("proper_regular_Q_all_nine_and_both_n_zero_prose_limits_faithful",all(text in req["problems"][i]["natural_language_statement"] for i,text in [(0,"neither strict properness"),(1,"$X^{10}$"),(2,"rational"),(2,"$1/t$"),(2,"$W=X^5$")]))
check("native_independent_boundary_limits_bound",math["actual_global_polynomial_PF_closed"] is True and math["actual_global_regular_Q_PF_closed"] is True and math["original_aggregate_F_injectivity_closed"] is False and math["original_aggregate_F_inverse_closed"] is False and math["uniform_stronger_O_one_over_t_squared_closed"] is False and math["rho1_zero_closed"] is False and math["exact_L_closed"] is False and math["infinite_sum_convergence_closed"] is False)
check("three_actual_dependency_Def_stage_root_bytes_identical",len(plan["existing_definitions"])==3 and all(sha(ROOT / d["root_relative"])==d["sha256"]==sha(TASK / d["task_relative"])==sha(PROJECT / d["root_relative"]) for d in plan["existing_definitions"]),plan["existing_definitions"])
'''+s[b:]
replace('for name in ["coefficient-map","coefficient-map-jet"]:','for name in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity"]:')
replace('all_207_old_author_frozen_members_unchanged','all_341_old_author_frozen_members_unchanged')
replace('old_members==207','old_members==341')
replace('"Jet_frozen_members":111','"Jet_frozen_members":111,"Injectivity_frozen_members":134')
replace('copyplan={"sources_sha256":receipt["source_sha256"]','copyplan={"source_sha256":receipt["source_sha256"]["CoefficientMapPartialFractions"],"sources_sha256":receipt["source_sha256"]')
replace('"retained_Injectivity_source_declarations":25,"moved_genuine_Definitions":7,"inline_original_Injectivity_proofs":18','"retained_PartialFractions_source_declarations":32,"moved_genuine_Definitions":5,"inline_original_PartialFractions_proofs":27')
anchor='\ncopyfiles=[]'
addition='''
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
sources={n:(TASK / ("formalization/"+n+".lean")).read_bytes() for n in receipt["source_sha256"]}
check("real_graph_no_axiom_declaration_or_external_boundary",len(graph)==prov["graph_records"] and not any(g["kind"]=="axiom" for g in graph) and not prov["new_external_theorem_boundaries"])
bridge=""
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity"]:
    helpers=[f for f in prov["inline_helper_facts"] if f["module"]==module]
    if not helpers:continue
    bridge+="open scoped BigOperators\\nopen Finset Polynomial\\n\\nnamespace ZetaNine."+module+"\\n\\n"
    for h in helpers:
        f=h["fact"];bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\\n\\n"
    bridge+="end ZetaNine."+module+"\\n\\n"
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
    prefix="import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\nimport Mathlib.Tactic\\nimport Mathlib.RingTheory.PowerSeries.Trunc\\n\\n"+bridge
    reconstructed=prefix+"\\n"+edit(source,cuts+changes).decode()+"\\n\\nopen "+NS+" ZetaNine.CoefficientMapInjectivity\\n\\ntheorem solution"+pr["original_signature"]+":= by\\n  exact "+NS+".checked_"+name+" "+t["wrapper_arguments"]+"\\n\\n#print axioms solution\\n"
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
'''
replace(anchor,addition+anchor)
replace('"all_proof_records":helpers,','"all_proof_records":helpers,"boundary_comparisons":boundary_comparisons,')
replace('open "+NS+" ZetaNine.CoefficientMapInjectivity','open ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity')
replace('copyfiles=[]','''failed=load(OUT / "retained-failed-attempt.json")
check("earlier_namespace_wrapper_failure_preserved_and_resolution_restored",all(sha(OUT / r["preserved_batch_relative"])==r["sha256"] for r in failed["files"]) and load(OUT / "compile-receipt.json.before-namespace-context-fix")["rows"][-1]["exit_code"]==1 and receipt["retained_failed_attempt"]=="retained-failed-attempt.json" and len(receipt["resumed_same_project_successful_steps"])==12,{"failed_build_label":"build-0-solution","original_proof_core_modified":False,"repair":"Original ZetaNine name resolution restored by global open."})
copyfiles=[]''')
a=s.index('limitations=');b=s.index('\nwrite(OUT / "README.md",readme)',a)
s=s[:a]+'''limitations=["Candidate local coefficient equality is for all nine actual coefficients, with j<=n and 1<=s<=9, without a properness premise. It uses the genuine shifted products and their formal unit denominator inverse; no arbitrary coefficient array or candidate match is assumed.","The global polynomial identity requires the exact strict proper condition 2*n+2*W.natDegree<9*(n+1). The rational finite partial-fraction equality additionally requires every t+k nonzero for rational t and k<=n. No formal series is evaluated analytically.","At n=0,W=X^4 the condition holds but the actual weighted function is 1/t and the simple-pole coefficient is one. At n=0,W=X^5 properness fails; the nine coefficients and partial numerator vanish while the actual function at the regular point t=1 equals one. These boundaries are retained and staged-compiled separately.","No infinite L-sum convergence, rho1 vanishing, uniform stronger O(1/t^2), prescribed exact L, original five-dimensional aggregate F injectivity/inverse, J or irrationality is asserted by this batch.","Reference theorem files intentionally use sorryAx and are statements only. All complete Solution proofs and inline actual helpers use only standard axioms. The author's offline gate is not an independent transplantation review or platform acceptance."]
readme="""# Actual finite partial-fractions offline author batch

Three exact frozen source endpoints are prepared: candidate_local_coefficients, actual_global_polynomial_partial_fractions and actual_global_partial_fractions. Environment: Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. The prior independent native mathematical review is hash-bound. This author batch still requires a separate independent transplantation review.

A fresh four-source native project supplies the actually executed cross-module declaration graph, four Lean parser/reference snapshots and the exact Parser.parseHeader span. Five unchanged real candidate definitions are moved to a lightweight Def importing the genuine Base/Jet/Injectivity Def chain. Each Solution retains all 27 original PF proofs and inlines the actual cross-source proof closure. Only the moved definition spans, diagnostic commands and original mission header are deleted. Selected theorem bindings/resolved references are renamed using actual parser spans; an exact original-signature wrapper is appended. Mathlib.Tactic preserves the source's transitive tactic import. There is no Theorems/Solutions/mission proof boundary or added hypothesis.

All 30 Base/Jet/Injectivity/PF definition types and values are compared in seven staged contexts (210 comparisons). The three original/Solution/reference statement types are exact. Complete endpoints use propext, Classical.choice and Quot.sound; helper proof records use only those standard axioms. Reference stubs deliberately contain sorryAx and are statements only. Real exits and logs remain in compile-receipt.json; no failed attempt is omitted.

The local nine-coefficient match does not require properness. The global polynomial identity requires 2*n+2*W.natDegree<9*(n+1). The finite rational-function identity additionally requires t+k nonzero for every k<=n, with t rational. Formal Q[[z]] coefficient identities do not imply analytic convergence. At n=0,W=X^4 the proper domain permits 1/t and simple-pole coefficient one; at n=0,W=X^5 the nine-order candidate vanishes while the actual function at regular t=1 equals one, and properness fails. Boundary source checks are recompiled against the complete staged Solution. No infinite L/convergence, rho1 vanishing, original five-dimensional aggregate F injectivity/inverse, prescribed exact L, J or irrationality is claimed.

The first appended global wrapper attempt lacked ZetaNine name resolution for the unchanged relative CoefficientMapJet/CoefficientMap names. Its failure logs, receipt and stage source bytes are preserved in retained-failed-attempt.json. The repair restores the original namespace resolution with an open command; it changes no proof or hypothesis. Twelve already successful fresh same-project native/oracle/Def steps are retained without rerunning; the final receipt records all 29 successful runs and the retained failed attempt separately.

Only this new task-local batch/project is written. Frozen mathematical sources, prior batches, shared root and scope are preserved. No API or credentials are accessed. root-copy-plan.json has the leaf source_sha256, seven proposed new modules, and all three genuine existing Def dependencies. Requests are offline only; independent review, installation and publication are separate parent actions.
"""
'''+s[b:]
(OUT / "audit_and_freeze.py").write_text(s,encoding="utf-8",newline="\n")
(OUT / "audit-recipe-provenance.json").write_text(json.dumps({"template":old.relative_to(TASK).as_posix(),"template_sha256":hashlib.sha256(old.read_bytes()).hexdigest(),"author_only":True,"old_modified":False,"changes":"Four source, five definitions, 27 proof PF author gate with exact original types, 210 def comparisons, actual dependency Def stage/root checks, existing341freeze validation, and finite/proper/regularQ limits."},indent=2)+"\n",encoding="utf-8")
print("Configured current batch author gate.")
