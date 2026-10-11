"""Author-only Reflection gates configured from the frozen PF author schema."""
from pathlib import Path
import json,hashlib
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2]
OLD=TASK / "formalization/platform/coefficient-map-partial-fractions"
old=OLD / "audit_and_freeze.py"
s=old.read_text(encoding="utf-8-sig")
def replace(a,b):
    global s
    assert a in s,a
    s=s.replace(a,b)
replace('CoefficientMapPartialFractions','CoefficientMapReflection')
replace('coefficient-map-partial-fractions','coefficient-map-reflection')
replace('four_frozen_actual_sources_unchanged','five_frozen_actual_sources_unchanged')
replace('df4d12de4529335fca0070e5d71294f396d8a00ef3fc9045cc74188f187ecea9','ac3d8f135cb3c69b39074548bea712f418fa6d0273ad27e33805374c1db20123')
replace('len(math["checks"])==16','len(math["checks"])==17')
replace('all_twenty_nine_actual_author_runs_exit_zero','all_thirty_one_actual_author_runs_exit_zero')
replace('len(receipt["rows"])==29','len(receipt["rows"])==31')
replace('"official_graph_and_parser_and_header_runs":6','"official_graph_and_parser_and_header_runs":7')
replace('"staged_source_builds_including_actual_existing_Definitions":10','"staged_source_builds_including_actual_existing_Definitions":11')
replace('all_thirty_actual_definition_types_and_values_equal','all_thirty_four_actual_definition_types_and_values_equal')
replace('len(definitions)==30 and len(comparisons)==210','len(definitions)==34 and len(comparisons)==238')
replace('"Base":9,"Jet":9,"Injectivity":7,"PartialFractions":5,"exact_actual_comparisons":210','"Base":9,"Jet":9,"Injectivity":7,"PartialFractions":5,"Reflection":4,"exact_actual_comparisons":238')
replace('per=28+len(prov["inline_helper_names"])','per=31+len(prov["inline_helper_names"])')
replace('all_original_twenty_seven_proofs_cross_module_closure_and_wrapper_standard_axioms','all_original_thirty_proofs_cross_module_closure_and_wrapper_standard_axioms')
replace('prov["source_declarations"]==32 and prov["source_defs"]==5 and prov["source_proofs"]==27 and len(prov["definition_facts"])==5','prov["source_declarations"]==34 and prov["source_defs"]==4 and prov["source_proofs"]==30 and len(prov["definition_facts"])==4')
a=s.index('check("proper_regular_Q_all_nine_and_both_n_zero_prose_limits_faithful"');b=s.index('\nold_members=0',a)
s=s[:a]+'''check("Even_n_and_strong_bound_and_both_boundary_prose_faithful",all(text in req["problems"][i]["natural_language_statement"] for i,text in [(0,"$n$ is even"),(1,"$s$ even"),(1,"simple-pole total is one"),(2,"does not require Even n"),(2,"$n=1$"),(2,"proper but not StrongProper")]))
check("native_independent_exact_domains_and_open_limits_bound",math["actual_local_coefficient_reflection_closed"] is True and math["actual_even_rho_cancellation_closed"] is True and math["actual_rho_one_cancellation_under_stronger_bound_closed"] is True and math["rho1_zero_from_strict_proper_alone_closed"] is False and math["original_aggregate_F_injectivity_closed"] is False and math["original_aggregate_F_inverse_closed"] is False and math["infinite_sum_Eq4_closed"] is False and math["exact_L_closed"] is False)
check("four_actual_dependency_Def_stage_root_bytes_identical",len(plan["existing_definitions"])==4 and all(sha(ROOT / d["root_relative"])==d["sha256"]==sha(TASK / d["task_relative"])==sha(PROJECT / d["root_relative"]) for d in plan["existing_definitions"]),plan["existing_definitions"])
'''+s[b:]
replace('for name in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity"]:', 'for name in ["coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions"]:')
replace('all_341_old_author_frozen_members_unchanged','all_515_old_author_frozen_members_unchanged')
replace('old_members==341','old_members==515')
replace('"Injectivity_frozen_members":134','"Injectivity_frozen_members":134,"PartialFractions_frozen_members":174')
replace('for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity"]:', 'for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions"]:')
replace('    for h in helpers:\n', '''    opens=[r["fact"] for r in prov["bridge_open_context_facts"] if r["module"]==module]
    for f in opens:bridge+=sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\\n"
    if opens:bridge+="\\n"
    for h in helpers:
''')
replace('    prefix="import Definitions.Def_ZetaNine_CoefficientMapReflection\\nimport Mathlib.Tactic\\nimport Mathlib.RingTheory.PowerSeries.Trunc\\n\\n"+bridge','    prefix="import Definitions.Def_ZetaNine_CoefficientMapReflection\\nimport Mathlib.Tactic\\n\\n\\n"+bridge')
replace('open ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity\\n','open ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\\n')
replace('complete_original_PF_proof_core_and_all_three_parser_splices_exact','complete_original_Reflection_proof_core_and_all_three_parser_splices_exact')
replace('facts=rows(OUT / "sketch_info.jsonl")','facts=rows(OUT / "CoefficientMapReflection-sketch_info.jsonl")\ncheck("exact_Reflection_parser_snapshot_selected",{kind:sum(f["kind"]==kind for f in facts) for kind in ["decl","ref","command"]}==prov["source_fact_counts"]=={"decl":34,"ref":178,"command":56},"CoefficientMapReflection-sketch_info.jsonl")')
replace('len(prov["definition_facts"])==5 and len(prov["deleted_diagnostic_facts"])==12','len(prov["definition_facts"])==4 and len(prov["deleted_diagnostic_facts"])==11')
replace('"original_proofs_retained_per_Sol":27','"original_proofs_retained_per_Sol":30')
replace('name=r["declaration"].replace(".checked_actual_global_partial_fractions",".actual_global_partial_fractions")','name=r["declaration"].replace(".checked_rho_one_zero_of_strong_proper",".rho_one_zero_of_strong_proper")')
replace('actual_staged_n_zero_simple_pole_and_nonproper_failure_recompiled','actual_staged_n_zero_simple_pole_and_odd_n_boundaries_recompiled')
replace('len(boundary_comparisons)==51','len(boundary_comparisons)==59')
replace('"records":51,"source_records":32,"exact_original_boundary_checks":19','"records":59,"source_records":34,"exact_original_boundary_checks":25')
a=s.index('failed=load(OUT / "retained-failed-attempt.json")');b=s.index('\ncopyfiles=[]',a)
s=s[:a]+'''definition="import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\n\\n\\nset_option autoImplicit false\\nnoncomputable section\\nopen scoped BigOperators\\nopen Finset Polynomial\\n\\nnamespace "+NS+"\\n\\n"
definition+="\\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in prov["definition_open_context_facts"])+"\\n\\n"
definition+="\\n\\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in prov["definition_facts"])+"\\n\\nend "+NS+"\\n"
check("four_actual_Def_spans_and_parser_namespace_context_exact",definition.encode()==(OUT / "staged" / plan["local_definition"]).read_bytes(),{"proofs_in_new_Def":0,"source_defs":4})
check("fresh_new_native_and_staged_object_cache_not_borrowed",receipt["native_and_staged_objects_borrowed"] is False and not receipt.get("resumed_same_project_successful_steps"),{"project":"project","five_native_source_modules":True,"only_Mathlib_dependency_cache_shared":True})
failed_gate=load(OUT / "audit-gate-failed-attempt.json")
check("Python_splice_oracle_snapshot_failure_preserved",failed_gate["verdict"]=="FAIL" and failed_gate["error"]=="complete_original_Reflection_proof_core_and_all_three_parser_splices_exact" and sha(OUT / "audit_and_freeze.py.before-splice-oracle-fix")==failed_gate["original_audit_script_sha256"] and failed_gate["actual_proof_source_modified"] is False,{"retained":"audit-gate-failed-attempt.json","repair":"Select the actual executed Reflection parser snapshot instead of the PF generic snapshot; no mathematical or staged source change and no Lean recompilation."})
'''+s[b:]
replace('"retained_PartialFractions_source_declarations":32,"moved_genuine_Definitions":5,"inline_original_PartialFractions_proofs":27','"retained_Reflection_source_declarations":34,"moved_genuine_Definitions":4,"inline_original_Reflection_proofs":30')
a=s.index('limitations=');b=s.index('\nwrite(OUT / "README.md",readme)',a)
s=s[:a]+'''limitations=["The local coefficient sign reflection and the even-order rho cancellation keep the exact original Even n premise. Both concern genuine local formal coefficients for 1<=s<=9 and do not need properness. The rho_one endpoint needs the original StrongProperMultiplier degree condition and has no Even premise.","StrongProperMultiplier is 2*n+2*W.natDegree<=9*(n+1)-2. It is stronger than strict properness. The proof of rho1=0 uses the actual global PF polynomial identity and its coefficient at9*n+8, not a cancellation assumption.","For n=0,W=X^4 all even-order totals vanish but rho1=1, the actual weighted function is1/t, and StrongProper fails although strict properness holds. For n=1 all quartics are StrongProper and rho1=0 without Even n; even-n anti-reflection is not extended to odd n, with the original actual rational counterexample recompiled.","This batch is finite and formal over rational coefficients. It does not assert infinite Eq4/L convergence, a prescribed exact L, original five-dimensional aggregate F injectivity/inverse, denominator integrality, J or irrationality. Integer W does not automatically make every local rational coefficient an integer.","Reference stubs intentionally use sorryAx and are statements only. Complete solutions and inline helpers use only standard axioms. This author gate is separate from an independent transplantation review, parent root build and platform acceptance."]
readme="""# Actual reflection and coefficient totals offline author batch

Three exact frozen source endpoints are staged: local_coefficient_reflection, rho_even_order_zero and rho_one_zero_of_strong_proper. Lean4.33.1, Mathlib0df444a360eaa60ab8c11dca51a86af692955474. A prior independent native mathematical review is hash-bound; this author report does not claim independent transplantation review or platform acceptance.

Five original actual sources are freshly compiled in a new local project. The executed graph, five source parser/ref snapshots and Parser.parseHeader supply real source spans. Four unchanged actual definitions move to a lightweight Def importing the genuine Base/Jet/Injectivity/PF Def chain. Installed PF Def SHA74904aff5266f68b9d9f5c3013fb636f48d0cadda75e872093419845f9b666e5 is checked before project copy. All 30 original Reflection proofs are retained in each Solution; the genuine cross-source proof closure is inlined. Namespace open context comes from actual parser command spans. Only moved defs, diagnostics and mission header are removed; selected bindings/resolved references are renamed, then exact-signature wrappers are appended. No Theorems, Solutions or mission proof boundary is introduced.

All34 actual definition types/values agree across seven contexts (238 comparisons). Three original/Solution/reference endpoint types are identical, with no new binders or premises. Complete endpoints use propext, Classical.choice, Quot.sound. All source and inline helper proof records are separately checked for only standard axioms. Reference stubs deliberately contain sorryAx. compile-receipt.json retains actual exits/logs; any failed attempt is preserved rather than omitted.

The first two endpoints require Even n; their genuine local coefficient sign and even-order total cancellation need no properness. The rho1 endpoint requires StrongProper:2*n+2*W.natDegree<=9*(n+1)-2, without Even n. Its real proof uses the actual finite global PF polynomial identity. Original boundary statements are recompiled against the full staged rho1 Solution and compared exactly: n=0,W=X^4 has even totals0 but rho1=1/proper/notStrong/actual1/t; n=1 quartics are Strong with rho1=0, while the even-n anti-reflection claim fails for odd n. These conditions are kept in requests and theorem types.

No analytic formal-series evaluation, infinite Eq4/L convergence, prescribed exact L, original five-dimensional aggregate F injectivity/inverse, denominator integrality, J or irrationality is asserted by this finite batch. Only the new task-local batch/project is written. All prior four batches including PF frozen174files, mathematical sources, shared root and scope remain unchanged; API and credentials are not accessed. root-copy-plan.json provides source_sha256, seven new module sources and four genuine existing Def dependencies for the parent. Publication remains separate.

The first Python exact-splice gate selected the PF generic parser snapshot rather than the executed Reflection-specific snapshot. audit-gate-failed-attempt.json and the prior gate script retain that failed check and difference. The repair selects the correct actual Reflection parser file and verifies its34decl/178ref/56command counts. No source or staged proof byte changed, and all31Lean runs plus the59record boundary compilation had already passed.
"""
'''+s[b:]
(OUT / "audit_and_freeze.py").write_text(s,encoding="utf-8",newline="\n")
(OUT / "audit-recipe-provenance.json").write_text(json.dumps({"template":old.relative_to(TASK).as_posix(),"template_sha256":hashlib.sha256(old.read_bytes()).hexdigest(),"old_modified":False,"author_only":True,"changes":"Reflection author gate:5source/4defs/30proof,31runs,238def comparisons,original17check mathreview,515oldfrozenmembers,exact parser-owned open contexts and same source spans,59exactnativeboundaryrecords,finite Even/StrongProper limits."},indent=2)+"\n",encoding="utf-8")
print("Configured Reflection author gate only.")
