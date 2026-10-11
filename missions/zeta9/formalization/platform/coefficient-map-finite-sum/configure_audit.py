"""Configure author-only finite-sum gates from the frozen Reflection schema."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2]
OLD=TASK/'formalization/platform/coefficient-map-reflection/audit_and_freeze.py'
s=OLD.read_text(encoding='utf-8-sig')
def replace(a,b):
 global s
 assert a in s,a
 s=s.replace(a,b)
replace('CoefficientMapReflection','CoefficientMapFiniteSum')
replace('coefficient-map-reflection','coefficient-map-finite-sum')
replace('ac3d8f135cb3c69b39074548bea712f418fa6d0273ad27e33805374c1db20123','a4d2cec35a3e9b506aed7a0df0b2afacce4adf07a5b03f42b713b9726b581386')
replace('len(math["checks"])==17','len(math["checks"])==15')
replace('all_thirty_one_actual_author_runs_exit_zero','all_thirty_eight_actual_author_runs_exit_zero')
replace('len(receipt["rows"])==31','len(receipt["rows"])==38')
replace('"native_source_compilation":1,"official_graph_and_parser_and_header_runs":7,"staged_source_builds_including_actual_existing_Definitions":11',
 '"native_source_compilation":6,"official_graph_and_parser_and_header_runs":8,"staged_source_builds_including_actual_existing_Definitions":12')
replace('all_thirty_four_actual_definition_types_and_values_equal','all_thirty_six_actual_definition_types_and_values_equal')
replace('len(definitions)==34 and len(comparisons)==238','len(definitions)==36 and len(comparisons)==252')
replace('"Reflection":4,"exact_actual_comparisons":238','"FiniteSum":4,"HarmonicStability":2,"exact_actual_comparisons":252')
replace('per=31+len(prov["inline_helper_names"])','per=8+len(prov["inline_helper_names"])')
replace('all_original_thirty_proofs_cross_module_closure_and_wrapper_standard_axioms','all_original_seven_proofs_cross_module_closure_and_wrapper_standard_axioms')
replace('prov["source_declarations"]==34 and prov["source_defs"]==4 and prov["source_proofs"]==30','prov["source_declarations"]==11 and prov["source_defs"]==4 and prov["source_proofs"]==7')
a=s.index('check("Even_n_and_strong_bound_and_both_boundary_prose_faithful"');b=s.index('\nold_members=0',a)
s=s[:a]+'''check("proper_finite_identity_retains_actual_rho_one_and_all_Nat_shift_prose",all(text in req["problems"][i]["natural_language_statement"] for i,text in [(0,"strict proper"),(0,"$T=0$"),(1,"simple-pole term"),(1,"retained"),(1,"$\\\\rho_{0,1}=1$"),(1,"odd/no-simple wrappers"),(2,"$s=0$"),(2,"$T=0$"),(2,"$j=0$")]))
check("native_independent_finite_only_exact_domains_bound",math["actual_finite_harmonic_identity_closed"] and math["actual_grouped_finite_identity_closed"] and not math["reflection_cancellation_closed"] and not math["rho1_zero_without_added_condition_closed"] and not math["infinite_sum_convergence_closed"] and not math["original_aggregate_F_inverse_closed"] and not math["exact_L_closed"])
check("four_existing_base_chain_and_one_actual_Harmonic_Def_stage_root_bytes_identical",len(plan["existing_definitions"])==5 and all(sha(ROOT / d["root_relative"])==d["sha256"]==sha(TASK / d["task_relative"])==sha(PROJECT / d["root_relative"]) for d in plan["existing_definitions"]),plan["existing_definitions"])
check("pure_HarmonicStability_exact_source_no_proof_boundary",prov["pure_HarmonicStability_sha256"]=="5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92" and prov["pure_HarmonicStability_parser_decl_count"]==2 and sha(OUT / "HarmonicStability-oracle-input.lean")==prov["pure_HarmonicStability_sha256"] and math["pure_harmonic_definition"]["same_actual_harmonicPower_body_as_original"] is True)
'''+s[b:]
replace('"coefficient-map-partial-fractions"]:','"coefficient-map-partial-fractions","coefficient-map-reflection"]:')
replace('all_515_old_author_frozen_members_unchanged','all_687_old_author_frozen_members_unchanged')
replace('old_members==515','old_members==687')
replace('"PartialFractions_frozen_members":174','"PartialFractions_frozen_members":174,"Reflection_frozen_members":172')
replace('import Definitions.Def_ZetaNine_CoefficientMapFiniteSum\\nimport Mathlib.Tactic\\n\\n\\n','import Definitions.Def_ZetaNine_CoefficientMapFiniteSum\\nimport Mathlib.Tactic\\nimport Mathlib.Algebra.BigOperators.Intervals\\n\\n')
replace('ZetaNine.CoefficientMapPartialFractions\\n','ZetaNine.CoefficientMapPartialFractions ZetaNine.HarmonicStability\\n')
replace('complete_original_Reflection_proof_core_and_all_three_parser_splices_exact','complete_original_FiniteSum_proof_core_and_all_three_parser_splices_exact')
replace('exact_Reflection_parser_snapshot_selected','exact_FiniteSum_parser_snapshot_selected')
replace('=={"decl":34,"ref":178,"command":56}', 'and prov["source_fact_counts"]["decl"]==11')
replace('len(prov["deleted_diagnostic_facts"])==11','len(prov["deleted_diagnostic_facts"])==6')
replace('"original_proofs_retained_per_Sol":30','"original_proofs_retained_per_Sol":7')
replace('.checked_rho_one_zero_of_strong_proper','.checked_actual_grouped_finite_identity')
replace('.rho_one_zero_of_strong_proper','.actual_grouped_finite_identity')
a=s.index('boundary_comparisons=[]');b=s.index('\ndefinition=',a)
s=s[:a]+'''boundary_comparisons=[]
extra_names={"fs_stage_difference_T_zero","fs_stage_difference_j_zero","fs_stage_difference_s_zero","fs_stage_harmonicPower_s_zero"}
for r in boundary["records"]:
    name=r["declaration"].replace(".checked_actual_grouped_finite_identity",".actual_grouped_finite_identity")
    if name in extra_names:
        assert set(r["axioms"])<=STD
        continue
    orig=native_byname[name]
    boundary_comparisons.append({"declaration":r["declaration"],"native_type_exact":orig["type"]==r["type"],"native_definition_value_exact":orig["definitionValue"]==r["definitionValue"],"axioms":r["axioms"]})
check("staged_finite_simple_pole_and_zero_order_shift_boundaries_actual_compile",boundary["exit_code"]==0 and (OUT / "stage-boundary-audit-exit.txt").read_text().strip()=="0" and len(boundary_comparisons)==40 and len(boundary["records"])==44 and extra_names<={r["declaration"] for r in boundary["records"]} and boundary["all_standard_axioms"] and all(r["native_type_exact"] and r["native_definition_value_exact"] for r in boundary_comparisons),{"records":44,"exact_original_native_records":40,"new_all_Nat_shift_boundaries":4,"all_axioms":sorted(STD)})
'''+s[b:]
replace('definition="import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\n\\n\\n',
 'definition="import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\nimport Definitions.Def_ZetaNine_HarmonicStability\\nimport Mathlib.Algebra.BigOperators.Intervals\\n\\n')
a=s.index('failed_gate=load(');b=s.index('\ncopyfiles=[]',a)
s=s[:a]+s[b:]
replace('"retained_Reflection_source_declarations":34,"moved_genuine_Definitions":4,"inline_original_Reflection_proofs":30',
 '"retained_FiniteSum_source_declarations":11,"moved_genuine_Definitions":4,"inline_original_FiniteSum_proofs":7')
a=s.index('limitations=');b=s.index('\nwrite(OUT / "README.md",readme)',a)
s=s[:a]+'''limitations=["The two actual rational finite-sum endpoints retain the actual strict ProperMultiplier condition. All coefficients come from the original weighted formal local series, positive integer sample denominators are automatically regular, and sums are finite.","The grouped public endpoint retains the genuine rho1*harmonicPower1T term. Original conditional no-simple/odd proof wrappers remain inside the exact source core with their explicit actual rho inputs, but are not public selected endpoints and are not used to claim unconditional cancellation.","The harmonic difference endpoint is for all natural s,T,j, including s0,T0,j0, with the exact unchanged existing harmonicPower definition. Empty intervals and s0 are actually recompiled.","n0W=X4 is a genuine strict-proper example with rho1=1, B0=tail0=0, actualR(t)=1/t and finiteL=harmonicPower1T. Strict properness gives no rho1 cancellation or infinite L convergence.","This batch uses five actual sources and the actual pure HarmonicStability Def, with no Reflection, Summation, aggregate, inverse or irrationality input. It contains no infinite sum, prescribed target, denominator-integrality or aggregate inverse claim.","This is an author gate, not an independent transplantation review or platform acceptance. Reference stubs use sorryAx deliberately; complete Solutions and all real inline proofs use only standard axioms. Parent handles root installation/build/publication separately."]
readme="""# Actual finite harmonic sums offline author batch

Three actual endpoints are staged: actual_finite_harmonic_identity, actual_grouped_finite_identity and harmonic_difference_eq_shifted. The two weighted rational finite identities keep strict ProperMultiplier and the grouped formula retains rho1*H_T. The harmonic difference is for every natural s,T,j including0. All original seven FS proofs are retained, including conditional internal wrappers with their original rho inputs; those wrappers are not selected public endpoints.

Fresh project/cache compiles five actual native source modules and the unchanged pure HarmonicStability Definition. Official Stage1 includes the actual five-source module prefix plus that exact pure Definition module; Stage2 executes six parser snapshots and the leaf header. Four genuine source definitions move by actual declaration spans. All required real cross-source proof helpers and actual namespace-open spans are copied, with no theorem stub or native mission boundary import. Only actual moved defs, header and diagnostics are deleted; selected binding/ref spans are renamed and exact-signature solution wrappers appended.

All36 actual definitions (Base9,Jet9,Inject7,PF5,FS4,Harmonic2) have exact types and values across seven contexts,252 comparisons. Three original/Sol/reference types are exact with no new assumptions. Complete proof records use standard axioms; statement references deliberately contain sorryAx. Four pre-existing Base/Jet/Inject/PF Defs plus the exact Harmonic Def are hash-checked at root and copied into this new project.

Original40 native audit/boundary records are recompiled against the complete staged grouped Solution with exact statement/value equality. Four additional T0/j0/s0/harmonicPower0 checks close all-Nat boundaries. n0X4 remains actual1/t with rho1=1, B=tail=0 and finiteL=H_T; omitting the simple-pole term would be false. No Reflection proof or infinite convergence, exact target L, five-dimensional aggregate inverse or irrationality is imported or inferred.

The author receipt records actual observed calls/exits/logs. Actual compiled objects and source bytes are bound in the freeze. All old author freezes remain unchanged. No root/scope/API/credential writes. This author PASS is separate from independent transplantation review, supported root task build and platform acceptance.
"""
'''+s[b:]
key='# Source/config/oracle/log/request evidence only; never recurse through .lake packages.'
replace(key,'''# Bind actual compiled objects, source and observed exit files without changing prior rows.
objects=[]
for r in receipt["rows"]:
    ex=OUT / (r["label"]+"-exit.txt")
    assert int(ex.read_text().strip())==r["exit_code"]==0
    r["exit_file"]=ex.name;r["exit_file_sha256"]=sha(ex)
    if r["command"][:3]==["lake","--no-cache","build"]:
        module=r["command"][3]
        obj=PROJECT / ".lake/build/lib/lean" / (module.replace(".","/")+".olean")
        src=PROJECT / (module.replace(".","/")+".lean")
        assert obj.exists() and src.exists()
        r["compiled_object_project_relative"]=obj.relative_to(PROJECT).as_posix();r["compiled_object_sha256"]=sha(obj)
        r["compiled_source_project_relative"]=src.relative_to(PROJECT).as_posix();r["compiled_source_sha256"]=sha(src)
        objects.append(obj)
receipt["observed_exit_files_and_compiled_objects_bound"]=True
dump(OUT / "compile-receipt.json",receipt)
'''+key)
replace('stable+=list((OUT / "staged").rglob("*.lean"))','stable+=list((OUT / "staged").rglob("*.lean"))+list((OUT / "dependencies").rglob("*.lean"))+list(dict.fromkeys(objects))')
(OUT/'audit_and_freeze.py').write_text(s,encoding='utf-8',newline='\n')
(OUT/'audit-recipe-provenance.json').write_text(json.dumps({'template':OLD.relative_to(TASK).as_posix(),
 'template_sha256':hashlib.sha256(OLD.read_bytes()).hexdigest(),'old_modified':False,'author_only':True,
 'changes':'FS finite endpoints;5actual sources+pureHarmonic;38actual calls;36defs252comparisons;all7proofs;40original+4new boundary records;7rootcopy/5existingDef requirements;compiled objects and exit files bound.'},indent=2)+'\n',encoding='utf-8')
print('Configured finite-sum author gate only; no Lean started.')
