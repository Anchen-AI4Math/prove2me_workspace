from run_step import *
import ast,re,subprocess
verify();mechanical=load(OUT/'mechanical-checks.json');fresh=load(OUT/'fresh-source-compile-receipt.json');receipt=load(OUT/'review-compile-receipt.json');copy_plan=load(BATCH/'root-copy-plan.json')
assert fresh['complete'] and receipt['complete']
successful_review=[r for r in receipt['rows'] if r['exit_code']==0]
failed_review=[r for r in receipt['rows'] if r['exit_code']!=0]
assert [(r['label'],r['logical_step'],r['exit_code']) for r in failed_review]==[('r53','historical visible fallback actual rn resolver',1)]
assert 'BaseIO' in (OUT/failed_review[0]['log']).read_text(encoding='utf-8')
filtered=load(OUT/'filtered-path-replay.json')
assert filtered['status']=='PASS' and filtered['actual_filtered_Lean_successes']==5
assert filtered['all30_resolutions_exact_same_own_objects'] and filtered['root_proof_fallback_removed']
assert filtered['fresh_graph319_exact'] and filtered['native6_and_staged6_full_kernel_equalities_plus18_rfl_replayed']
assert filtered['old_successes_guarded_and_not_relabelled']
checks=list(mechanical['checks'])
def check(n,okay,evidence=None):
 checks.append({'name':n,'pass':bool(okay),'evidence':evidence})
 if not okay:
  dest=OUT/('retained-final-gate-failure-'+str(len(list(OUT.glob('retained-final-gate-failure-*.json')))+1).zfill(2)+'.json')
  dump(dest,{'failed_check':n,'checks':checks,'excluded':True});raise AssertionError(n)
standard={'propext','Classical.choice','Quot.sound'}
def step(name):
 xs=[r for r in receipt['rows'] if r['logical_step']==name];assert len(xs)==1;return xs[0]
def records(name):return rows(OUT/step(name)['log'])
for r in fresh['rows']:
 for k in ['log','exit_file','wrapper']:assert sha(OUT/r[k])==r[k+'_sha256']
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 if r['output_sha256']:assert sha(TASK/r['output_task_relative'])==r['output_sha256']
for r in receipt['rows']:
 for k in ['log','exit_file','wrapper','stdout_copy']:
  if r.get(k):assert sha(OUT/r[k])==r[k+'_sha256']
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 if r['output_sha256']:assert sha(TASK/r['output_task_relative'])==r['output_sha256']
check('all_successful_independent_actual_invocations_logs_objects_bound',True,{'fresh_original_successes':16,'fresh_original_failure_excluded':'s17 FS missing platform HS object','supplemental_and_review_successes':len(successful_review),'review_failure_excluded':'r53 IO versus BaseIO resolver probe'})
check('fresh_native9_pureHS_controls2_and_separate_platform_cache_objects_not_borrowed',fresh['successful_Lean_invocations']==25 and fresh['failed_dependency_scheduler_invocations']==1 and not receipt['native_and_staged_objects_borrowed'],{'cache_native':N.relative_to(TASK).as_posix(),'cache_platform':P.relative_to(TASK).as_posix()})
native={r['label']:r for r in records('actual fresh types_original.lean')}
defs=[r for r in native.values() if r['value'] is not None];assert len(defs)==55
context_names=['types_definition.lean']+[f'types_{i}_{k}.lean' for i in range(3) for k in ['solution','reference']]
reports={c:{r['label']:r for r in records('actual fresh '+c)} for c in context_names}
maps={'ZetaNine.CoefficientMapAggregate.'+n for n in ['aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']}
comparisons=[]
for d in defs:
 for c,rs in reports.items():
  r=rs[d['label']];equal=r['value']==d['value'];canonical=r['value']==reports['types_definition.lean'][d['label']]['value']
  assert r['type']==d['type'] and set(r['axioms'])<=standard
  if d['label'] not in maps:assert equal
  else:assert canonical
  comparisons.append({'declaration':d['label'],'context':c,'type_exact':True,'default_PP_value_exact':equal,'canonical_staged_default_PP_exact':canonical,'proof_bearing':d['label'] in maps})
ordinary=[r for r in comparisons if not r['proof_bearing']];qualified=[r for r in comparisons if r['proof_bearing']]
check('actual55Defs385_types_and52ordinary364_defaultPP_values_exact',len(comparisons)==385 and len(ordinary)==364 and all(r['default_PP_value_exact'] for r in ordinary),{'types':385,'ordinary_values':364})
check('three_proof_map_default_PP_differences_qualified',len(qualified)==21 and sum(not r['default_PP_value_exact'] for r in qualified)==7 and {r['declaration'] for r in qualified if not r['default_PP_value_exact']}=={'ZetaNine.CoefficientMapAggregate.coordinateLinearMap'},{'7_coordinate_differences':True,'14_apparent_PP_equalities_not_fullExpr_proof':True})
kernel_counts={}
for context in ['native','staged']:
 rs=records('fresh '+context+' Aggregate kernel full values six plus nine rfl');assert len(rs)==15
 ks=[r for r in rs if r['kind']=='actual_native_whole_kernel_value'];ps=[r for r in rs if r['kind']=='rfl_whole_or_data_equality']
 assert len(ks)==6 and len(ps)==9 and all(r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['pp_proofs'] and r['original_full_expr_repr'] and r['alias_full_expr_repr'] for r in ks)
 assert all(set(r['axioms'])<=standard for r in rs)
 kernel_counts[context]={'actual_whole_Meta_isDefEq':6,'whole_function_rfl':6,'data_rfl':3}
check('two_separate_environments_actual_native_alias_staged_full_value_kernel_equalities',True,kernel_counts)
alias_native=(PROJECT/'NativeValueComparisonDefinition.lean').read_bytes();alias_stage=(PROJECT/'StagedValueComparisonDefinition.lean').read_bytes()
assert alias_native.count(b'import missions.zeta9.formalization.CoefficientMapAggregate')==1
check('actual_shared_alias_program_differs_only_single_import',alias_native.replace(b'import missions.zeta9.formalization.CoefficientMapAggregate',b'import Definitions.Def_ZetaNine_CoefficientMapAggregate')==alias_stage,{'native_original_hash':sha(PROJECT/'NativeValueComparisonDefinition.lean')})
canonical={r['declaration']:r for r in records('canonical staged full map context 0')}
for i in range(7):
 rs=records('canonical staged full map context '+str(i));assert len(rs)==3
 for r in rs:
  c=canonical[r['declaration']];assert r['full_expression_repr']==c['full_expression_repr'] and r['type']==c['type'] and r['raw_value']==c['raw_value'] and r['pp_proofs'] and set(r['axioms'])<=standard
check('21_seven_context_fullExpr_canonical_propagations_exact_not21_native_calls',True,{'records':21,'native_direct_kernel_calls':6,'staged_direct_kernel_calls':6})
targets=[];plan=load(BATCH/'target-plan.json')
for i,t in enumerate(plan['targets']):
 n=t['theorem_name'];a=native[n];s=reports[f'types_{i}_solution.lean'][n];ref=reports[f'types_{i}_reference.lean'][n]
 assert a['type']==s['type']==ref['type'] and set(a['axioms'])==set(s['axioms'])==standard and 'sorryAx' in ref['axioms']
 targets.append({'theorem':n,'actual_original_type':a['type'],'actual_Solution_type':s['type'],'exact':True,'solution_axioms':s['axioms'],'reference_axioms':ref['axioms']})
check('three_original_Solution_reference_endpoint_types_exact_no_extra_hypotheses',True,targets)
proof_records=[]
for i in range(3):
 rs=records('actual fresh helpers_'+str(i)+'.lean');assert len(rs)==107 and all(set(r['axioms'])<=standard for r in rs);proof_records+=rs
native_proofs=records('actual106 native source and required helper proofs');assert len(native_proofs)==106 and all(set(r['axioms'])<=standard for r in native_proofs)
check('all321_Sol_true_proof_records_and106_native_required_proofs_standard_only',True,{'Sol_records':321,'each_Sol':107,'original':25,'genuine_helpers':81,'wrapper':1,'native_records':106})
source_controls=[r for r in fresh['rows'] if 'native control' in r['logical_step']]
native_baselines=[]
def map_selected(x):
 if isinstance(x,str):return x.replace('ZetaNine.CoefficientMapTelescoper.checked_actual_polynomial_quotient_degree_bound','ZetaNine.CoefficientMapTelescoper.actual_polynomial_quotient_degree_bound')
 if isinstance(x,list):return [map_selected(v) for v in x]
 if isinstance(x,dict):return {k:map_selected(v) for k,v in x.items()}
 return x
old_records=[load(TASK/'verification/formalization-coefficient-map-telescoper-2026-10-04/type-report.json'),load(TASK/'verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-boundary-types.json')]
for i,c in enumerate(source_controls):
 rs=rows(OUT/c['log']);expected=35 if i==0 else 54;assert len(rs)==expected
 staged=records('actual staged original control '+str(i));assert len(staged)==expected
 a={r['declaration']:r for r in rs};b={map_selected(r)['declaration']:map_selected(r) for r in staged};old={r['declaration']:r for r in old_records[i]}
 assert set(a)==set(b)==set(old)
 for n,r in a.items():assert r['type']==b[n]['type']==old[n]['type'] and r['definitionValue']==b[n]['definitionValue']==old[n]['definitionValue'] and set(r['axioms'])<=standard and set(b[n]['axioms'])<=standard
 native_baselines.append({'original_record_count':expected,'actual_staged_exact_count':expected,'all_closed':True})
check('all35_original_and54_independent_native_stage_control_records_exact',True,native_baselines)
own=records('eight independent own true numerator and root controls');assert len(own)==8 and all(set(r['axioms'])<=standard for r in own)
check('eight_additional_own_numerator_root_and_quotient_controls_actual_closed',True,own)
math=TASK/'verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-review.json';mr=load(math)
assert sha(math)=='cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a' and mr['verdict']=='PASS' and len(mr['checks'])==16 and len(mr['stable_files'])==150
for r in mr['stable_files']:assert sha(ROOT/r['root_relative'])==r['sha256'] and (ROOT/r['root_relative']).stat().st_size==r['bytes']
check('original_native_math_review16_checks150_bindings_exact_not_objects_reused',True)
agg=TASK/'formalization/platform/coefficient-map-aggregate/independent/independent-integration-review.json';ar=load(agg)
assert sha(agg)=='ff464d565f54cdcb8efd6445864fb278ed8ed0525c2b0fbab6fe158c96d5c24d' and ar['verdict']=='PASS'
for r in ar['stable_files']:assert sha(ROOT/r['root_relative'])==r['sha256'] and (ROOT/r['root_relative']).stat().st_size==r['bytes']
check('prior_Aggregate_independent_freeze771_bindings_unchanged',len(ar['stable_files'])==771)
check('root7files9existingDefs_and5build_check_receipts_exact',True,load(OUT/'frozen-handoff.json'))
check('supported_task_scoped_root_build_actual3810jobs0_oldTao2check1',True)
selected=load(OUT/'lean-path-selected.json')['LEAN_PATH'];parts=[Path(p).resolve() for p in selected.split(';') if p]
check('actual_selected_native_path_prefers_only_fresh_native_objects_without_root_proof_cache',parts[0]==N.resolve() and not any(p==(ROOT/'.lake/build/lib/lean').resolve() for p in parts),selected)
check('actual_filtered_native13_platform17_resolutions_all_own_objects_no_root_fallback',True,filtered)
check('filtered_graph_and_two_whole_kernel_environments_replayed_without_relabelling_history',True,{'actual_filtered_Lean_successes':5,'prior_unfiltered_successes_retained':True,'all30_objects_same_bytes':True,'graph319_exact':True})
check('failed_IO_BaseIO_path_probe_and_old_visible_path_gate_retained_excluded',len(failed_review)==1 and (OUT/'retained-final-gate-failure-01.json').exists(),{'Lean_failed_step':'r53','Lean_exit':1,'final_gate_failed_check':load(OUT/'retained-final-gate-failure-01.json')['failed_check'],'historical_root_fallback_visible_but_all30_actual_resolutions_own_cache':True})
runtime=load(OUT/'runtime-version-receipt.json');assert runtime['exit_code']==0 and sha(OUT/'runtime-version.log')==runtime['log_sha256'] and sha(OUT/'runtime-version-exit.txt')==runtime['exit_sha256'] and 'version 4.33.1' in (OUT/'runtime-version.log').read_text(encoding='utf-8')
assert (PROJECT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
lib=next(p for p in load(PROJECT/'lake-manifest.json')['packages'] if p['name']=='mathlib');assert lib['rev']=='0df444a360eaa60ab8c11dca51a86af692955474'
g=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True);write(OUT/'mathlib-revision.log',g.stdout+g.stderr);assert g.returncode==0 and g.stdout.decode().strip()==lib['rev']
check('actual_pinned_Lean_and_Mathlib_runtime_manifest_revision',True,{'Lean':'4.33.1','Mathlib':lib['rev']})
check('first_FS_import_scheduler_failure_retained_and_excluded_native_proofs_unchanged',fresh['rows'][-1]['exit_code']==1 and fresh['retained_failed_steps']==['s17'] and len(fresh['rows'])==17,{'successful_old_steps':16,'topology_correction_only':True,'fresh_project_not_reset':True})
check('input_paths_lt260_outputs_and_logs_reserve64_suffix',True,{'input_path_maximum':max(len(str(PROJECT/r['root_relative_destination'])) for r in copy_plan['files']),'initial_preflight_output_suffix_maximum':load(OUT/'output-path-preflight.json')['maximum_with_64_char_suffix'] if 'maximum_with_64_char_suffix' in load(OUT/'output-path-preflight.json') else 245})
for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
check('no_root_scope_API_credentials_mutation_only_current_task_and_actual_dependencies',True)
original_successful=[r for r in fresh['rows'] if r['exit_code']==0]
original_failed=[r for r in fresh['rows'] if r['exit_code']!=0]
assert len(original_successful)==16 and len(original_failed)==1 and len(successful_review)==59 and len(receipt['rows'])==60
summary={'independent_successful_Lean_invocations':len(original_successful)+len(successful_review),'runtime_version_invocations':1,'successful_actual_invocations_including_runtime':len(original_successful)+len(successful_review)+1,'retained_failed_Lean_invocations':len(original_failed)+len(failed_review),'fresh_source_successes':25,
 'original_proof_check_successes_including_runtime':69,'historical_actual_resolution_successes':2,'filtered_environment_replay_successes':5,'old_successes_not_relabelled':True,
 'graph_records':load(OUT/'extraction-summary.json')['actual_graph_records'],'sourceDefs':55,'type_comparisons':385,'ordinary_Def_PP_value_comparisons':364,'qualified_proof_map_context_records':21,
 'direct_native_full_Meta_comparisons':6,'direct_staged_full_Meta_comparisons':6,'closed_rfl_data_equalities':18,'Sol_proof_records':321,'native_required_proof_records':106,
 'original_author_boundary_records':35,'original_independent_boundary_records':54,'own_boundary_records':8,'root_build_jobs':3810}
dump(OUT/'actual-final-summary.json',summary);dump(OUT/'actual-Def-comparisons.json',comparisons)
fixed=[TASK/r['task_relative'] for r in load(BATCH/'source-manifest.json')['files']]+[BATCH/'source-manifest.json',BATCH/'SHA256SUMS.txt']
fixed += [BATCH/n for n in load(OUT/'frozen-handoff.json')['root_evidence_sha256']]
fixed += [ROOT/r['root_relative_destination'] for r in copy_plan['files']]+[ROOT/r['root_relative'] for r in copy_plan['required_existing_Definitions']]
fixed += [ROOT/r['root_relative'] for r in mr['stable_files']]+[math]+[ROOT/r['root_relative'] for r in ar['stable_files']]+[agg]
fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='independent-integration-review.json']
fixed += [p for p in BUILD.rglob('*') if p.is_file()]+[ROOT/'lean-toolchain',ROOT/'lake-manifest.json']
fixed=sorted(set(p.resolve() for p in fixed),key=lambda p:p.as_posix())
bindings=[]
for p in fixed:
 b={'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
 if p.is_relative_to(TASK):b['task_relative']=p.relative_to(TASK).as_posix()
 bindings.append(b)
report={'schema_version':1,'review_role':'independent platform transplantation reviewer; not native or platform author','verdict':'PASS','checks':checks,'counts':summary,'stable_files':bindings,
 'findings':[{'severity':'informational','topic':'proof_values','detail':'364 ordinary pretty values are exact. Three proof-bearing maps use six native plus six staged true kernel comparisons and eighteen closed rfl/data proofs through a shared actual alias. Their twenty-one context checks are canonical propagation, not twenty-one direct native calls.'},
 {'severity':'informational','topic':'failed_import_scheduler','detail':'The first independent FS Def build failed because platform HS/Reflection had not yet been compiled. Its source/log/exit was retained; sixteen successful steps were hash-bound in the same fresh cache, and only remaining modules were compiled in actual import order.'},
 {'severity':'informational','topic':'environment_history','detail':'Earlier successful executions had a visible Root proof-cache fallback. Actual findOLean probes selected all thirteen native and seventeen platform modules from the same independent cache, with every object hash-bound. After removing the fallback, five actual executions repeated both resolution probes, graph319, and both six-comparison/nine-rfl full-value environments. Earlier executions remain historical and are not relabelled as filtered or fresh. The initial IO/BaseIO probe failed with actual exit1 and is retained and excluded, as is the earlier environment final-gate failure.'},
 {'severity':'informational','topic':'scope','detail':'The true R difference, actual Q=P/M^9 and root factor/quotient degree are proved under their original conditions. Aggregate inverse, kernel triviality, J and zeta(9) irrationality are outside this verdict.'},
 {'severity':'informational','topic':'boundary','detail':'n0 X4 has zero aggregate but is not Strong; Q is empty and weightedR(1)=1. The difference endpoint keeps Even, Strong and aggregate zero; the representation endpoint has no Even/Strong/zero premise and retains n>=1 and regular points.'}],
 'root_scope_API_credentials_modified':False,'borrowed_native_or_staged_objects':False}
dump(OUT/'independent-integration-review.json',report)
for r in bindings:p=ROOT/r['root_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
print('Tel independent PASS',len(checks),'checks',len(bindings),'bindings; actual counts',summary,flush=True)
print('REPORT SHA256',sha(OUT/'independent-integration-review.json'),flush=True)
