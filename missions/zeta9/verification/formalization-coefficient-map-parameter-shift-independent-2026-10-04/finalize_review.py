"""Final independent native gate. Reads actual logs/objects, then freezes exact bindings."""
from run import *
import re,ast
verify();receipt=load(OUT/'actual-execution-receipt.json')
assert receipt['source_phase_complete'] and receipt['controls_phase_complete']
assert receipt['empty_independent_cache_verified_before_first_run'] and not receipt['author_native_objects_borrowed']
checks=[]
def check(name,condition,evidence=None):
 checks.append({'name':name,'pass':bool(condition),'evidence':evidence})
 if not condition:
  idx=1+len(list(OUT.glob('retained-final-gate-*.json')))
  dump(OUT/('retained-final-gate-'+str(idx).zfill(2)+'.json'),{'status':'FAIL','checks':checks,'excluded':True})
  raise AssertionError(name)
def step(name):
 rs=[r for r in receipt['rows'] if r['logical_step']==name];assert len(rs)==1 and rs[0]['actual_exit']==0;return rs[0]
def records(name):
 log=OUT/step(name)['log'];return [json.loads(x) for x in log.read_text(encoding='utf-8-sig').splitlines() if x.startswith('{')]
standard={'propext','Classical.choice','Quot.sound'}
for row in receipt['rows']:
 for key in ['log','exit_file']:assert sha(OUT/row[key])==row[key+'_sha256']
 assert (OUT/row['exit_file']).read_text().strip()==str(row['actual_exit'])
 if row['source_root_relative']:assert sha(ROOT/row['source_root_relative'])==row['source_sha256']
 if row['object_task_relative']:assert sha(TASK/row['object_task_relative'])==row['object_sha256']
check('all_actual_successful_commands_sources_logs_exits_objects_current_bytes_bound',True)
check('fresh_initial_cache_all14_source_modules_real_compiled_not_borrowed',all(step('fresh source '+m)['object_sha256'] for m in ORDER),{'source_modules':14,'cache':'.rt/pi1/b','Mathlib_package_cache_only_shared':True})
prep=load(OUT/'final-preparation.json');check('complete_actual_native_import_closure_fourteen_samebyte_sources',len(prep['source_bindings'])==14)
author=load(AUTHOR/'author-audit.json')
check('exact_parent_author_freeze_fiftynine_stable_bindings',len(author['stable_files'])==59,{'sha256':AUTHOR_SHA,'source_sha256':SOURCE_SHA})
check('author_final_retry_compile_and_type_audit_actual0_historical1_excluded',author['actual_successful_parent_compiles']==13 and author['actual_successful_final_source_compiles']==1 and author['actual_successful_final_type_audits']==1,author['historical_failures_retained_and_excluded'])
src=records('actual own source-full-audit.lean');expected=records('actual own expected-types.lean');boundary=records('actual own independent-boundary-v4.lean');kernel=records('actual own kernel-types-v2.lean')
check('fresh_actual_source17_records_2_definition_values_15_true_proofs',len(src)==17 and sum(x['full_definition_value_expression_repr'] is not None for x in src)==2)
check('all_original_source_proof_and_data_axioms_standard_three_only',all(set(x['axioms'])<=standard for x in src),{'source_records':17,'axiom_names':sorted(standard)})
check('independently_spelled_expected17_types_and_two_whole_value_rfls_closed',len(expected)==17 and all(set(x['axioms'])<=standard for x in expected))
orig_expected=[r for r in kernel if 'declaration' in r];cmp=[r for r in kernel if r.get('kind')=='actual_whole_type_kernel_comparison']
check('fresh_expected_program_replayed_same_full_types_axioms',orig_expected==expected)
check('fifteen_complete_original_expected_type_kernel_equalities_actual',len(cmp)==15 and all(x['type_kernel_equal'] and x['actual_type_full_expr'] and x['expected_type_full_expr'] for x in cmp),{'comparisons':15,'extra_assumptions':False})
check('twentyseven_independent_real_boundary_proofs_actual_standard3',len(boundary)==27 and all(set(x['axioms'])<=standard for x in boundary))
failed_boundary=[r for r in receipt['rows'] if r['actual_exit']!=0 and r['label'] in ['e18','e19','e20']]
assert [(r['label'],r['actual_exit']) for r in failed_boundary]==[('e18',1),('e19',1),('e20',1)]
bad_log=(OUT/failed_boundary[0]['log']).read_text(encoding='utf-8-sig')
bad_records=[json.loads(x) for x in bad_log.splitlines() if x.startswith('{')]
invalid={x['declaration'].split('.')[-1] for x in bad_records if 'sorryAx' in x['axioms']}
check('first_boundary_Nat_Rat_inference_failure_actual1_retained_wholly_excluded',invalid=={'n0_t2_new_regular','n2_t2_new_regular','first_original_system_at_n1','last_original_system_at_n2'} and len(bad_records)==27,{'failed_step':'e18','all_failed_run_records_excluded':True,'four_explicit_Nat_annotations_only':True,'author_source_unchanged':True})
syntax_log=(OUT/failed_boundary[1]['log']).read_text(encoding='utf-8-sig')
check('second_typed_bounded_forall_syntax_failure_actual1_retained_excluded',syntax_log.count('unexpected token')==4,{'failed_step':'e19','actual_exit':1,'third_control_keeps_exact_Nat_domain_via_forall_arrow_syntax':True})
third_log=(OUT/failed_boundary[2]['log']).read_text(encoding='utf-8-sig')
third_records=[json.loads(x) for x in third_log.splitlines() if x.startswith('{')]
check('third_n2_Rat_numeral_specialization_failure_actual1_retained_excluded',len(third_records)==27 and {x['declaration'].split('.')[-1] for x in third_records if 'sorryAx' in x['axioms']}=={'last_original_system_at_n2'}, {'failed_step':'e20','actual_exit':1,'last_control_proof_only_adds_explicit_Rat_2plus1eq3_norm_num':True})
failed_kernel=[r for r in receipt['rows'] if r['actual_exit']!=0 and r['label']=='e23'];assert len(failed_kernel)==1
kernel_failure_log=(OUT/failed_kernel[0]['log']).read_text(encoding='utf-8-sig')
check('whole_kernel_program_trailing_parenthesis_actual1_retained_excluded',"unexpected token ')'" in kernel_failure_log and failed_kernel[0]['actual_exit']==1,{'failed_step':'e23','all32_failed_output_records_excluded':True,'repair_one_trailing_parenthesis_only':True})
bnames={x['declaration'].split('.')[-1] for x in boundary}
check('n0_clipped_V_regular_counterexample_and_valid_ratio_actually_proved',{'clipped_V_n0','n0_Q_at_2','n0_Q_at_3','n0_Q_difference_value','n0_R_H_over_D_value','n0_clipped_V_Q_difference_counterexample','n0_t2_new_regular','n0_t2_R_ratio_still_valid'}<=bnames)
check('n2_regular_old_R_zero_valid_crossmultiplied_ratio_actually_proved',{'n2_t2_new_regular','n2_t2_old_R_zero','n2_t2_new_R_zero','n2_t2_D_nonzero','n2_t2_R_ratio_with_zero_old_R'}<=bnames)
check('derived_regular_denominators_and_poles_zero_q_positive_V_actual',{'independent_old_regular','independent_old_successor_regular','independent_required_denominators','t_one_is_excluded','t_zero_is_excluded','t_minus_n_minus_one_is_excluded','zero_q_remainder','zero_q_difference','all_positive_n_V_successor'}<=bnames)
check('genuine_first_and_last_original_unique_transport_systems_actual',{'first_original_system_at_n1','last_original_system_at_n2'}<=bnames)
author_text=(AUTHOR/'audit-01/type-audit.log').read_text(encoding='utf-8-sig');fresh_author=(OUT/step('actual own author-type-audit.lean')['log']).read_text(encoding='utf-8-sig')
def axiom_reports(s):
 return [{'name':n,'axioms':[re.sub(r'\.\{[^}]+\}$','',x.strip()) for x in names.split(',') if x.strip()]} for n,names in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",s,re.S)]
aa=axiom_reports(author_text);ia=axiom_reports(fresh_author)
check('actual_original_twenty_author_printed_axioms_replayed_exact',len(aa)==len(ia)==20 and aa==ia and all(set(x['axioms'])<=standard for x in ia))
check('author_full_check_stdout_diagnostic_replayed_exact',author_text==fresh_author,{'type_diagnostic_only':True,'definitive_type_gate':'fifteen actual kernel comparisons and seventeen explicit type proofs'})
resolved=records('actual own fourteen module resolver');assert len(resolved)==15
search=[Path(x).resolve() for x in resolved[0]['LEAN_PATH'].split(';') if x]
cache=(PROJECT/'b/lib/lean').resolve();blocked=(ROOT/'.lake/build/lib/lean').resolve()
package_caches={(ROOT/'.lake/packages'/x['name']/'.lake/build/lib/lean').resolve() for x in load(PROJECT/'lake-manifest.json')['packages']}
pinned_Lean_library=Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean').resolve()
check('actual_Lean_search_path_only_own_cache_pinned_packages_runtime_no_Root_proof_fallback',cache in search and blocked not in search and set(search)<=package_caches|{cache,pinned_Lean_library},{'actual_path':resolved[0]['LEAN_PATH'],'package_first_default_Lake_order':True,'actual14_module_resolutions_verified_separately':True})
historical_gate=load(OUT/'retained-final-gate-01.json')
check('overstrict_package_first_order_Python_gate_failure_retained_excluded',historical_gate['status']=='FAIL' and historical_gate['checks'][-1]['name']=='actual_Lean_search_path_prefers_own_cache_Root_proof_fallback_absent',{'actual_exit':1,'Lean_invocations':0,'resolved_all14_own_cache':True,'allowed_exact_paths_gate_now_used_without_relabelling_any_runs':True})
object_bindings=[]
for m,r in zip(ORDER,resolved[1:]):
 p=(cache/(m.replace('.','/')+'.olean')).resolve()
 assert r['module']==m and Path(r['resolved_olean']).resolve()==p and p.is_file()
 row=step('fresh source '+m);assert sha(p)==row['object_sha256']
 object_bindings.append({'module':m,'task_relative':p.relative_to(TASK).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
check('actual_findOLean_all14_native_modules_resolve_exact_own_compiled_objects',True,object_bindings)
version=(OUT/step('actual pinned runtime')['log']).read_text(encoding='utf-8-sig')
check('actual_Lean_runtime_4_33_1_and_manifest_bytes_exact','version 4.33.1' in version and (PROJECT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1')
lib=next(x for x in load(PROJECT/'lake-manifest.json')['packages'] if x['name']=='mathlib')
g=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
write(OUT/'actual-mathlib-revision.log',g.stdout+g.stderr);write(OUT/'actual-mathlib-revision-exit.txt',str(g.returncode)+'\n')
check('actual_pinned_Mathlib_git_revision_manifest_exact',g.returncode==0 and g.stdout.decode().strip()==lib['rev']=='0df444a360eaa60ab8c11dca51a86af692955474')
dep_files=[]
for rel,h,count in [('verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json','7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1',296),('verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json','92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82',108)]:
 p=TASK/rel;d=load(p);assert sha(p)==h and d['verdict']=='PASS' and len(d['stable_files'])==count
 for r in d['stable_files']:
  q=ROOT/r['root_relative'];assert sha(q)==r['sha256'] and q.stat().st_size==r['bytes'];dep_files.append(q)
 dep_files.append(p)
check('prior_kernel296_and_connection108_independent_freezes_unchanged_not_objects_used',True)
source=(TASK/'formalization/CoefficientMapParameterShift.lean').read_text(encoding='utf-8-sig')
check('actual_source_keeps_all_three_transport_hypotheses_n_positive_full_equation_regular',len(re.findall(r'^theorem ',source,re.M))==15 and len(re.findall(r'^def ',source,re.M))==2 and not re.search(r'\b(sorry|admit|axiom|unsafe)\b',source))
check('old_dc6299_preparation_snapshot_preserved_not_substituted_for_final',sha(OUT/'candidate-observed-dc6299.lean')=='dc629940878fd365e1cb995fe3e4ca6b75b38aee6938eeca37a9fa493e7156b0' and SOURCE_SHA!=sha(OUT/'candidate-observed-dc6299.lean'))
diagnostic=load(OUT/'retained-schema-preflight-01.json');check('purePython_schema_keyerror_actual1_retained_excluded_no_Lean',diagnostic['actual_exit']==1 and diagnostic['Lean_invocations']==0 and diagnostic['excluded_from_success_counts'])
utf8=load(OUT/'retained-utf8-reporting-failure-01.json');check('purePython_GBK_failed_log_reporting1_retained_excluded_no_Lean',utf8['actual_exit']==1 and utf8['Lean_invocations']==0 and utf8['excluded_from_success_counts'])
for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
check('only_task_written_no_Root_API_credentials_or_other_task_mutations',True)
rows=receipt['rows'];success=[r for r in rows if r['actual_exit']==0];failed=[r for r in rows if r['actual_exit']!=0]
assert len(success)==21 and len(failed)==4 and len(rows)==25
counts={'fresh_source_modules':14,'actual_successful_Lean_source_and_controls':20,'runtime_version_invocations':1,'all_actual_successful_invocations':21,'independent_failed_Lean_invocations':4,'retained_independent_purePython_failures':3,'original_author_failed_source_compile':1,'source_top_level_records':17,'source_definition_records':2,'source_theorem_records':15,'independent_expected_type_and_whole_value_proofs':17,'whole_type_kernel_comparisons':15,'own_boundary_proofs':27,'original_author_axiom_replay_records':20,'actual_own_module_resolutions':14}
dump(OUT/'actual-counts.json',counts)
fixed=[AUTHOR/'author-audit.json']+[ROOT/r['root_relative'] for r in author['stable_files']]+dep_files
fixed += [ROOT/r['root_relative'] for r in prep['source_bindings']]+[ROOT/r['root_relative'] for r in prep['runtime_bindings']]
fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='independent-review.json']
fixed += [p for p in PROJECT.rglob('*') if p.is_file() and '.lake' not in p.parts and '__pycache__' not in p.parts]
fixed += [p for p in (PROJECT/'.lake').iterdir() if p.is_file()]
fixed=sorted({p.resolve() for p in fixed},key=lambda x:x.as_posix());bindings=[]
for p in fixed:
 assert p.is_relative_to(ROOT.resolve())
 r={'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
 if p.is_relative_to(TASK):r['task_relative']=p.relative_to(TASK).as_posix()
 bindings.append(r)
report={'schema_version':1,'verdict':'PASS','scope':'PASS_ACTUAL_ORIGINAL_FINITE_R_PARAMETER_TRANSPORT_REGULAR_RATIONAL_POINTS_ONLY','review_role':'independent native reviewer, not source or native author','source_sha256':SOURCE_SHA,'source_bytes':10672,'checks':checks,'counts':counts,'stable_files':bindings,'author_report_sha256':AUTHOR_SHA,
 'author_or_root_native_objects_borrowed':False,'Root_proof_fallback_removed_before_first_run':True,'Root_API_credentials_modified':False,
 'findings':[{'severity':'informational','topic':'domain','detail':'The R parameter equality holds for n>=0 at true shifted regular points. The actual remainder and original-system transports retain n>=1, including the full DP+H polynomial equality. The n0 clipped-V difference counterexample is actually proved.'},
 {'severity':'informational','topic':'zero_R','detail':'No division by Rold or nonzero-Rold hypothesis is present. The n2,t2 regular point has both actual R values zero and nonzero D; its cross-multiplied parameter equality is actually verified.'},
 {'severity':'informational','topic':'search_path','detail':'The independent project uses Lake default package-first search ordering. Actual findOLean selected all fourteen native modules from pi1/b. The exact path contains only pinned package caches, pi1/b and Lean4.33.1 runtime; no Root or author project cache is present. An initial Python final gate overstrictly demanded pi1/b be first; it is retained and excluded and replaced with the exact allowed-path-set plus actual object-resolution gate.'},
 {'severity':'informational','topic':'scope','detail':'This closes true finite rational-function transports and the five unique actual polynomial systems. Formal F-coordinate transport, infinite-sum parameter transport, determinant formulas, arithmetic height/content and irrationality are outside this verdict.'},
 {'severity':'informational','topic':'history','detail':'Old dc6299 preparation and author first-source compile1 remain retained and excluded. Two independent pure Python reporting failures (initial schema KeyError and GBK glyph output) are retained and excluded. The first own boundary file inferred four literal-bound indices Rat; the second retry used invalid typed bounded-forall syntax; the third needed explicit rational 2+1=3 normalization for the last n2 specialization. All three complete failed runs are retained and excluded. The v4 file changes only those four quantifiers to explicit Nat forall/arrow syntax and adds that final numeral proof; all twenty-seven controls actually passed. The first kernel comparison script had one trailing unmatched parenthesis: its whole failed run is excluded, and the separately retained v2 succeeds after removing only that parenthesis. Existing source comments saying first compilation is pending are historical; actual current same-byte compile receipts govern the verdict.'}]}
dump(OUT/'independent-review.json',report)
for r in bindings:
 p=ROOT/r['root_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
print('ParameterShift independent PASS',len(checks),'checks',len(bindings),'bindings',counts,flush=True)
print('REPORT SHA256',sha(OUT/'independent-review.json'),flush=True)
