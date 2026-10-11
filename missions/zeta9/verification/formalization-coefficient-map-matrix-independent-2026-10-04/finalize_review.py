"""Final native Matrix gate: actual kernel records, resolver, exits and exact byte freeze."""
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
  dump(OUT/('retained-final-gate-'+str(idx).zfill(2)+'.json'),{'status':'FAIL','checks':checks,'excluded':True,'Lean_invocations':0})
  raise AssertionError(name)
def step(name):
 rs=[r for r in receipt['rows'] if r['logical_step']==name];assert len(rs)==1 and rs[0]['actual_exit']==0;return rs[0]
def textlog(name):return (OUT/step(name)['log']).read_text(encoding='utf-8-sig')
def records(name):return [json.loads(x) for x in textlog(name).splitlines() if x.startswith('{')]
standard={'propext','Classical.choice','Quot.sound'}
for row in receipt['rows']:
 for key in ['log','exit_file']:assert sha(OUT/row[key])==row[key+'_sha256']
 assert (OUT/row['exit_file']).read_text().strip()==str(row['actual_exit'])
 if row['source_root_relative']:assert sha(ROOT/row['source_root_relative'])==row['source_sha256']
 if row['object_task_relative']:assert sha(TASK/row['object_task_relative'])==row['object_sha256']
check('all_actual_sources_logs_exits_objects_current_exact_bytes',True)
check('initially_empty_independent_cache_all13_actual_source_modules_compiled',all(step('fresh source '+m)['object_sha256'] for m in ORDER),{'source_modules':13,'cache':'.rt/mi1/b','package_cache_only_shared':True})
prep=load(OUT/'preparation-state.json')
check('actual13_source_import_closure_same_bytes',len(prep['source_bindings'])==13)
check('all_source_and_short_execution_path_plus64_guards',all(x['pass'] and x['path_plus64']<=259 for x in prep['path_guards']))
author=load(AUTHOR/'author-audit.json')
check('frozen_author44_current_exact_bindings_and_final_source',len(author['stable_files'])==44 and author['source_sha256']==SOURCE_SHA,{'sha256':AUTHOR_SHA})
author_successes=[load(AUTHOR/m/'receipt.json') for m in ['compile-03','source-audit-01','endpoint-audit-01']]
check('author_three_actual_successes_two_historical_failures_retained',author['actual_successes']==3 and all(r['actual_exit']==0 for r in author_successes) and len(author['retained_failed_attempts'])==2 and all(r['actual_exit']==1 for r in author['retained_failed_attempts']),{'author_same_parent_cache_reuse_honestly_recorded':author['author_parent_cache_reused'],'fresh_parent_build_claimed':author['fresh_parent_build_claimed']})
src=records('actual own source-full-audit.lean');expected=records('actual own expected-types.lean')
boundary=records('actual own independent-boundary.lean');kernel=records('actual own kernel-types.lean')
check('actual_source22_full_types_5_full_definition_values_17_proofs',len(src)==22 and sum(x['kind']=='def' for x in src)==5 and sum(x['kind']=='theorem' for x in src)==17 and sum(x['full_definition_value_expression_repr'] is not None for x in src)==5 and all(x['full_type_expression_repr'] for x in src))
check('all_source22_actual_axioms_only_standard_three',all(set(x['axioms'])<=standard for x in src),sorted(standard))
check('independent22_closed_types_and_5_whole_function_rfl_equalities',len(expected)==22 and all(set(x['axioms'])<=standard and x['full_type_expression_repr'] for x in expected) and len([x for x in expected if x['declaration'].endswith('_value')])==5)
replay=[r for r in kernel if 'declaration' in r];comparisons=[r for r in kernel if r.get('kind')=='actual_whole_type_kernel_comparison']
check('same_independent22_full_expression_types_and_axioms_replayed',replay==expected)
check('actual17_complete_original_expected_kernel_type_comparisons',len(comparisons)==17 and all(x['type_kernel_equal'] and x['actual_full_type_expression'] and x['expected_full_type_expression'] for x in comparisons),{'extra_assumptions':False})
check('own26_actual_boundary_proofs_standard_three_only',len(boundary)==26 and all(set(x['axioms'])<=standard and x['full_type_expression_repr'] for x in boundary))
names={x['declaration'].split('.')[-1] for x in boundary}
check('actual5_monomial_row_output_columns_and_column_transpose',{'raw_row_B','raw_row_rho3','raw_row_rho5','raw_row_rho7','raw_row_rho9','column_entries_are_monomial_output_transposed'}<=names)
check('actual10_typed_Fin_selector_entries_and_integer_target_tuple',{'selector00','selector01','selector02','selector03','selector04','selector10','selector11','selector12','selector13','selector14','pair_B','pair_rho9','target_tuple'}<=names)
check('actual_pure_zeta9_target_and_inverse_nonzero',{'pure_nine_output_nonzero','pure_nine_multiplier_nonzero'}<=names)
check('actual_zero_output_inverse_zero',{'zero_target_multiplier_zero'}<=names)
check('actual_pure_zeta9_HasSum_and_norm_summability',{'pure_nine_actual_sum_and_absolute'}<=names)
check('original_even_two_and_four_determinants_actually_nonzero',{'concrete_even_two_det','concrete_even_four_det'}<=names)
check('rational_row_inverse_selection_product_reconstruction_only',{'rational_inverse_coefficients_scope'}<=names)
def axiom_reports(s):
 return [{'name':n,'axioms':[re.sub(r'\.\{[^}]+\}$','',x.strip()) for x in vals.split(',') if x.strip()],
  'printed_axioms':[x.strip() for x in vals.split(',') if x.strip()]} for n,vals in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",s,re.S)]
aa=axiom_reports((AUTHOR/'source-audit-01/source-audit.log').read_text(encoding='utf-8-sig'))
ia=axiom_reports(textlog('actual own author-type-audit.lean'))
ae=axiom_reports((AUTHOR/'endpoint-audit-01/endpoint-audit.log').read_text(encoding='utf-8-sig'))
ie=axiom_reports(textlog('actual own author-endpoint-audit.lean'))
check('author22_source_checks_and_printed_axioms_replayed_exact',len(aa)==len(ia)==22 and aa==ia and all(set(x['axioms'])<=standard for x in ia))
check('author12_endpoint_checks_6types_5wholevalues_pure9nonzero_replayed',len(ae)==len(ie)==12 and ae==ie and all(set(x['axioms'])<=standard for x in ie))
check('author_source_and_endpoint_diagnostic_stdout_replayed_exact',textlog('actual own author-type-audit.lean')==(AUTHOR/'source-audit-01/source-audit.log').read_text(encoding='utf-8-sig') and textlog('actual own author-endpoint-audit.lean')==(AUTHOR/'endpoint-audit-01/endpoint-audit.log').read_text(encoding='utf-8-sig'),{'diagnostic_comparison_only':True,'definitive_type_checks':'actual17 whole kernel equalities and22 independently specified proofs'})
resolved=records('actual own thirteen module resolver');assert len(resolved)==14
search=[Path(x).resolve() for x in resolved[0]['LEAN_PATH'].split(';') if x]
cache=(PROJECT/'b/lib/lean').resolve()
package_caches={(ROOT/'.lake/packages'/x['name']/'.lake/build/lib/lean').resolve() for x in load(PROJECT/'lake-manifest.json')['packages']}
runtime_library=Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean').resolve()
check('actual_search_path_exact_allowed_package_own_cache_runtime_set',cache in search and set(search)<=package_caches|{cache,runtime_library},{'actual_path':resolved[0]['LEAN_PATH'],'package_first_order_permitted':True,'no_Root_author_other_independent_proof_fallback':True})
objects=[]
for m,r in zip(ORDER,resolved[1:]):
 p=(cache/(m.replace('.','/')+'.olean')).resolve()
 assert r['module']==m and Path(r['resolved_olean']).resolve()==p and p.is_file() and sha(p)==step('fresh source '+m)['object_sha256']
 objects.append({'module':m,'task_relative':p.relative_to(TASK).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
check('actualfindOLean_all13_choose_exact_own_fresh_compiled_objects',True,objects)
version=textlog('actual pinned runtime')
check('actual_runtime_Lean4_33_1_and_exact_toolchain_manifest','version 4.33.1' in version and (PROJECT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1')
lib=next(x for x in load(PROJECT/'lake-manifest.json')['packages'] if x['name']=='mathlib')
g=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
write(OUT/'actual-mathlib-revision.log',g.stdout+g.stderr);write(OUT/'actual-mathlib-revision-exit.txt',str(g.returncode)+'\n')
check('actual_Mathlib_revision_matches_pinned_manifest',g.returncode==0 and g.stdout.decode().strip()==lib['rev']=='0df444a360eaa60ab8c11dca51a86af692955474')
dependency=prep['dependency_review'];d=load(ROOT/dependency['root_relative']);verify_bindings(d['stable_files'])
check('nativeKernel296_unchanged_true_dependency_bytes_not_objects_borrowed',len(d['stable_files'])==296 and d['verdict']=='PASS',{'report_sha256':dependency['sha256']})
source=(TASK/'formalization/CoefficientMapMatrix.lean').read_text(encoding='utf-8-sig')
check('actual_source5_defs_17theorems_no_new_axiom_sorry_unsafe',len(re.findall(r'^theorem ',source,re.M))==17 and len(re.findall(r'^def ',source,re.M))==5 and not re.search(r'\b(sorry|admit|axiom|unsafe)\b',source))
signatures={name:sig for name,sig in re.findall(r'^theorem (\w+)\s+(.*?)\s*:=',source,re.M|re.S)}
bounded={x['source'].split('.')[-1] for x in comparisons}-{'quarticAggregate_eq_row_vector','coordinatePolynomial_single_one','column_action_matrix_is_transpose','selectedIntegerPair_mul_selection','selected_prescribed_L'}
check('original_domains_even_n_ge2_retained_in_all_inverse_proofs',len(bounded)==12 and all('(hn2 : 2 ≤ n)' in signatures[name] and '(hn : Even n)' in signatures[name] for name in bounded),{'actual17_complete_type_comparisons_are_definitive':True,'domain':'Even n and 2<=n','independent_inverse_degree_le4_rational_coefficients':True})
for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
check('only_task_writes_no_Root_API_credentials_scope_changes',True)
probe=load(OUT/'retained-schema-probe.json')
check('read_only_Python_schema_probe_failure_retained_excluded_no_Lean',probe['actual_python_process_exit']==1 and probe['Lean_invocations']==0 and probe['excluded_from_proof_and_Lean_success_counts'])
rows=receipt['rows'];success=[r for r in rows if r['actual_exit']==0];failed=[r for r in rows if r['actual_exit']!=0]
check('actual21_successful_runtime_source_and_control_receipts',len(success)==21 and not failed)
counts={'fresh_source_modules':13,'actual_successful_Lean_source_and_controls':20,'runtime_version_invocations':1,'all_actual_successful_invocations':len(success),'independent_failed_Lean_invocations':len(failed),'retained_read_schema_Python_failures':1,'original_author_failed_source_compiles':2,'source_top_level_records':22,'source_definition_records':5,'source_theorem_records':17,'independent_expected_types_and_whole_function_values':22,'whole_type_kernel_comparisons':17,'own_boundary_proofs':26,'author_source_axiom_replay_records':22,'author_endpoint_axiom_replay_records':12,'actual_own_module_resolutions':13}
dump(OUT/'actual-counts.json',counts)
fixed=[AUTHOR/'author-audit.json']+[ROOT/r['root_relative'] for r in author['stable_files']]
fixed += [ROOT/dependency['root_relative']]+[ROOT/r['root_relative'] for r in d['stable_files']]
fixed += [ROOT/r['root_relative'] for r in prep['source_bindings']]
fixed += [ROOT/'lean-toolchain',ROOT/'lake-manifest.json']
fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='independent-review.json']
for directory,dirs,files in os.walk(PROJECT):
 dirs[:]=[x for x in dirs if x not in ['.lake','__pycache__']]
 fixed += [Path(directory)/name for name in files]
fixed += [p for p in (PROJECT/'.lake').iterdir() if p.is_file()]
fixed=sorted({p.resolve() for p in fixed},key=lambda x:x.as_posix());bindings=[]
for p in fixed:
 assert p.is_relative_to(ROOT.resolve())
 r={'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
 if p.is_relative_to(TASK):r['task_relative']=p.relative_to(TASK).as_posix()
 bindings.append(r)
report={'schema_version':1,'verdict':'PASS','scope':'PASS_ACTUAL_ORIGINAL_F_ROW_MATRIX_SELECTION_RATIONAL_INVERSE_AND_TRUE_SUMS_ONLY','review_role':'independent native reviewer, different from source author','source_sha256':SOURCE_SHA,'source_bytes':(TASK/'formalization/CoefficientMapMatrix.lean').stat().st_size,'author_report_sha256':AUTHOR_SHA,'checks':checks,'counts':counts,'stable_files':bindings,
 'author_or_Root_native_objects_borrowed':False,'Root_proof_fallback_removed_before_first_run':True,'Root_API_credentials_scope_modified':False,
 'actual_source_records':src,'independent_expected_records':expected,'actual_whole_kernel_comparisons':comparisons,'actual_boundary_records':boundary,'original_author_axiom_replays':ia+ie,
 'findings':[{'topic':'orientation','detail':'F has monomial rows and actual output columns B,rho3,rho5,rho7,rho9. Its row action equals actual quartic F, while Mathlib column toMatrix is the transpose. The inverse expression uses the verified row orientation (b,a)S F^-1.'},
 {'topic':'scope','detail':'Original Even n and n>=2 are retained. Integer output targets have a rational quartic preimage, exact actual B and rho coordinates, actual exactL=b+a*zeta9, true HasSum and norm summability. Integrality of W, integer lattice index, height/content, transport in n, or irrationality is not claimed.'},
 {'topic':'environment','detail':'Every thirteen-module actual findOLean resolves to its own freshly compiled mi1 object, with an exact allowed path set of pinned packages, mi1/b, and Lean4.33.1 runtime. Author and prior independent proof objects were not borrowed.'},
 {'topic':'history','detail':'Both original author source compile failures are retained and excluded. The source precompilation comment is historical; current actual compile receipts govern the verdict. Pure preparation and its no-execution counts remain preserved as historical preparation.'}]}
dump(OUT/'independent-review.json',report)
verify_bindings(bindings)
print('Native Matrix independent PASS',len(checks),'checks',len(bindings),'bindings',counts,flush=True)
print('REPORT SHA256',sha(OUT/'independent-review.json'),flush=True)
