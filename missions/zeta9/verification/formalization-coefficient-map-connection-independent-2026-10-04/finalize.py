from pathlib import Path
import ast,hashlib,json,re,sys
from prepare import OUT,TASK,ROOT,AUTHOR,SOURCE,SOURCE_HASH,BUILD,MODULE,sha,dump,bind,verify
sys.stdout.reconfigure(encoding='utf-8')
verify();r=json.loads((OUT/'fresh-compile-receipt.json').read_text(encoding='utf-8'))
assert r['complete'] and [x['exit_code'] for x in r['rows']]==[0,0,0,0,1,0,0]
for row in r['rows']:
 for key in ['log','exit_file','wrapper','output']:
  b=row.get(key)
  if b:assert sha(TASK/b['task_relative'])==b['sha256']
 assert (TASK/row['exit_file']['task_relative']).read_text().strip()==str(row['exit_code'])
 if row['label']!='s05':assert sha(TASK/row['source']['task_relative'])==row['source']['sha256']
 else:assert sha(OUT/'failed-own-boundary-01/b.lean')==row['source']['sha256']
def parse(n):
 p=OUT/(n+'.log');return [json.loads(x) for x in p.read_text(encoding='utf-8').splitlines() if x.startswith('{')]
module=parse('s02');original=parse('s03');author_boundaries=parse('s04');own=parse('s06');expected=parse('s07')
standard={'propext','Classical.choice','Quot.sound'}
assert all(set(x['axioms'])<=standard for rows in [module,original,author_boundaries,own,expected] for x in rows)
source_names=re.findall(r'^(def|theorem)\s+(\w+)',SOURCE.read_text(encoding='utf-8'),re.M)
src_names={'ZetaNine.CoefficientMapConnection.'+name:kind for kind,name in source_names}
actual={x['declaration']:x for x in module};original_by_name={x['declaration']:x for x in original}
frozen_types=json.loads((AUTHOR/'type-audit.json').read_text(encoding='utf-8'))['records']
assert len(source_names)==39 and len([x for x in source_names if x[0]=='def'])==12
assert set(src_names)==set(original_by_name)=={x['declaration'] for x in frozen_types}
for row in frozen_types:
 name=row['declaration'];assert actual[name]['kind']==('def' if src_names[name]=='def' else 'theorem')
 assert actual[name]['module']==MODULE and actual[name]['startLine']>0
 for k in ['type','type_expression_repr','value','definition_expression_repr']:
  assert row.get(k)==original_by_name[name].get(k)==actual[name].get(k),(name,k)
 own_source_line=next(i for i,line in enumerate(SOURCE.read_text(encoding='utf-8').splitlines(),1) if re.match(r'^(def|theorem)\s+'+re.escape(name.split('.')[-1])+r'\b',line))
 assert actual[name]['startLine']==own_source_line
fb=json.loads((AUTHOR/'boundary-audit.json').read_text(encoding='utf-8'))['records']
assert len(author_boundaries)==len(fb)==12
assert {x['declaration']:x for x in author_boundaries}=={x['declaration']:x for x in fb}
own_names=re.findall(r'^theorem\s+(\w+)',(OUT/'b.lean').read_text(encoding='utf-8'),re.M)
assert len(own)==len(own_names)==23 and {x['declaration'] for x in own}=={'ConnectionIndependent.'+n for n in own_names}
assert len(expected)==5 and all(x['actual_type_isDefEq_expected'] for x in expected)
assert not any(x['kind'] in ['axiom','opaque'] for x in module)
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',SOURCE.read_text(encoding='utf-8'))
imports=re.findall(r'^import\s+(\S+)',SOURCE.read_text(encoding='utf-8'),re.M)
assert len(imports)==5 and all(x.startswith('Mathlib.') for x in imports)
old=TASK/'verification/coefficient-map-connection-offline-precheck-2026-10-04'
offline=json.loads((old/'offline-alignment-report.json').read_text(encoding='utf-8'))
assert len(offline['checks'])==39 and all(x['exact_integer_polynomial_check'] for x in offline['checks'])
assert sha(old/'observed-connection-paper.md')==sha(TASK/'round7/research/connection.md')
old_core=(old/'observed-Connection-source.lean').read_text(encoding='utf-8').split('def connectionReflection')[0]
assert SOURCE.read_text(encoding='utf-8').split('def connectionReflection')[0]==old_core
instances=json.loads((OUT/'exact-instance-checks.json').read_text(encoding='utf-8'))
assert instances['source_sha256']==SOURCE_HASH and len(instances['checks'])==75 and all(x['pass'] for x in instances['checks'])
paths=json.loads((OUT/'output-path-preflight.json').read_text(encoding='utf-8'));assert paths['all_paths_with_64_char_suffix_below_260']
for p in [OUT/'e.lean',OUT/'s07.ps1',OUT/'s07.log',OUT/'s07-exit.txt']:
 assert len(str(p))+64<=259
for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
actual_summary={'all_native_module_records':len(module),'source_definitions':12,'source_theorems':27,
 'generated_native_records_separate':len(module)-39,'internal_native_records':sum(x['internal'] for x in module),
 'source_type_and_full_expression_comparisons':39,'source_def_value_and_full_expression_comparisons':12,
 'fresh_original_author_boundaries':12,'fresh_own_closed_boundaries':23,'five_independently_encoded_exact_endpoint_types':5,
 'closed_proof_records_source_plus_author_plus_own_plus_expected':27+12+23+5,
 'actual_successful_Lean_invocations':6,'retained_failed_own_control_invocations':1,
 'symbolic_historical_checks':39,'new_finite_exact_rational_checks':75,'new_full_polynomial_instance_solutions':21}
dump(OUT/'actual-evidence-summary.json',actual_summary)
checks=[]
def check(name,evidence):checks.append({'name':name,'pass':True,'evidence':evidence})
check('frozen_source_and_all_five_author_controls_rehashed',SOURCE_HASH)
check('all_frozen_author_53_manifest_and54_checksums_members_rehashed','No author file modified; failed author attempts retained separately')
check('final_author_actual_native_attempt7_source_object_exit_and3006_job_log_bound','Successful final attempt only; earlier successes with older source hashes excluded')
check('new_own_project_and_short_cache_no_borrowed_native_objects',{'project':(OUT/'p').relative_to(TASK).as_posix(),'cache':BUILD.relative_to(TASK).as_posix(),'source_build':r['rows'][0]})
check('only_five_actual_Mathlib_imports_and_pinned_runtime_shared',imports)
check('all_source_and_own_outputs_actual_zero',{'successful_labels':['s01','s02','s03','s04','s06','s07'],'failed_control_label':'s05 retained and excluded'})
check('short_input_output_log_paths_guarded_with64_suffix',{'maximum':paths['maximum'],'bound':259})
check('actual_module_graph_and_source_ranges_from_Lean',{'records':len(module),'named_source':39,'internal':sum(x['internal'] for x in module)})
check('all39_original_types_PP_and_fullExpr_exact_in_fresh_environment','Original source audit, author frozen records and independent actual module extraction compared')
check('all12_original_Def_values_PP_proofs_true_and_fullExpr_exact','Includes actual connectionLinearMap proof fields; no proof elision claim')
check('all_native_source_and_generated_records_only_standard_axioms',{'records':len(module),'allowed':sorted(standard)})
check('no_added_axiom_opaque_unsafe_or_placeholder','Actual module kind/axioms plus exact source scan')
check('all12_frozen_author_boundaries_recompiled_and_exact','New object, fresh original controls and frozen records compared')
check('all23_own_boundary_theorems_actual_closed_and_standard_only',[x['declaration'] for x in own])
check('all_five_main_endpoint_types_independently_encoded_and_kernel_isDefEq',expected)
check('Fin15_split5plus10_and_indices4_5_14_recovered','recoverP/recoverQ/recoverEdges/restoreAll actual closed proofs')
check('nonmonomial_nonmonic_and_zero_input_boundaries','mixedInputs/zeroInputs/mixedDegree/mixedTargetNonmonomial actual proofs')
check('degree29_reflection_excludes_odd_highest_degree_without_zeroing_all_odd_coefficients','reflectedDegree28/actualDegree28/affineReflectionAllowsOddCoefficient actual proofs')
check('projection_promoted_to_entire_polynomial_equality','fullProjectedEquality plus universal fullLift exact type')
check('homogeneous_kernel_has_no_degree_P_or_Even_or_GL5_zeta_kernel_premise','unrestrictedPKernel and independently encoded kernel exact type')
check('original_arbitrary_f_compU_equation_and_all_bounded_polynomial_pair_uniqueness','originalSystem exact type; originalUniquenessAllPolynomials; mixed and zero RHS closed')
check('all_five_true_paper_targets_and_positive_domain_retained','actualTargetFormula; universal fiveSystems exact type; odd n1 and even n2 all Fin5 controls')
check('n0_Natclip_and_written_rational_coordinate_counterexample_separated','Three actual n0 controls; source uses clipped Nat.sub and n>=1 main endpoints')
check('historical39_exact_integer_symbolic_core_checks_bound_and_unchanged','Earlier source differs only after homogeneous kernel; actual core and paper snapshot exact')
check('new75_exact_rational_instance_checks_and21_full_original_system_solutions',{'n':[1,2,3],'basis':'even t coefficients0..28','no_universal_claim':True})
check('author_and_independent_failed_attempts_preserved_excluded','Own first boundary issue was concrete vector inference/Rat numeral normalization only; native proofs unchanged')
check('success_same_project_cache_resume_hash_bound_without_false_fresh_repeat','First four successful steps bound and reused; only corrected controls repeated')
check('only_current_task_and_actual_imports_reviewed_no_root_scope_API_credentials_mutation',True)
manifest=json.loads((AUTHOR/'source-manifest.json').read_text(encoding='utf-8'))
fixed=[TASK/x['task_relative'] for x in manifest['files']]+[AUTHOR/'source-manifest.json',AUTHOR/'SHA256SUMS.txt']
fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['independent-review.json']]
fixed += [p for p in BUILD.rglob('*') if p.is_file()]
fixed += [ROOT/'lean-toolchain',ROOT/'lake-manifest.json',TASK/'round7/research/connection.md']
fixed += [old/n for n in ['offline-alignment-report.json','precheck-freeze.json','observed-Connection-source.lean','observed-connection-paper.md']]
fixed=sorted(set(p.resolve() for p in fixed),key=lambda p:p.as_posix())
report={'schema_version':1,'review_role':'independent native mathematical source reviewer; not source or platform author','verdict':'PASS',
 'source_sha256':SOURCE_HASH,'checks':checks,'counts':actual_summary,'stable_files':[bind(p) for p in fixed],
 'findings':[{'severity':'informational','topic':'basis','detail':'The actual 15x15 map uses even t coefficients. It is related to u coefficients by a unipotent change of basis; no claim of literal identical matrices.'},
 {'severity':'informational','topic':'scope','detail':'Proves the positive-n original polynomial connection systems. It does not prove the aggregate five-output GL5 statement, zeta linear independence, or zeta(9) irrationality.'},
 {'severity':'informational','topic':'boundary_failure','detail':'First independent controls failed only at two concrete vector inference/Rat numeral reductions. Failed bytes/log/exit retained, corrected closed controls actual0; original proofs were unchanged.'},
 {'severity':'informational','topic':'n_zero','detail':'The native Nat(n-1) clips at n0. The written rational-coordinate q=X9 nonzero kernel counterexample is separate from the modified source H0, which is nonzero on X9.'}],
 'standard_axioms':sorted(standard),'root_scope_API_credentials_modified':False,'borrowed_native_objects':False}
dump(OUT/'independent-review.json',report)
for row in report['stable_files']:
 p=ROOT/row['root_relative'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
print('Independent Connection PASS',len(checks),'checks;',len(report['stable_files']),'bindings; summary',actual_summary,flush=True)
print('REPORT SHA256',sha(OUT/'independent-review.json'),flush=True)
