"""Finalize only after actual fresh builds, graph and byte reconstruction."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
HERE=Path(__file__).resolve().parent;BATCH=HERE.parent;TASK=BATCH.parents[2];ROOT=TASK.parents[1];PROJECT=HERE/'project'
NS='ZetaNine.CoefficientMapInjectivity';STD={'propext','Classical.choice','Quot.sound'}
TARGETS=['all_local_coefficients_zero_implies_zero','fullLocalCoefficientMap_injective','quartic_is_proper']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def write(p,s):p.write_text(s,encoding='utf-8',newline='\n')
reconstruction=load(HERE/'reconstruction-report.json');checks=reconstruction['checks']
def check(n,okay,e=None):
    checks.append({'name':n,'pass':bool(okay),'evidence':e});assert okay,n
receipt=load(HERE/'compile-receipt.json')
check('all_29_final_independent_native_oracle_staged_type_helper_runs_observed_zero',receipt.get('complete') is True and len(receipt['rows'])==30 and sum(r['exit_code']==0 for r in receipt['rows'])==29 and all(sha(HERE/r['log'])==r['log_sha256'] for r in receipt['rows']) and [r['label'] for r in receipt['rows'] if r['exit_code']!=0]==['build-staged-1'] and receipt['fresh_project_without_objects_at_start'] and not receipt['native_or_staged_olean_borrowed'],{'observed_runs':len(receipt['rows']),'successful_runs':29,'retained_initial_output_path_failure':1,'native_sources':3,'staged_Definitions_including_dependencies':3,'full_Solutions':3,'references':3,'type_value_reports':8,'helper_reports':3,'actual_oracles':5,'pinned_dependency_cache_only':True})
check('initial_long_output_failure_preserved_short_exact_source_recompile_succeeded',len(receipt['retained_failed_attempts'])==1 and receipt['retained_failed_attempts'][0]['exit_code']==1 and (HERE/'build-staged-1-exit.txt').read_text().strip()=='1' and 'failed to create file' in (HERE/'build-staged-1.log').read_text(encoding='utf-8-sig') and len([r for r in receipt['rows'] if r['label'].endswith('-short-output') and r['exit_code']==0])==6 and all(sha(HERE/r['source'])==sha(PROJECT/r['destination'])==r['sha256'] for r in receipt['independent_object_copies']),receipt['retained_failed_attempts'])
env=os.environ.copy();env.pop('LEAN_PATH',None)
p=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True,env=env)
(HERE/'mathlib-revision.log').write_bytes(p.stdout+p.stderr)
check('Lean_4_33_1_and_actual_pinned_Mathlib_revision','version 4.33.1' in (HERE/'toolchain.log').read_text(encoding='utf-8-sig') and p.returncode==0 and p.stdout.decode().strip()=='0df444a360eaa60ab8c11dca51a86af692955474')
original={r['label']:r for r in rows(HERE/'types_original.log')}
contexts=['types_definition']+[f'types_{i}_{kind}' for i in range(3) for kind in ['solution','reference']]
reports={k:{r['label']:r for r in rows(HERE/(k+'.log'))} for k in contexts}
definitions=[r for r in original.values() if r['value'] is not None]
comparisons=[]
for d in definitions:
    for k,rs in reports.items():
        got=rs[d['label']]
        comparisons.append({'declaration':d['label'],'context':k,'type_equal':d['type']==got['type'],'value_equal':d['value']==got['value'],'axioms':got['axioms']})
check('all_25_actual_Base_Jet_Inject_definition_types_values_175_comparisons_exact',len(definitions)==25 and len(comparisons)==175 and all(r['type_equal'] and r['value_equal'] and set(r['axioms'])<=STD for r in comparisons),{'definitions':25,'contexts':7,'type_value_pairs':175})
target_evidence=[]
for i,n in enumerate(TARGETS):
    full=NS+'.'+n;orig=original[full];sol=reports[f'types_{i}_solution'][full];ref=reports[f'types_{i}_reference'][full]
    target_evidence.append({'theorem':full,'actual_original_type':orig['type'],'original_solution_reference_type_equal':orig['type']==sol['type']==ref['type'],'original_axioms':orig['axioms'],'solution_axioms':sol['axioms'],'reference_axioms':ref['axioms']})
check('three_exact_original_Solution_reference_types_no_extra_premise',all(r['original_solution_reference_type_equal'] for r in target_evidence),target_evidence)
check('all_three_complete_proofs_exact_standard_three_axioms',all(set(r['original_axioms'])==set(r['solution_axioms'])==STD for r in target_evidence))
helper_reports=[rows(HERE/f'helpers_{i}.log') for i in range(3)]
check('all_78_inline_proof_records_standard_axioms_only',all(len(rs)==26 and all(set(r['axioms'])<=STD for r in rs) for rs in helper_reports),{'records':sum(map(len,helper_reports)),'each':'18 original Inject proofs + 1 actual Base proof + 6 actual Jet proofs + wrapper'})
check('reference_sorryAx_explicit_Solutions_do_not_import_stub_or_mission',all('sorryAx' in r['reference_axioms'] for r in target_evidence) and all(not any(line.startswith(('import Theorems.','import Solutions.','import missions.')) for line in (BATCH/'staged'/('Solutions/Sol_ZetaNine_CoefficientMapInjectivity_'+n+'.lean')).read_text(encoding='utf-8').splitlines()) for n in TARGETS))
def canon(rs):return sorted(json.dumps({**r,'axioms':sorted(r['axioms'])},sort_keys=True,ensure_ascii=False) for r in rs)
for k in ['types_original']+contexts:
    check(k+'_eight_author_actual_full_name_type_value_reports_recomputed',canon(rows(HERE/(k+'.log')))==canon(rows(BATCH/(k+'.log'))))
for i in range(3):check('helpers_'+str(i)+'_author_actual_proof_report_recomputed',canon(helper_reports[i])==canon(rows(BATCH/f'helpers_{i}.log')))

# Re-import the previous independently proved closed-domain and counterexamples
# into the actual transplanted Solution context. Only import and selected-name
# substitutions change; the previous boundary proofs are otherwise byte exact.
native_review_path=TASK/'verification/formalization-coefficient-map-injectivity-2026-10-03/independent-review.json'
native_review=load(native_review_path)
check('prior_16_check_actual_native_mathematical_review_hash_bound',sha(native_review_path)=='a271a7c004845f9151f79c7779cea6c451337d65890922fd8a15dae9a5aea747' and native_review['verdict']=='PASS' and len(native_review['checks'])==16 and all(r['pass'] for r in native_review['checks']))
boundary_original=TASK/'verification/formalization-coefficient-map-injectivity-2026-10-03/independent-boundary-audit.lean'
boundary_text=boundary_original.read_text(encoding='utf-8-sig')
old='import missions.zeta9.formalization.CoefficientMapInjectivity'
assert boundary_text.count(old)==1
boundary_text=boundary_text.replace(old,'import Solutions.Sol_ZetaNine_CoefficientMapInjectivity_quartic_is_proper').replace('quartic_is_proper','checked_quartic_is_proper')
# The blanket identifier replacement also touched the import; restore its
# module spelling without modifying a mathematical declaration or proof.
boundary_text=boundary_text.replace('import Solutions.Sol_ZetaNine_CoefficientMapInjectivity_checked_quartic_is_proper','import Solutions.Sol_ZetaNine_CoefficientMapInjectivity_quartic_is_proper')
write(PROJECT/'boundary_transplanted.lean',boundary_text)
p=subprocess.run(['lake','env','lean','boundary_transplanted.lean'],cwd=PROJECT,env=env,capture_output=True)
(HERE/'boundary_transplanted.log').write_bytes(p.stdout+p.stderr);write(HERE/'boundary_transplanted-exit.txt',str(p.returncode)+'\n')
boundary_rows=rows(HERE/'boundary_transplanted.log')
closed=[r for r in boundary_rows if r['declaration'].startswith('independent_')]
check('actual_transplanted_closed_domain_and_n_zero_boundary_audit_exit_zero',p.returncode==0 and len(closed)==16 and all(set(r['axioms'])<=STD for r in closed),{'Lean_exit':p.returncode,'closed_boundary_records':len(closed),'source':boundary_original.relative_to(TASK).as_posix(),'original_bytes_sha256':sha(boundary_original),'only_changes':'native import -> actual complete quartic Solution; selected quartic theorem identifier -> checked name','log_sha256':sha(HERE/'boundary_transplanted.log')})
byboundary={r['declaration']:r for r in closed}
check('n_zero_X4_strict_proper_simple_pole_not_stronger_gap_preserved',all(k in byboundary for k in ['independent_n_zero_quartic_proper','independent_n_zero_nonzero_simple_pole','independent_n_zero_quartic_no_two_degree_gap','independent_n_zero_actual_simple_pole']),{k:byboundary[k]['type'] for k in ['independent_n_zero_quartic_proper','independent_n_zero_nonzero_simple_pole','independent_n_zero_quartic_no_two_degree_gap','independent_n_zero_actual_simple_pole']})
check('n_zero_X5_nonzero_zero_local_array_outside_domain_preserves_necessity',all(k in byboundary for k in ['independent_n_zero_nonproper_kernel','independent_n_zero_nonproper_nonzero','independent_n_zero_nonproper_bound']),{k:byboundary[k]['type'] for k in ['independent_n_zero_nonproper_kernel','independent_n_zero_nonproper_nonzero','independent_n_zero_nonproper_bound']})

dreq=load(BATCH/'definitions-request.json')[0];preq=load(BATCH/'problems-request.json')
dfields={'definition_name','definition_title','definition','natural_language_statement','source','tags','env','private'}
pfields={'theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source','tags'}
check('offline_public_payload_documented_fields_only',set(dreq)<=dfields and {'definition_name','definition_title','definition'}<=set(dreq) and set(preq)=={'env','private','problems'} and all(set(p)<=pfields and p['formal_statement'].endswith(':= by sorry') and len(p['theorem_title'])<=200 for p in preq['problems']),{'API_calls':False,'local_schema':'formalization/platform/readback-2026-10-03/api-docs/references/contribute.md'})
check('public_prose_correct_full_array_proper_domain_no_aggregate_inverse_L_claim','five aggregated' in preq['problems'][0]['natural_language_statement'] and 'No surjectivity' in preq['problems'][1]['natural_language_statement'] and 'including zero' in preq['problems'][2]['natural_language_statement'] and '$1/t$' in preq['problems'][2]['natural_language_statement'])
check('native_review_keeps_original_aggregate_F_inverse_L_and_irrationality_open',all(native_review[k] is False for k in ['original_aggregated_F_injectivity_closed','original_aggregated_F_inverse_closed','stronger_uniform_O_one_over_t_squared_closed','rho1_zero_closed','exact_L_closed','J_closed','irrationality_closed']))
plan=load(BATCH/'root-copy-plan.json');install=load(BATCH/'root-install-receipt.json')
installed=[]
for f in plan['files']:
    p=ROOT/f['root_relative_destination']
    installed.append({'root_relative':f['root_relative_destination'],'sha256':sha(p),'expected':f['sha256'],'bytes':p.stat().st_size})
check('seven_installed_root_files_exact_frozen_stage_bytes',len(installed)==7 and all(r['sha256']==r['expected'] for r in installed))
check('actual_existing_Base_and_Jet_Definitions_exact',len(plan['required_existing_Definitions'])==2 and all(sha(ROOT/f['root_relative'])==sha(TASK/f['task_relative'])==f['sha256'] for f in plan['required_existing_Definitions']),plan['required_existing_Definitions'])
check('parent_install_receipt_and_scoped_build_observed_success_hash_bound',install['frozen_author_audit_sha256']==sha(BATCH/'author-audit.json') and install['frozen_root_copy_plan_sha256']==sha(BATCH/'root-copy-plan.json') and install['results']=={'check':1,'build':0} and install['root_bytes_match_frozen_stage'] and not install['full_F_invertibility_proved'] and (BATCH/'task-build-exit.txt').read_text().strip()=='0' and 'Build completed successfully' in (BATCH/'task-build.log').read_text(encoding='utf-8-sig'),{'parent_root_build_jobs':3760,'root_check_exit':1,'check_pass_claimed':False})
expected_other=['ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean; add it to a mission scope.json','ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2.lean; add it to a mission scope.json']
check('task_scope_check_only_two_preexisting_other_mission_errors',(BATCH/'task-check-exit.txt').read_text().strip()=='1' and (BATCH/'task-check.log').read_text(encoding='utf-8-sig').splitlines()==expected_other,{'not_modified_by_reviewer':True})
hashes={}
for line in (BATCH/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
    h,rel=line.split('  ',1);p=(BATCH/rel).resolve();assert p.is_relative_to(TASK) and sha(p)==h;hashes[p.relative_to(TASK).as_posix()]=h
check('134_frozen_members_rechecked_after_all_fresh_proof_and_boundary_runs',len(reconstruction['frozen_manifest_members'])==134 and sha(BATCH/'SHA256SUMS.txt')=='d04da22546da82edfbdc68949573e71359ebaef5542f93d3e12b44df21edccb2')
old_counts={}
for name in ['coefficient-map','coefficient-map-jet']:
    batch=TASK/'formalization/platform'/name;count=0
    for line in (batch/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
        h,rel=line.split('  ',1);assert sha(batch/rel)==h;count+=1
    old_counts[name]=count
check('207_predecessor_author_frozen_members_unchanged',old_counts=={'coefficient-map':96,'coefficient-map-jet':111},old_counts)
dependencies=[BATCH/'SHA256SUMS.txt',BATCH/'root-copy-plan.json',BATCH/'root-install-receipt.json',BATCH/'task-build.log',BATCH/'task-build-exit.txt',BATCH/'task-check.log',BATCH/'task-check-exit.txt',native_review_path,boundary_original,TASK/'formalization/platform/readback-2026-10-03/api-docs/references/contribute.md']
dependencies += [TASK/'formalization/platform/coefficient-map-jet'/n for n in ['extract_decl_graph.lean','extract_sketch_info.lean','extract_header.lean']]
for f in plan['required_existing_Definitions']:dependencies.append(TASK/f['task_relative'])
for p in dependencies:hashes[p.relative_to(TASK).as_posix()]=sha(p)
for r in installed:hashes[r['root_relative']]=r['sha256']
for f in plan['required_existing_Definitions']:hashes[f['root_relative']]=sha(ROOT/f['root_relative'])
for p in HERE.iterdir():
    if p.is_file():hashes[p.relative_to(TASK).as_posix()]=sha(p)
project_sources=list(PROJECT.glob('*.lean'))+[PROJECT/f['root_relative_destination'] for f in plan['files']]+[PROJECT/f['root_relative'] for f in plan['required_existing_Definitions']]+[PROJECT/('missions/zeta9/formalization/'+n+'.lean') for n in ['CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity']]
for p in project_sources:hashes[p.relative_to(TASK).as_posix()]=sha(p)
for n in ['lake-manifest.json','lean-toolchain']:hashes[(PROJECT/n).relative_to(TASK).as_posix()]=sha(PROJECT/n)
limits=['The result concerns the genuine full (n+1)-by-9 local coefficient array on the strict proper domain 2n+2*natDegree W<9(n+1), including n=0 and W=0. It does not identify the original five aggregated F outputs with this array.','Every complete Solution retains all 18 original Injectivity proofs and the exact seven Base/Jet proofs selected by actual cross-module value dependency closure. Only actual definition spans, parser-certified print diagnostics and import header are removed, and the selected target references renamed.','Injectivity and the zero-kernel criterion need properness. The actual n=0,W=X^5 nonzero polynomial has every local coefficient zero outside that domain. The n=0,W=X^4 proper polynomial has simple coefficient 1 and actual weightedR=1/t at regular points; strict properness does not imply rho1=0, O(1/t^2) or summability.','All three proofs have only propext, Classical.choice and Quot.sound. The statement-reference files intentionally use sorryAx and are never imported by Solutions. The independent project reused only pinned dependency artifacts, never native or staged olean files.','Original aggregate F injectivity/inverse/surjectivity, exact infinite L, denominator/asymptotic obligations, J and zeta(9) irrationality remain open. Other later task files are outside this reviewed proof closure.','The first Lake Solution run elaborated and printed the standard axioms, then failed writing the long Windows output path. Its actual exit1 and logs are preserved. All six remaining exact staged modules subsequently compiled with short independent outputs and their new own objects were copied into this independent cache. Already successful native/Definition/oracle runs were not repeated.','This is an offline source transplantation review. Parent root installation and scoped build are separately hash-bound. The root scope check has exactly two preexisting unrelated unassigned files, so no claim that it passes. No API or credentials were accessed and platform acceptance is not claimed.']
result={'schema_version':1,'review_role':'independent actual Injectivity platform transplantation review','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS' if all(r['pass'] for r in checks) else 'FAIL','checks':checks,'sha256':dict(sorted(hashes.items())),'findings':[],'targets':target_evidence,'definition_comparisons':comparisons,'cross_module_proof_closure':reconstruction['cross_module_core_closure'],'inline_original_helpers':reconstruction['inline_helpers'],'source_position_counts':{'Stage1_environment':94,'Base_source':27,'Base_generated':1,'Jet_source':28,'Jet_generated':9,'Inject_source':25,'Inject_defs':7,'Inject_proofs':18,'Inject_generated':4,'Inject_Stage2_decl':25,'Inject_Stage2_ref':117,'Inject_Stage2_command':43,'removed_print_diagnostics':9},'actual_header_span':reconstruction['header'],'fresh_compile':{'main_observed_successful_runs':29,'main_retained_failed_output_attempts':1,'boundary_observed_successful_runs':1,'native_sources':3,'Definitions':3,'Solutions':3,'reference_stubs':3,'type_value_reports':8,'proof_helper_reports':3,'all_helper_proof_records':78,'closed_boundary_records':16,'native_or_staged_olean_borrowed':False},'retained_failed_attempts':receipt['retained_failed_attempts'],'closed_boundary_checks':closed,'installed_root':installed,'required_existing_Definitions':plan['required_existing_Definitions'],'limitations':limits,'reviewer_root_writes':False,'reviewer_scope_writes':False,'reviewer_frozen_math_source_writes':False,'reviewer_API_calls':False,'credentials_read':False,'platform_publication_claimed':False,'platform_acceptance_claimed':False}
report=BATCH/'independent-integration-review.json';write(report,json.dumps(result,ensure_ascii=False,indent=2)+'\n')
summary='''# Independent actual local-array Injectivity transplantation review

PASS. A new task-local project started without original or staged objects and freshly compiled all three exact original native sources, all three Definitions, three complete Solutions and three statement references. The actual official declaration graph, all three parser/ref oracles and header parser were replayed; 94 environment records and Injectivity's 25 declarations, 117 references and 43 commands exactly match. The Injectivity source consists of seven actual definitions, 18 proofs and four generated eq_1 records. Actual byte-span reconstruction gives all seven staged files exactly. The true value closure selects one original Base proof and six original Jet proofs; all 18 Injectivity proofs remain in every Solution.

Eight independent import reports give 175 exact type/value comparisons for all 25 actual Base/Jet/Injectivity definitions. All three original, Solution and reference types are identical with no added premise. All 78 helper/wrapper proof records use only standard axioms; each complete endpoint has exactly propext, Classical.choice and Quot.sound. References intentionally contain sorryAx and are never imported by a Solution. The final 29 successful main runs and one additional boundary audit exited zero. One earlier Lake attempt elaborated the complete Solution but failed writing the long Windows object path; its actual exit1/log remain intact. The six remaining exact stages compiled via lake env lean with short independent outputs; only their freshly generated own objects were copied into the review cache. Already successful runs were not repeated. The actual transplanted Solution also closes the 16 independently stated domain/indexing/boundary checks. At n=0, W=X^4 is proper, has simple coefficient 1 and gives 1/t; W=X^5 is nonzero with zero local array outside the proper domain. These prevent overclaiming stronger decay or unrestricted injectivity.

The complete (n+1)-by-9 local array is injective on 2n+2*natDegree W<9(n+1), including quartics for all natural n. This is not original five-dimensional aggregate F injectivity or an inverse, and it does not establish exact infinite L, J or zeta(9) irrationality. The report binds all 134 frozen author members, actual independent evidence, unchanged 207 predecessor author members, seven installed root files, both actual predecessor Definitions and parent install/scoped-build records. Parent task build passed (3760 jobs); task scope check retains exactly two unrelated preexisting unassigned files. No root, scope, frozen mathematical source, API or credentials were modified/accessed by the reviewer. No platform acceptance is asserted.

Machine-readable result: independent-integration-review.json. Replay and reconstruction evidence: independent-review/. Checksums: independent-integration-review-SHA256SUMS.txt.
'''
write(BATCH/'independent-integration-review.md',summary)
sidecar=[report,BATCH/'independent-integration-review.md']+[p for p in HERE.iterdir() if p.is_file()]
write(BATCH/'independent-integration-review-SHA256SUMS.txt',''.join(sha(p)+'  '+p.relative_to(TASK).as_posix()+'\n' for p in sorted(sidecar)))
print(json.dumps({'verdict':result['verdict'],'checks':len(checks),'sha256_bindings':len(hashes),'review_sha256':sha(report),'closed_boundary_records':len(closed)},ensure_ascii=False),flush=True)
