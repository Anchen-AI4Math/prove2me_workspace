"""Freeze only after independent actual Lean, source, and root evidence pass."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=OUT.parents[3];ROOT=TASK.parents[1]
NS='ZetaNine.CoefficientMapAggregate';ALIAS=NS+'ValueComparison'
TARGETS=['aggregate_add','polynomial_restore','aggregate_zero_all_rho']
MAPS=[NS+'.'+n for n in ['aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']]
STD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def dump(p,d):p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
def index(rs):
 a={r['declaration']:r for r in rs};assert len(a)==len(rs);return a
def standard(r):return set(r['axioms'])<=STD
def normalize(s):
 for n in TARGETS:s=s.replace(NS+'.checked_'+n,NS+'.'+n)
 return s
def payload(rs):return {r['label']:{'type':r['type'],'value':r['value'],'axioms':sorted(r['axioms'])} for r in rs}
mechanical=load(OUT/'mechanical-checks.json');assert mechanical['complete'];checks=list(mechanical['checks'])
def check(n,ok,d=None):
 checks.append({'name':n,'pass':bool(ok),'detail':d});dump(OUT/'finalizer-development-checks.json',{'checks':checks,'complete':False});assert ok,n
receipts=[load(OUT/n) for n in ['prepare-compile-receipt.json','actual-extraction-receipt.json','native-alias-audit-receipt.json','replay-compile-receipt.json']]
assert [len(r['rows']) for r in receipts]==[17,11,3,30] and all(r['complete'] for r in receipts)
calls=[r for receipt in receipts for r in receipt['rows']]
for r in calls:
 assert r['exit_code']==int((OUT/r['exit_file']).read_text().strip())==0
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 for f in ['log','exit_file','wrapper','output','stdout_copy']:
  if r.get(f):assert sha(OUT/r[f])==r['stdout_sha256' if f=='stdout_copy' else f+'_sha256']
 wrapper=(OUT/r['wrapper']).read_text(encoding='utf-8-sig');assert (OUT/'cache').as_posix() in wrapper and (BATCH/'project').as_posix() not in wrapper
 assert (OUT/'project').as_posix() in wrapper and 'LEAN_NUM_THREADS = "1"' in wrapper
check('61_actual_independent_source_parser_module_type_proof_Lean_runs_zero',len(calls)==61,{'preparation':17,'source_extraction':11,'native_alias_type_and_kernel':3,'platform_replay':30,'native_and_staged_objects_borrowed':False,'guarded_same_project_type_oracle_resume':True})
env=load(OUT/'actual-environment.json')
check('actual_Lean_4_33_1_and_pinned_Mathlib_environment',env['actual_runtime_exit_code']==0 and '4.33.1' in env['lean_runtime_stdout'] and env['lean_toolchain']=='leanprover/lean4:v4.33.1' and env['mathlib_manifest_revision']=='0df444a360eaa60ab8c11dca51a86af692955474' and sha(ROOT/'lake-manifest.json')==env['root_lake_manifest_sha256'] and sha(ROOT/'lean-toolchain')==env['root_toolchain_sha256'] and (OUT/'actual-toolchain-exit.txt').read_text().strip()=='0',{'separate_runtime_probe':1})
original=index(rows(OUT/'replay-types_original.log'));definitions=index(rows(OUT/'replay-types_definition.log'))
assert len(original)==52 and len(definitions)==49
contexts=[('definition',definitions)];solutions=[];references=[]
for i in range(3):
 s=index(rows(OUT/f'replay-types_{i}_solution.log'));r=index(rows(OUT/f'replay-types_{i}_reference.log'));assert len(s)==len(r)==50
 contexts.extend([(f'solution_{i}',s),(f'reference_{i}',r)]);solutions.append(s);references.append(r)
typecomparisons=[];ordinary=[];mapPP=[]
for c,rs in contexts:
 for n in definitions:
  a,b=original[n],rs[n];typecomparisons.append({'context':c,'declaration':n,'pass':a['type']==b['type'] and standard(a) and standard(b)})
  if n not in MAPS:ordinary.append({'context':c,'declaration':n,'pass':a['value']==b['value']})
  else:mapPP.append({'context':c,'declaration':n,'raw_default_PP_equal':a['value']==b['value'],'pp_proofs':False,'native_raw_value':a['value'],'staged_raw_value':b['value']})
check('343_native_Def_types_exact_in_seven_contexts',len(typecomparisons)==343 and all(r['pass'] for r in typecomparisons),{'actual_Defs':49,'contexts':7})
check('322_ordinary_native_Def_raw_values_exact',len(ordinary)==322 and all(r['pass'] for r in ordinary),{'ordinary_Defs':46,'parent_Defs':43,'new_ordinary_Defs':3,'proof_bearing_Defs_excluded':3})
check('21_proof_map_default_PP_comparisons_honestly_split_7_diff_14_equal',len(mapPP)==21 and sum(not r['raw_default_PP_equal'] for r in mapPP)==7 and {r['declaration'] for r in mapPP if not r['raw_default_PP_equal']}=={NS+'.coordinateLinearMap'}, {'raw_PP_equal_is_not_full_proof_expression_equality':True,'aggregateLinearMap_proof_fields_elided_in_default_PP':True})
kernel=rows(OUT/'independent-native-value-comparison.log');kr=[r for r in kernel if r['kind']=='actual_native_whole_kernel_value'];rfl=[r for r in kernel if r['kind']=='rfl_whole_or_data_equality']
check('six_native_whole_Meta_isDefEq_and_nine_kernel_rfl_records',len(kernel)==15 and len(kr)==6 and len(rfl)==9 and all(r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['pp_proofs'] and standard(r) for r in kr) and all(standard(r) for r in rfl), {'native_kernel_environment_count':1,'direct_native_kernel_pairs':6,'whole_definition_rfl':6,'toFun_data_rfl':3,'proof_irrelevance_applies_to_proof_fields':True,'full_Expr_repr_retained':True})
full=[];canonical=index(rows(OUT/'full-context-0.log'));assert set(canonical)==set(MAPS)
for i in range(7):
 rs=index(rows(OUT/f'full-context-{i}.log'));assert set(rs)==set(MAPS)
 for n,r in rs.items():
  a=canonical[n];full.append({'context_index':i,'declaration':n,'full_expression_sha256':hashlib.sha256(r['full_expression_repr'].encode()).hexdigest(),
   'pass':r['full_expression_repr']==a['full_expression_repr'] and r['type']==a['type'] and r['raw_value']==a['raw_value'] and r['pp_proofs'] and standard(r)})
check('21_actual_full_proof_map_expression_context_propagation_matches_canonical_Def',len(full)==21 and all(r['pass'] for r in full),{'contexts':load(OUT/'replay-compile-receipt.json')['full_value_contexts'],'direct_native_kernel_calls_claimed_for_these_21':False,'source_isomorphic_alias_bound_to_six_native_kernel_pairs':True})
targetchecks=[]
for i,n in enumerate(TARGETS):
 a,b,c=original[NS+'.'+n],solutions[i]['solution'],references[i][NS+'.'+n]
 assert a['value'] is b['value'] is c['value'] is None and standard(a) and standard(b) and set(a['axioms'])==set(b['axioms'])==STD and set(c['axioms'])==STD|{'sorryAx'}
 targetchecks.append({'target':NS+'.'+n,'original_type':a['type'],'solution_type':b['type'],'reference_type':c['type'],'pass':a['type']==b['type']==c['type'],'extra_hypotheses':[]})
check('three_original_Sol_reference_exact_types_without_extra_hypotheses',all(r['pass'] for r in targetchecks),{'reference_sorryAx_is_statement_stub_only':True})
native=index(rows(OUT/'independent-native-required-proofs.log'));assert len(native)==73 and all(standard(r) for r in native.values())
proofchecks=[]
for i in range(3):
 hs=rows(OUT/f'replay-helpers_{i}.log');assert len(hs)==74;rs={normalize(r['declaration']):r for r in hs if r['declaration']!='solution'};assert set(rs)==set(native)
 for n,r in rs.items():proofchecks.append({'solution_index':i,'declaration':r['declaration'],'native_declaration':n,'pass':normalize(r['type'])==native[n]['type'] and standard(r),'axioms':r['axioms']})
 w=next(r for r in hs if r['declaration']=='solution');proofchecks.append({'solution_index':i,'declaration':'solution','pass':w['type']==original[NS+'.'+TARGETS[i]]['type'] and standard(w),'axioms':w['axioms']})
check('all_222_actual_Sol_proofs_match_73_native_types_only_standard_axioms',len(proofchecks)==222 and all(r['pass'] for r in proofchecks),{'per_Sol':74,'original_proofs':20,'actual_cross_helpers':53,'wrapper':1})
for n in ['types_original','types_definition']+[f'types_{i}_{k}' for i in range(3) for k in ['solution','reference']]+[f'helpers_{i}' for i in range(3)]:assert payload(rows(OUT/('replay-'+n+'.log')))==payload(rows(BATCH/(n+'.log')))
check('eleven_actual_type_proof_reports_equal_frozen_author_reports',True)
brows=rows(OUT/'replay-stage-boundary-audit.log');nb=rows(OUT/'independent-native-boundary-audit.log');st=index([r for r in brows if r['kind']=='native_exact_boundary']);nt=index(nb);extra=[r for r in brows if r['kind']=='boundary_only_genuine_helper']
assert len(st)==len(nt)==54 and len(extra)==33 and {normalize(n) for n in st}==set(nt) and all(standard(r) for r in brows+nb)
bc=[]
for n,r in st.items():
 a=nt[normalize(n)];ok=normalize(r['type'])==a['type'] and (r['definitionValue']==a['definitionValue'] or normalize(n) in MAPS)
 bc.append({'declaration':n,'native_declaration':normalize(n),'type_exact':normalize(r['type'])==a['type'],'raw_value_exact':r['definitionValue']==a['definitionValue'],'proof_map_value_verified_by_native_kernel_and_context_chain':normalize(n) in MAPS,'pass':ok})
check('54_actual_original_boundaries_exact_types_and_ordinary_values',all(r['pass'] for r in bc),{'original_source_records':26,'author_closed_records':6,'independent_closed_records':22,'three_proof_map_values_verified_separately':True})
check('33_actual_boundary_only_parent_helpers_standard_axioms',all(standard(r) for r in extra),{'helpers_excluded_from_222_Sol_proof_count':True,'genuine_graph_parser_source_bodies':True})
assert brows==rows(BATCH/'stage-boundary-audit.log')
check('fresh_staged_boundary_87_records_equal_frozen_author_report',True,{'native_boundaries':54,'extra_audit_only_helpers':33,'fresh_official_boundary_parsers':2})
old=TASK/'verification/formalization-coefficient-map-aggregate-independent-2026-10-04'
oldclosed=index(load(old/'independent-boundary-types.json'));oldcore=index(load(old/'independent-original-types.json'))
assert len(oldclosed)==22 and len(oldcore)==32
assert all(n in nt and nt[n]['type']==r['type'] and nt[n]['definitionValue']==r.get('definitionValue') and standard(r) for n,r in oldclosed.items())
# The older complete source report uses the same default PP, which is separately qualified for proof maps.
assert all(n in nt and nt[n]['type']==r['type'] and nt[n]['definitionValue']==r['definitionValue'] for n,r in oldcore.items())
check('fresh_native_26_core_plus_6_author_and_22_independent_controls_match_math_freeze',True,{'prior_native_report_only_comparison_not_borrowed_objects':True})
required=['agg_ind_roundtrip_zero','agg_ind_roundtrip_nonmonic','agg_ind_n_zero_X_four_F_zero','agg_ind_n_zero_X_four_rho1','agg_ind_n_zero_X_four_proper_not_strong','agg_ind_n_zero_actual_F_not_injective','agg_ind_n_zero_quartic_F_nonzero_kernel','agg_ind_n_zero_X_three_output','agg_ind_n_zero_F_zero_does_not_give_HasSum','agg_ind_all_rho_zero_strong_even']
check('actual_n0_X4_noninjective_rho1_notStrong_noHasSum_and_nonmonic_controls_present',all(n in nt for n in required),{'F0_X4':0,'rho_0_1_X4':1,'X4_nonzero_and_quartic':True,'StrictProper_not_Strong':True,'F_zero_does_not_imply_all_rho_without_Even_and_Strong':True})
nl=[r['natural_language_statement'] for r in load(BATCH/'problems-request.json')['problems']]
check('prose_preserves_general_linearity_quartic_restore_and_even_Strong_rho_totals',all(t in nl[i] for i,t in [(0,'without an evenness'),(1,'nonmonic quartics'),(1,'does not assert that the aggregate'),(2,'stronger degree bound'),(2,'Evenness and the stronger degree bound are retained'),(2,'not the individual local coefficient array'),(2,'does not infer $W=0$'),(2,'rho_{0,1}=1')]))
prints=[]
for r in calls:
 for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/r['log']).read_text(encoding='utf-8-sig')):
  s={a.strip() for a in axs.split(',') if a.strip()};assert s<=STD;prints.append({'invocation':r['label'],'declaration':name,'axioms':sorted(s)})
check('all_actual_source_Sol_printed_axioms_standard',len(prints)>=3,len(prints))
rootprints=re.findall(r"info: Solutions/Sol_ZetaNine_CoefficientMapAggregate_([^.:]+)\.lean:\d+:\d+: 'solution' depends on axioms: \[([^\]]*)\]",(BATCH/'task-build.log').read_text(encoding='utf-8-sig'))
check('parent_build_three_new_Sol_standard_axiom_prints',len(rootprints)==3 and {n for n,a in rootprints}==set(TARGETS) and all({s.strip() for s in a.split(',')}<=STD for n,a in rootprints),{'older_PNT_mirror_outside_proof_claim':True})
failed=load(OUT/'retained-alias-preparation-failure.json');attempt2=OUT/'alias-reconstruction-python-exit.txt.attempt02-preserved'
check('four_Python_preparation_or_mechanical_assertions_retained_separately_from_all_Lean_zero',failed['actual_exit_code']==1 and not failed['mathematical_or_Lean_failure'] and load(OUT/'retained-finalizer-oldcore-count-failure.json')['actual_exit_code']==1 and not load(OUT/'retained-finalizer-oldcore-count-failure.json')['mathematical_or_Lean_failure'] and load(OUT/'retained-boundary-order-failure.json')['actual_exit_code']==1 and not load(OUT/'retained-boundary-order-failure.json')['mathematical_or_Lean_failure'] and attempt2.read_text().strip()=='1' and (OUT/'alias-reconstruction-python-exit.txt').read_text().strip()=='0',{'causes':['namespace-length-dependent actual type printer line wrapping','Windows text writer CRLF conversion','frozen FiniteSum/Reflection bridge ordering','old original report includes6 author closed controls'],'actual_native_and_stage_Lean_failures':0})
dump(OUT/'independent-comparison-records.json',{'definition_type_comparisons':typecomparisons,'ordinary_raw_value_comparisons':ordinary,'proof_map_default_PP_comparisons':mapPP,'native_whole_kernel_records':kr,'native_rfl_records':rfl,'full_expression_context_propagation':full,'target_comparisons':targetchecks,'Sol_proof_comparisons':proofchecks,'boundary_comparisons':bc,'native_boundary_records':nb,'extra_audit_helper_records':extra,'printed_axioms':prints})
findings=[
 {'severity':'informational','code':'EXACT_SCOPE','detail':'Actual rational five-output F_n is linear for every n, including zero. Quartic coefficient restoration has natDegree<=4 and includes zero/nonmonic polynomials. All-rho vanishing keeps Even n, actual Strong degree gap, F_n(W)=0, and 1<=s<=9; it concerns totals, not all local coefficients or W=0.'},
 {'severity':'informational','code':'PROOF_BEARING_DEFINITIONS','detail':'Four actual constructor proof references close ten genuine helper bodies as local have proofs. Data fields remain original.49 types across7contexts give343 exact type comparisons;46 ordinary Def values give322 raw comparisons. Three proof maps require the separate full kernel proof and context propagation; default PP yields7 unequal and14 apparently equal map values, with elided proof fields.'},
 {'severity':'informational','code':'KERNEL_AND_PROPAGATION_COUNTS','detail':'One fresh actual native environment checks six whole original/alias definitions using Meta.isDefEq, six whole-function kernel rfl theorems and three data rfl theorems.21 full-expression checks are propagation of the same staged global definitions through seven contexts, bound by isomorphic source and native alias equality. They are not21 separate direct native kernel comparisons.'},
 {'severity':'informational','code':'GENUINE_COMPLETE_PROOFS','detail':'Each Sol retains20 actual Aggregate proofs,53 genuine parent helpers and one wrapper;222 proof records use only the three standard axioms. References contain sorryAx only as statement stubs; complete Sols import pure Definitions and Mathlib.'},
 {'severity':'informational','code':'COUNTEREXAMPLE_BOUNDARIES','detail':'Fresh original closed n0,X4 controls prove F0=0 for a nonzero quartic, rho1=1, strict properness without Strong, and no HasSum. n0,X3 and zero/nonmonic restoration controls are retained. No inverse or irrationality claim is made.'},
 {'severity':'informational','code':'ROOT_AND_FRESH_OBJECTS','detail':'61 successful independent Lean source/extraction/module/audit invocations plus one runtime probe use new native/platform objects and shared pinned Mathlib only. The parent3803-job scoped build0 and15 root module bytes are bound. Check1 is only the two old Tao unassigned entries. Two Python preparation byte assertions, one boundary-order Python assertion and one old-report-count Python assertion are retained and excluded from Lean success evidence.'},
 {'severity':'informational','code':'OPEN_OBLIGATIONS','detail':'Aggregate inverse/integrality heights, small nonzero integer forms, general parameters, J and zeta9 irrationality remain outside this verdict. KernelBridge and other missions are separate; no API, scope, root, credentials or publication changes are performed by this reviewer.'}]
md='Independent Aggregate platform integration review: PASS.\n\nActual five rational outputs, quartic coefficient restoration, and all-rho totals under the original Even and Strong hypotheses.\n\n61 fresh actual Lean exits0 plus one runtime probe;343 exact Def types and322 ordinary raw values; six native whole kernel equalities and nine rfl/data records;21 full-expression context propagation records;222 Sol proof records;54 native boundaries and33 audit-only genuine helpers. Default proof-map PP equality is not claimed as full expression equality.\n\nParent scoped3803-job build0 and15 root byte files match. No inverse or irrationality result is claimed.\n'
(OUT/'independent-integration-review.md').write_bytes(md.encode());(OUT/'independent-integration-review.log').write_bytes(('PASS\n'+'\n'.join(c['name']+': PASS' for c in checks)+'\n').encode())
paths={TASK/r['task_relative'] for r in load(BATCH/'source-manifest.json')['files']}
paths.update(BATCH/n for n in mechanical['author_frozen_controls']);paths.update(BATCH/n for n in mechanical['root_evidence_sha256']);paths.update(ROOT/n for n in mechanical['root_paths']);paths.update(ROOT/n for n in mechanical['old_frozen_manifests'])
paths.update(ROOT/r['root_relative'] for r in load(old/'independent-review.json')['stable_files']);paths.add(old/'independent-review.json');paths.update(ROOT/n for n in ['lake-manifest.json','lean-toolchain'])
for batch in mechanical['prior_independent_reviews']:paths.add(TASK/'formalization/platform'/batch/'independent/independent-integration-review.json')
paths.update(OUT.rglob('*'));reportpath=OUT/'independent-integration-review.json';stable=[]
for p in sorted(paths,key=lambda p:p.as_posix()):
 if not p.is_file() or p==reportpath:continue
 assert p.is_relative_to(ROOT);stable.append({'task_relative':p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
report={'schema_version':1,'verdict':'PASS','scope_verdict':'PASS_ACTUAL_AGGREGATE_PLATFORM_INTEGRATION','review_role':'Independent transplant reviewer; not mathematical or platform batch author','checked_at':datetime.now(timezone.utc).isoformat(),
 'source_sha256':load(OUT/'prepare-compile-receipt.json')['original_sources_sha256']['CoefficientMapAggregate'],'author_frozen_controls':mechanical['author_frozen_controls'],'checks':checks,'findings':findings,
 'compile_counts':{'preparation':17,'source_extraction':11,'native_alias_type_kernel':3,'platform_replay':30,'total':61,'separate_runtime_probe':1,'all_Lean_invocations':62,'actual_nonzero_Lean_exits':0,'retained_Python_preparation_or_mechanical_failures':4},
 'audit_counts':{'graph':len(rows(OUT/'native-decl-graph.jsonl')),'new_Defs':6,'actual_Defs':49,'definition_type_comparisons':343,'ordinary_value_comparisons':322,'proof_map_PP_different':7,'proof_map_default_PP_equal':14,'direct_native_kernel_pairs':6,'whole_definition_rfl':6,'data_rfl':3,'full_expression_context_propagation':21,'exact_targets':3,'native_required_proofs':73,'Sol_proof_records':222,'native_boundary_records':54,'audit_only_extra_helpers':33},
 'actual_cross_source_helpers':mechanical['actual_cross_helpers'],'new_external_theorem_boundaries':[],'root_module_bytes_verified':True,'parent_task_build_exit_code':0,'parent_task_build_jobs':3803,'workspace_check_exit_code':1,
 'reviewer_root_scope_API_credentials_writes':False,'platform_published_by_reviewer':False,'platform_acceptance_claimed':False,'failed_attempts_excluded_from_success_evidence':True,'stable_files':stable,'hash_exclusions':['report self','dynamic scope.json','API receipts and documentation','credentials']}
dump(reportpath,report);assert all(sha(ROOT/r['root_relative'])==r['sha256'] and (ROOT/r['root_relative']).stat().st_size==r['bytes'] for r in stable)
print('Independent Aggregate PASS; '+str(len(checks))+' checks; '+str(len(stable))+' bindings');print('review_sha256='+sha(reportpath))
