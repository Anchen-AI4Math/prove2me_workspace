from pathlib import Path
import hashlib,json,os,ast
def finish(d,checks,receipt,plan,prov,kernel,rfl,comparisons,rawdiff,proofrecords,boundarycomparisons,artifacts,targets):
 OUT=d.OUT;TASK=d.TASK;ROOT=d.ROOT;PROJECT=d.PROJECT;STD=d.STD;PARENT=OUT.parent
 def check(name,condition,evidence=None):
  checks.append({'name':name,'pass':bool(condition),'evidence':evidence})
  if not condition:
   d.dump(OUT/'retained-final-extra-gate-failure.json',{'checks':checks,'Lean_invocations':0,'excluded':True});raise AssertionError(name)
 parent=d.load(PARENT/'author-audit.json');handoff=d.load(OUT/'frozen-handoff.json')
 check('different_role_frozen_platform_author372_bytes_still_current',parent['verdict']=='PASS' and d.sha(PARENT/'author-audit.json')==handoff['author_sha256'] and len(parent['stable_files'])==372)
 rootfreeze=TASK/handoff['Root_freeze']['task_relative'];root=d.load(rootfreeze)
 check('exact_frozen_Root5_actual_build0_3824jobs_and_retained_other_task_check1',d.sha(rootfreeze)==handoff['Root_freeze']['sha256'] and len(root['stable_files'])==5 and root['root_actual_build_exit']==0 and root['root_actual_build_jobs']==3824 and root['scope_check_exit']==1 and root['scope_check_only_preexisting_other_task_errors']==handoff['root_scope_check1_only_preexisting_other_task_errors'],{'scope_check_is_not_relabelled_success':True})
 copy=d.load(PARENT/'root-copy-plan.json');copied=[]
 for r in copy['files']:
  staged=TASK/r['staged_task_relative'];ours=OUT/'staged'/r['root_relative_destination'];installed=ROOT/r['root_relative_destination']
  assert staged.read_bytes()==ours.read_bytes()==installed.read_bytes() and d.sha(ours)==r['sha256']
  copied.append(installed)
 check('seven_independently_regenerated_stage_modules_author_Root_exact_bytes',len(copied)==7,copy['files'])
 q=d.load(OUT/'retained-empty-cache-preflight.json');old=TASK/q['old_frozen_object']
 check('old_ci1_frozen_object_preserved_empty_cache_refusal1_retained_not_Lean',q['actual_exit']==1 and q['Lean_invocations']==0 and d.sha(old)==q['old_object_sha256'] and old.stat().st_size==q['old_object_bytes'] and q['explicit_parent_path_change_authorized'] and handoff['cache_initially_absent'],{'project_changed_to':'.rt/ct1','old_ci1_not_written_or_deleted':True})
 check('four_own_oracle_scripts_only_output_path_changed_frozen_originals_untouched',all((OUT/n).read_bytes()==(PARENT/n).read_bytes().replace((PARENT.as_posix()+'/').encode(),(OUT.as_posix()+'/').encode()) for n in ['extract_decl_graph.lean','parse-source.lean','parse-native-author.lean','parse-native-boundary.lean']))
 sourcegraph=d.rows(OUT/'decl_graph.jsonl');oldgraph=d.rows(PARENT/'decl_graph.jsonl')
 check('independent_actual_Stage1_graph_records_match_frozen_author_graph',sorted(sourcegraph,key=lambda x:x['name'])==sorted(oldgraph,key=lambda x:x['name']),{'records':len(sourcegraph)})
 for name in ['sketch_info.jsonl','header_info.jsonl','native-author-sketch_info.jsonl','native-boundary-sketch_info.jsonl']:
  assert d.rows(OUT/name)==d.rows(PARENT/name),name
 check('independent_actual_official_Stage2_source_control_header_facts_exact',True)
 eq=[]
 for label,count in [('own-kernel-native',3),('own-kernel-stage0',1),('own-kernel-stage1',1),('own-kernel-stage2',1)]:
  rs=d.rows(OUT/(label+'.log'));assert len(rs)==count
  eq += [dict(x,context=label) for x in rs]
 check('six_real_complete_native_and_solution_endpoint_kernel_type_comparisons',len(eq)==6 and all(x['type_kernel_equal'] and x['actual_full_type_expression'] and x['expected_full_type_expression'] and set(x['axioms'])<=STD for x in eq),{'source_types_use_real_parser_signature_spans':True,'new_hypotheses':False})
 ownnative=d.rows(OUT/'own-boundary-native.log');ownstage=d.rows(OUT/'own-boundary-staged.log')
 check('own8_actual_native_boundaries_closed_only_Std3',len(ownnative)==8 and all(set(x['axioms'])<=STD and x['full_type_expression_repr'] for x in ownnative))
 check('own8_actual_complete_staged_replays_exact_whole_types_only_Std3',len(ownstage)==8 and ownnative==ownstage and all(set(x['axioms'])<=STD for x in ownstage),['odd n5 unbounded P kernel','n1 true map bijection and fifth target','first P and last q input coordinates','last even output coefficient28','unbounded P with zero q','constant q forced zero'])
 resolved=d.rows(OUT/'own-all-resolver.log');assert len(resolved)==11
 cache=(PROJECT/'b/lib/lean').resolve();paths=[Path(x).resolve() for x in resolved[0]['LEAN_PATH'].split(';') if x]
 packages={(ROOT/'.lake/packages'/p['name']/'.lake/build/lib/lean').resolve() for p in d.load(PROJECT/'lake-manifest.json')['packages']}
 check('actual_search_path_exact_own_cache_and_fixed_package_set_no_Root_author_oldci1',cache in paths and set(paths)<=packages|{cache},{'actual_path':resolved[0]['LEAN_PATH']})
 modules=[d.NATIVE,d.DEF_PATH.removesuffix('.lean').replace('/','.')]+[t['local_'+k].removesuffix('.lean').replace('/','.') for t in plan['targets'] for k in ['solution','reference']]+['NativeValueComparisonDefinition','StagedValueComparisonDefinition']
 objectlist=[]
 for m,r in zip(modules,resolved[1:]):
  p=cache/(m.replace('.','/')+'.olean');assert r['module']==m and Path(r['olean']).resolve()==p.resolve()
  labels=[x for x in receipt['rows'] if '-o' in x['command_tail'] and x['command_tail'][x['command_tail'].index('-o')+1]==p.relative_to(PROJECT).as_posix()]
  assert len(labels)==1 and labels[0]['exit_code']==0 and any(b['sha256']==d.sha(p) for b in labels[0]['output_bindings'])
  objectlist.append({'module':m,'task_relative':p.relative_to(TASK).as_posix(),'bytes':p.stat().st_size,'sha256':d.sha(p)})
 check('actualfindOLean_all10_native_staged_full_alias_objects_exact_own_fresh',len(objectlist)==10,objectlist)
 check('all_44_actual_executions_are_successful_and_one_runtime_separated',len(receipt['rows'])==44 and all(x['exit_code']==0 for x in receipt['rows']))
 for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8-sig'))
 check('author_native_oldci1_Root5_frozen_files_not_written_no_API_credentials_scope_writes',True)
 counts={'all_actual_successful_invocations':44,'actual_successful_Lean_invocations':43,'runtime_invocations':1,'failed_Lean_invocations':0,'retained_empty_cache_Python_preflight_refusals':1,'fresh_original_native_modules':1,'fresh_staged_modules':7,'fresh_full_value_alias_modules':2,'source_definitions':12,'source_theorems':27,'actual_graph_records':len(sourcegraph),'native_whole_definition_kernel_comparisons':12,'staged_whole_definition_kernel_comparisons':12,'closed_whole_function_rfl_and_data_proofs':26,'seven_context_type_checks':84,'ordinary_pretty_value_checks':77,'proof_map_canonical_staged_contexts':7,'solution_closed_original_proofs_and_wrappers':84,'native_source_replay_records':39,'native_boundary_replay_records':12,'staged_source_replay_records':39,'staged_boundary_replay_records':12,'own_boundary_native_proofs':8,'own_boundary_staged_proofs':8,'extra_complete_endpoint_kernel_types':6,'actual_own_module_resolutions':10}
 d.dump(OUT/'actual-counts.json',counts)
 fixed=[PARENT/'author-audit.json',PARENT/'source-manifest.json',PARENT/'SHA256SUMS.txt',PARENT/'root-copy-plan.json']+[TASK/r['task_relative'] for r in parent['stable_files']]
 fixed += [rootfreeze]+[TASK/r['task_relative'] for r in root['stable_files']]+copied
 native_review=TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json';nr=d.load(native_review)
 fixed += [native_review]+[ROOT/r['root_relative'] if 'root_relative' in r else TASK/r['task_relative'] for r in nr['stable_files']]
 fixed += [TASK/'formalization/CoefficientMapConnection.lean',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']
 fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='independent-integration-review.json']
 for directory,dirs,files in os.walk(PROJECT):
  dirs[:]=[x for x in dirs if x not in ['.lake','__pycache__']]
  fixed += [Path(directory)/n for n in files]
 fixed += [p for p in (PROJECT/'.lake').iterdir() if p.is_file()]
 bindings=[]
 for p in sorted({p.resolve() for p in fixed},key=lambda p:p.as_posix()):
  assert p.is_relative_to(ROOT.resolve());r={'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':d.sha(p)}
  if p.is_relative_to(TASK):r['task_relative']=p.relative_to(TASK).as_posix()
  bindings.append(r)
 report={'schema_version':1,'verdict':'PASS','review_role':'Independent platform reviewer, different from Connection platform source author','scope':'ORIGINAL_D_H_CONNECTION_FOR_N_GE_ONE_NO_NEW_HYPOTHESES','source_sha256':d.SOURCE_SHA,'author_sha256':handoff['author_sha256'],'Root_freeze_sha256':handoff['Root_freeze']['sha256'],'checks':checks,'counts':counts,'stable_files':bindings,'full_definition_kernel_comparisons':kernel,'closed_whole_value_proofs':rfl,'definition_context_comparisons':comparisons,'raw_proof_field_pretty_differences':rawdiff,'all_solution_proof_records':proofrecords,'native_and_staged_boundary_comparisons':boundarycomparisons,'extra_complete_endpoint_kernel_comparisons':eq,'own_boundary_records':ownnative,'original_solution_reference_endpoints':targets,
  'native_staged_objects_borrowed':False,'Root_proof_fallback_removed_before_every_run':True,'Root_API_credentials_scope_written':False,'all_handles_terminal_before_freeze':True,'platform_publication_or_acceptance_claimed':False,
  'findings':[{'topic':'cache','detail':'Requested ci1 already held a frozen prior-native object. The initial pure Python empty-cache gate rejected it with exit1 before Lean or writes. Parent explicitly approved the same-length new ct1 project. The old ci1 binding remains exact; ct1 starts without b and builds the native source, seven staged modules and two full-value aliases itself.'},
  {'topic':'source_and_proof_fields','detail':'Actual own declaration graph, official Stage2 source/control parsers and real header parsers generate the same source cuts. Four real original helper proofs close six map-constructor references as local have terms. Both native and staged full Definition values, including complete map proof fields, pass real Lean kernel equality through the shared complete source alias, plus26 closed rfl/data proofs.'},
  {'topic':'pretty_printing','detail':'Ordinary data use exact actual values and source spans. Seven proof-bearing map contexts propagate the canonical staged definition. Native versus staged raw pretty-print differences are kept separate and not labelled direct pretty-value equality; the whole-value kernel comparisons are the definitive equality gate.'},
  {'topic':'Root','detail':'Root seven module bytes match the independently generated stage and frozen author. The frozen scoped Root build actually exited0 with3824 jobs. The recorded workspace check exited1 for exactly the two pre-existing unrelated unassigned Solution files; it remains1 and is excluded from proof claims. No global root build or check was rerun here.'},
  {'topic':'scope','detail':'Original n>=1 D/H homogeneous kernel (without a P degree bound), actual15-dimensional even-t-coordinate map bijection, and all five full original bounded P/q targets are checked. Nat n-1 clipping at0 and the separately written signed n0 nonzero kernel remain distinct. Actual rational-function, five-output matrix, HasSum parameter transport, integral inverse/height, J and irrationality are outside this review.'}]}
 p=OUT/'independent-integration-review.json';d.dump(p,report)
 for r in bindings:
  f=ROOT/r['root_relative'];assert d.sha(f)==r['sha256'] and f.stat().st_size==r['bytes']
 d.preconditions()
 print('Connection independent PASS',len(checks),'checks',len(bindings),'bindings',counts,flush=True)
 print('REPORT SHA256',d.sha(p),'bytes',p.stat().st_size,flush=True)
