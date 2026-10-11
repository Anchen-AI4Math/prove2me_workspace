from pathlib import Path
from collections import Counter
from datetime import datetime,timezone
import json,re,sys,os,concurrent.futures
import inspect_prepare as p
checks=[]
STD3={'propext','Classical.choice','Quot.sound'}
def ck(label,value):
 checks.append(dict(label=label,passed=bool(value)))
 assert value,label

def records(label,receipt):
 row=next(x for x in reversed(receipt['rows']) if x['label']==label and x['exit_code']==0)
 result=[]
 path=p.TASK/row['folder_task_relative']/'stdout.log'
 for lineno,line in enumerate(path.open(encoding='utf-8'),1):
  if not line.startswith('{'):continue
  value=json.loads(line)
  if 'kind' in value:result.append(dict(record=value,stdout_line=lineno))
 return result

def validate_payload(value):
 assert value['format']=='lean-expr-dag-v1'
 nodes=value['nodes'];assert isinstance(nodes,list) and nodes
 arities={'bvar':2,'fvar':2,'mvar':2,'sort':2,'const':3,'app':3,'lam':5,'forallE':5,'letE':6,'litNat':2,'litString':2,'mdata':3,'proj':4}
 refs={'app':[1,2],'lam':[2,3],'forallE':[2,3],'letE':[2,3,4],'mdata':[2],'proj':[3]}
 for i,node in enumerate(nodes):
  assert isinstance(node,list) and node[0] in arities and len(node)==arities[node[0]]
  for j in refs.get(node[0],[]):assert isinstance(node[j],int) and 0<=node[j]<i
  if node[0] in ['lam','forallE']:assert node[4] in ['default','implicit','strictImplicit','instImplicit']
  if node[0]=='letE':assert isinstance(node[5],bool)
 for key in ['type_root','value_root']:assert isinstance(value[key],int) and 0<=value[key]<len(nodes)
 return len(nodes)

def final():
 out=p.OUT/'independent-review.json';assert not out.exists()
 ck('new Root explicit recovery lane2 grant',p.load(p.OUT/'Root-review-resume-grant-v2.json')['Root_explicit_grant'])
 ck('all own actual compile processes terminal verified by OS',p.load(p.OUT/'final-own-processes.json')==[])
 ck('final supplement driver terminal',p.load(p.OUT/'supplement-terminal.json')['actual_resolution_exit0'])
 ck('previous independent objects provenance fully revalidated',p.load(p.OUT/'recovery-inspection-v4.json')['verdict']=='PASS_PREVIOUS_INDEPENDENT_SOURCE_RUNS_REVALIDATED')
 author=p.load(p.AUTHOR/'author-audit.json')
 ck('author frozen report unchanged',p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA)
 plan=p.load(p.OUT/'control-preparation-v3.json');prep=p.load(p.OUT/'source-preparation.json')
 receipt=p.load(p.OUT/'execution-receipt.json')
 ck('29 actual calls retained',len(receipt['rows'])==29)
 ck('28 actual successes retained',sum(x['exit_code']==0 for x in receipt['rows'])==28)
 failed=[x for x in receipt['rows'] if x['exit_code']!=0]
 ck('single true missing-namespace failed control retained',len(failed)==1 and failed[0]['label']=='independent-assertions-v2' and failed[0]['exit_code']==1 and not failed[0]['output_bindings'])
 required=['runtime']+['native-'+x['module'].rsplit('.',1)[-1] for x in prep['native_sources']]+['serializer-'+x['module'] for x in prep['serializer_sources']]+['independent-assertions-v3','independent-semantic-v3','independent-all-generated-closure-v1','independent-actual-resolution-v2']
 ck('28 required labels exact and distinct',len(required)==len(set(required))==28)
 for label in required:ck('actual0 '+label,any(x['label']==label and x['exit_code']==0 and x['all_subprocess_handles_terminal'] for x in receipt['rows']))
 for row in receipt['rows']:
  directory=p.TASK/row['folder_task_relative']
  ck('actual exit receipt '+row['label'],int((directory/'exit.txt').read_text())==row['exit_code'])
  ck('actual single-thread Lean command '+row['label'],'-j1' in row['command'])
  paths=p.load(directory/'selected-paths.json')
  names=[x['name'] for x in p.load(p.PROJECT/'lake-manifest.json')['packages']]
  for k in ['LEAN_PATH','LEAN_SRC_PATH']:
   own=p.PROJECT/('b/lib/lean' if k=='LEAN_PATH' else '')
   packages=[p.ROOT/'.lake/packages'/n/('.lake/build/lib/lean' if k=='LEAN_PATH' else '') for n in names]
   expected={str(t.resolve()).casefold() for t in [own]+packages if t.is_dir()}
   ck('exact own and fixed-package search paths '+row['label']+' '+k,{str(Path(t).resolve()).casefold() for t in paths[k]['allowed_exact_set']}==expected and all(str(Path(t).resolve()).casefold() in expected for t in paths[k]['filtered']))
 sem=records('independent-semantic-v3',receipt)
 gen=records('independent-all-generated-closure-v1',receipt)
 res=records('independent-actual-resolution-v2',receipt)
 ser=records('serializer-IndependentExprDagValidationV3',receipt)
 counts=Counter(x['record']['kind'] for x in sem)
 expected_counts={'independent_actual_original_forall':16,'independent_expected_original_forall':16,'independent_complete_forall_kernel_comparison':16,'independent_actual_related_definition':18,'independent_expected_related_definition':18,'independent_full_definition_kernel_comparison':18,'independent_whole_function_rfl':18,'independent_typed_boundary':9,'independent_actual_helper_inventory':1}
 for key,value in expected_counts.items():ck('exact record count '+key,counts[key]==value)
 node_count=0;payload_count=0;raw_diagnostics=[]
 for sourced in sem+gen+ser:
  record=sourced['record'];declaration=record.get('declaration',record.get('kind'))
  if 'axioms' in record:ck('actual Std3 '+declaration,set(record['axioms'])<=STD3)
  for key in ['closed','closed_type_and_actual_proof','closed_complete_type','all_fields_Expr_equal_roundtrip','type_roundtrip_kernel_equal','value_roundtrip_kernel_equal','whole_type_roundtrip_kernel_equal','whole_type_kernel_equal','type_kernel_equal','value_kernel_equal','all_fields_roundtrip','raw_repr_reconstruction_equal']:
   if key in record:ck(key+' '+declaration,record[key] is True)
  for key,value in record.items():
   if isinstance(value,dict) and 'nodes' in value:
    node_count+=validate_payload(value);payload_count+=1;ck('complete DAG topology '+declaration+' '+key,True)
  for key in ['type_Expr_equal_diagnostic','value_Expr_equal_diagnostic']:
   if key in record:raw_diagnostics.append(dict(declaration=declaration,key=key,raw_result=record[key]))
 headers=plan['original_exact_headers']
 original=(p.TASK/'formalization/CoefficientMapFormalTransportOutputs.lean').read_text(encoding='utf-8-sig')
 actual=(p.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean').read_text(encoding='utf-8-sig')
 ck('16 original theorem headers count',len(headers)==16 and len(re.findall(r'^theorem\s+\w+',original,re.M))==16)
 for row in headers:ck('literal original header unchanged '+row['name'],original.count(row['header']+' :=')==actual.count(row['header']+' :=')==1)
 ck('actual verified SOURCE SHA',p.sha(p.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean')==p.SOURCE_SHA)
 actual_names={x['record']['declaration'] for x in sem if x['record']['kind']=='independent_actual_original_forall'}
 ck('all16 original forall kernel audited',actual_names=={'ZetaNine.CoefficientMapFormalTransportOutputs.'+x['name'] for x in headers})
 definition_records=[x['record'] for x in sem if x['record']['kind']=='independent_actual_related_definition']
 ck('all18 actual complete definitions audited',{x['declaration'] for x in definition_records}==set(plan['related_definition_names']))
 ck('all9 actual boundary statements audited',{x['record']['declaration'] for x in sem if x['record']['kind']=='independent_typed_boundary'}=={'OutputsIndependentBoundary.'+x for x in plan['boundary_names']})
 inventories=[x['record'] for x in gen if x['record']['kind']=='independent_complete_generated_closure_inventory']
 ck('exact complete generated inventory count',len(inventories)==1)
 inventory=inventories[0]
 ck('all native21 and independent assertion modules inventoried',set(inventory['modules'])==set(plan['helper_modules']))
 std_names=[x['record']['declaration'] for x in gen if x['record']['kind']=='independent_all_actual_declaration_Std3']
 helper_names=[x['record']['declaration'] for x in gen if x['record']['kind'] in ['independent_generated_helper_proof_type','independent_all_generated_definition']]
 ck('every actual module declaration Std3 covered uniquely',len(std_names)==len(set(std_names)) and set(std_names)==set(inventory['all_declarations']))
 ck('every generated helper type/value covered uniquely',len(helper_names)==len(set(helper_names)) and set(helper_names)==set(inventory['all_generated_helpers']))
 ck('26 actual own resolutions',len(res)==26)
 expected_modules=p.load(p.OUT/'resolution-preparation-v2.json')['modules']
 ck('own resolved modules exact',{x['record']['module'] for x in res}==set(expected_modules))
 object_outputs={b['task_relative']:b for x in receipt['rows'] if x['exit_code']==0 for b in x['output_bindings']}
 for entry in res:
  record=entry['record'];path=Path(record['realPath']).resolve()
  expected=(p.PROJECT/'b/lib/lean'/(record['module'].replace('.','/')+'.olean')).resolve()
  ck('real findOLean chose actual own source object '+record['module'],record['actual_expected_own_path_equal'] is True and path==expected and p.bind(path)['task_relative'] in object_outputs)
 ck('all27 own proof objects originate in actual SOURCE compiler calls',{p.bind(t)['task_relative'] for t in (p.PROJECT/'b/lib/lean').rglob('*.olean')}==set(object_outputs) and len(object_outputs)==27)
 export=p.OUT/'OutputsIndependentlyVerifiedSource.lean';assert not export.exists();export.write_bytes((p.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean').read_bytes())
 stable={}
 for row in author['stable_files']:
  key=('task_relative',row['task_relative']) if row.get('task_relative') is not None else ('root_relative',row['root_relative'])
  stable[key]=row
 def retain(path):
  binding=p.bind(path);stable[('task_relative',binding['task_relative'])]=binding
 for base in [p.PROJECT,p.OUT]:
  for directory,dirs,files in os.walk(base,followlinks=False):
   dirs[:]=[d for d in dirs if d not in ['__pycache__','packages'] and not (Path(directory)/d).is_junction() and not (Path(directory)/d).is_symlink()]
   for name in files:
    path=Path(directory)/name
    if path.name in ['independent-review.json','post-freeze-binding-check.json','finalize-failure.json']:continue
    retain(path)
 retain(p.AUTHOR/'author-audit.json');retain(p.TASK/'formalization/CoefficientMapFormalTransportOutputs.lean')
 stable_files=[stable[k] for k in sorted(stable)]
 def binding_ok(row):
  path=p.resolve(row);return path,path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for path,ok in pool.map(binding_ok,stable_files):ck('frozen exact binding '+str(path),ok)
 report=dict(verdict='PASS',reviewer_role='Independent Outputs native reviewer; not author of the 16 Outputs proofs',reviewer='outputs_independent_recovery_1007',frozen_at=datetime.now(timezone.utc).isoformat(),checks=checks,stable_files=stable_files,verified_export=p.bind(export),compiled_private_source=p.bind(p.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean'),original_shared_source=author['original_shared_source'],original_exact_headers=headers,author_report=p.bind(p.AUTHOR/'author-audit.json'),author636_inputs_personally_rehashed=True,previous_independent_review_reuse=p.bind(p.OUT/'recovery-inspection-v4.json'),previous_independent_reviewer_SOURCE_calls_reused=24,previous_independent_own_objects_reused=23,new_reviewer_actual_calls=5,total_actual_calls=29,actual_successes=28,actual_failures=1,failed_runs=[x['folder_task_relative'] for x in failed],all_actual_handles_terminal=True,own_process_readback=p.bind(p.OUT/'final-own-processes.json'),foreign_proof_objects_borrowed=False,only_fixed_mathlib_package_dependency_objects_reused=True,native_SOURCE_modules=21,complete_original_forall=16,all_actual_complete_definition_records=definition_records,whole_function_rfl=18,typed_boundaries=9,complete_semantic_record_counts=dict(counts),all_native_and_assertion_declarations_Std3=len(std_names),all_generated_helpers=len(helper_names),all_generated_closure_inventory=inventory,complete_DAG_payloads=payload_count,complete_DAG_nodes=node_count,raw_Expr_diagnostics_unaltered=raw_diagnostics,metadata_binders_levels_names_or_arguments_suppressed=False,actual_own_findOLean=26,scope=dict(finite_B_constantTerm_forall_n_ge_one=True,five_actual_outputs_forall_n_ge_one=True,actual_LEFT_Gamma_matrix_transport_forall_n_ge_one=True,includes_minimum_n_one=True,HasSum_parameter_transport=False,integer_height_bound=False,J=False,irrationality=False,platform_acceptance=False),required_actual_labels=required,exact_complete_type_kernel_records=[x['record'] for x in sem if x['record']['kind']=='independent_complete_forall_kernel_comparison'],exact_complete_definition_type_value_kernel_records=[x['record'] for x in sem if x['record']['kind']=='independent_full_definition_kernel_comparison'],lossless_proof_and_definition_expression_records_location='actual-runs/c027-a01/stdout.log plus complete generated closure actual-runs/c028-a01/stdout.log; all logs and their immutable bindings retained',whole_failed_controls_excluded=True,all_original_sources_and_failed_controls_preserved=True,API_calls=0,Root_module_installations=0)
 p.dump(out,report)
 p.check(stable_files)
 p.dump(p.OUT/'post-freeze-binding-check.json',dict(report=p.bind(out),stable_binding_count=len(stable_files),all_exact_content_bindings_rehashed_after_freeze=True,verdict='PASS',all_actual_handles_terminal=True))
 print(json.dumps(dict(verdict='PASS',report_SHA=p.sha(out),checks=len(checks),stable_bindings=len(stable_files),actual_calls=29,actual_successes=28,actual_failures=1,actual_SOURCE=21,complete_forall=16,whole_definitions=18,boundaries=9,Std3_declarations=len(std_names),generated_helpers=len(helper_names),own_resolutions=26,export_SHA=p.sha(export),postfreeze_SHA=p.sha(p.OUT/'post-freeze-binding-check.json')),indent=2))
if __name__=='__main__':
 sys.stdout.reconfigure(encoding='utf-8')
 try:final()
 except Exception as e:
  p.dump(p.OUT/'finalize-failure.json',dict(error=str(e),checks=checks,independent_PASS_claimed=False));raise
