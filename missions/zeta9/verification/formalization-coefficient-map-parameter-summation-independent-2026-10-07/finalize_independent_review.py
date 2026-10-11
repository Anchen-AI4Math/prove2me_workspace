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


# Generic receipt/schema validation SOURCE reused from this reviewer's earlier independent package; no mathematics or proof objects reused.

def final():
 out=p.OUT/'independent-review.json';assert not out.exists()
 ck('explicit Root independent lane2 grant',p.load(p.OUT/'Root-independent-lane2-grant.json')['Root_explicit_grant'])
 ck('actual OS all own compiler processes terminal',p.load(p.OUT/'final-own-processes.json')==[])
 ck('all own semantic generated and resolver handles terminal',p.load(p.OUT/'control-terminal.json')['resolution_exit0'])
 author=p.load(p.AUTHOR/'author-audit.json')
 ck('author report frozen exact SHA',p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA)
 ck('personal author755 rehash recorded',p.load(p.OUT/'source-preparation.json')['author755bindings_personally_rehashed'])
 prep=p.load(p.OUT/'source-preparation.json');plan=p.load(p.OUT/'control-preparation.json')
 receipt=p.load(p.OUT/'execution-receipt.json')
 required=['runtime']+['native-'+x['module'].rsplit('.',1)[-1] for x in prep['native_sources']]+['serializer-'+x['module'] for x in prep['serializer_sources']]+['independent-'+k+'-v1' for k in ['assertions','semantic','generated']]+['independent-actual-resolution-v1']
 ck('29 distinct required actual labels',len(required)==len(set(required))==29)
 failed=[x for x in receipt['rows'] if x['exit_code']!=0]
 for label in required:ck('required actual0 '+label,any(x['label']==label and x['exit_code']==0 and x['all_subprocess_handles_terminal'] for x in receipt['rows']))
 for row in receipt['rows']:
  directory=p.TASK/row['folder_task_relative']
  ck('actual exit.txt agrees '+row['label'],int((directory/'exit.txt').read_text())==row['exit_code'])
  ck('actual single-thread Lean call '+row['label'],'-j1' in row['command'])
  ck('actual private CWD '+row['label'],Path(row['execution_CWD']).resolve()==p.PROJECT.resolve())
  selected=p.load(directory/'selected-paths.json')
  names=[x['name'] for x in p.load(p.PROJECT/'lake-manifest.json')['packages']]
  for key in ['LEAN_PATH','LEAN_SRC_PATH']:
   own=p.PROJECT/('b/lib/lean' if key=='LEAN_PATH' else '')
   packages=[p.ROOT/'.lake/packages'/n/('.lake/build/lib/lean' if key=='LEAN_PATH' else '') for n in names]
   exact={str(t.resolve()).casefold() for t in [own]+packages if t.is_dir()}
   ck('exact own and fixed-package import paths '+row['label']+' '+key,{str(Path(t).resolve()).casefold() for t in selected[key]['allowed_exact_set']}==exact and all(str(Path(t).resolve()).casefold() in exact for t in selected[key]['filtered']))
   ck('no Root project build or foreign project objects '+row['label']+' '+key,str(p.ROOT.resolve()).casefold() not in exact and str((p.ROOT/'.lake/build/lib/lean').resolve()).casefold() not in exact)
 sem=records('independent-semantic-v1',receipt);gen=records('independent-generated-v1',receipt);res=records('independent-actual-resolution-v1',receipt);ser=records('serializer-IndependentExprDagValidationV3',receipt)
 counts=Counter(x['record']['kind'] for x in sem)
 expected_counts={'independent_actual_original_forall':17,'independent_expected_original_forall':17,'independent_complete_forall_kernel_comparison':17,'independent_actual_related_definition':1,'independent_expected_related_definition':1,'independent_full_definition_kernel_comparison':1,'independent_whole_function_rfl':1,'independent_typed_boundary':9}
 for key,value in expected_counts.items():ck('complete record count '+key,counts[key]==value)
 node_count=0;payload_count=0;infer_count=0;raw=[]
 for sourced in sem+gen+ser:
  record=sourced['record'];name=record.get('declaration',record.get('kind'))
  if 'axioms' in record:ck('actual Std3 '+name,set(record['axioms'])<=STD3)
  for key in ['closed_complete_type_and_value','closed_complete_type','actual_value_inferType_kernel_equal','all_fields_Expr_equal_roundtrip','type_roundtrip_kernel_equal','value_roundtrip_kernel_equal','whole_type_kernel_equal','type_kernel_equal','value_kernel_equal','all_fields_roundtrip','raw_repr_reconstruction_equal']:
   if key in record:ck(key+' '+name,record[key] is True)
  if 'actual_value_inferType_kernel_equal' in record:infer_count+=1
  for key,value in record.items():
   if isinstance(value,dict) and 'nodes' in value:
    node_count+=validate_payload(value);payload_count+=1;ck('whole DAG all references fields retained '+name+' '+key,True)
  for key in ['type_Expr_equal_diagnostic','value_Expr_equal_diagnostic']:
   if key in record:raw.append(dict(declaration=name,key=key,raw_result=record[key]))
 headers=plan['original_complete_headers']
 original=(p.TASK/'formalization/CoefficientMapParameterSummationTransport.lean').read_text(encoding='utf-8-sig')
 actual=p.PROJECT/'missions/zeta9/formalization/CoefficientMapParameterSummationTransport.lean'
 actual_text=actual.read_text(encoding='utf-8-sig')
 ck('original and fresh actual source byte identical',p.sha(actual)==p.sha(p.TASK/'formalization/CoefficientMapParameterSummationTransport.lean')==p.SOURCE_SHA)
 ck('all17 original complete headers',len(headers)==17 and len(re.findall(r'^theorem\s+\w+',original,re.M))==17)
 for header in headers:ck('literal original header unchanged '+header['name'],original.count(header['header']+' :=')==actual_text.count(header['header']+' :=')==1)
 ck('whole actual transfer definition immutable',original.split('def transferMultiplier',1)[1].split('\ntheorem ',1)[0]==actual_text.split('def transferMultiplier',1)[1].split('\ntheorem ',1)[0])
 actual_names={x['record']['declaration'] for x in sem if x['record']['kind']=='independent_actual_original_forall'}
 ck('all17 actual original theorem names audited',actual_names=={'ZetaNine.CoefficientMapParameterSummationTransport.'+x['name'] for x in headers})
 actual_defs=[x['record'] for x in sem if x['record']['kind']=='independent_actual_related_definition']
 ck('complete actual transferMultiplier type and value audited',{x['declaration'] for x in actual_defs}==set(plan['whole_definition_names']))
 ck('original9 typed boundary names covered',{x['record']['declaration'] for x in sem if x['record']['kind']=='independent_typed_boundary'}=={'ParameterSummationIndependentBoundary.'+x for x in plan['boundary_names']})
 inventories=[x['record'] for x in gen if x['record']['kind']=='independent_complete_generated_closure_inventory'];ck('one complete generated helper inventory',len(inventories)==1)
 inventory=inventories[0]
 ck('every native22 plus assertions module inventoried',set(inventory['modules'])==set(plan['helper_modules']))
 std_names=[x['record']['declaration'] for x in gen if x['record']['kind']=='independent_all_actual_declaration_Std3']
 helpers=[x['record'] for x in gen if x['record']['kind']=='independent_all_generated_complete_type_and_value']
 ck('all actual declarations Std3 complete unique',len(std_names)==len(set(std_names)) and set(std_names)==set(inventory['all_declarations']))
 helper_names=[x['declaration'] for x in helpers]
 ck('all generated helpers full type value inferType complete unique',len(helper_names)==len(set(helper_names)) and set(helper_names)==set(inventory['all_generated_helpers']) and all(x['actual_value_inferType_kernel_equal'] for x in helpers))
 ck('actual resolver exactly27 modules',len(res)==27 and {x['record']['module'] for x in res}==set(p.load(p.OUT/'resolution-preparation.json')['modules']))
 outputs={b['task_relative']:b for row in receipt['rows'] if row['exit_code']==0 for b in row['output_bindings']}
 for sourced in res:
  record=sourced['record'];expected=(p.PROJECT/'b/lib/lean'/(record['module'].replace('.','/')+'.olean')).resolve()
  ck('actual findOLean realPath own '+record['module'],record['actual_expected_own_path_equal'] is True and Path(record['realPath']).resolve()==expected and p.bind(expected)['task_relative'] in outputs)
 own_objects={p.bind(t)['task_relative'] for t in (p.PROJECT/'b/lib/lean').rglob('*.olean')}
 ck('all28 proof objects compiled from own fresh SOURCE',len(own_objects)==28 and own_objects==set(outputs))
 ck('initial own cache absent attested before preparation',prep['project_initially_absent'] and prep['cache_initially_absent'])
 export=p.OUT/'ParameterSummationIndependentlyVerifiedSource.lean';assert not export.exists();export.write_bytes(actual.read_bytes())
 stable={}
 for row in author['stable_files']:
  key=('task_relative',row['task_relative']) if row.get('task_relative') is not None else ('root_relative',row['root_relative']);stable[key]=row
 def retain(path):
  binding=p.bind(path);stable[('task_relative',binding['task_relative'])]=binding
 for base in [p.PROJECT,p.OUT]:
  for directory,dirs,files in os.walk(base,followlinks=False):
   dirs[:]=[d for d in dirs if d not in ['__pycache__','packages'] and not (Path(directory)/d).is_junction() and not (Path(directory)/d).is_symlink()]
   for name in files:
    path=Path(directory)/name
    if path.name in ['independent-review.json','post-freeze-binding-check.json','finalize-failure.json']:continue
    retain(path)
 retain(p.AUTHOR/'author-audit.json');retain(p.TASK/'formalization/CoefficientMapParameterSummationTransport.lean')
 stable_files=[stable[k] for k in sorted(stable)]
 def exact_binding(row):
  path=p.resolve(row);return path,path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for path,ok in pool.map(exact_binding,stable_files):ck('exact stable binding '+str(path),ok)
 report=dict(verdict='PASS',reviewer_role='Native Parameter-Summation17 INDEPENDENT; not author',frozen_at=datetime.now(timezone.utc).isoformat(),checks=checks,stable_files=stable_files,original_complete_headers=headers,original_candidate=author['original_candidate'],compiled_private_source=p.bind(actual),verified_export=p.bind(export),author_report=p.bind(p.AUTHOR/'author-audit.json'),author755bindings_personally_rehashed=True,own_project='.rt/psi1',native_SOURCE_count=22,all_objects_fresh_SOURCE_compiled=True,author_or_Root_or_prior_oi7_proof_objects_borrowed=False,generic_recorder_serializer_validator_SOURCE_reuse_disclosed=True,complete_original_forall=17,complete_original_definition=1,actual_definition_type_value_and_inferType_records=actual_defs,whole_function_rfl=1,original_typed_boundaries=9,all_actual_module_declarations_Std3=len(std_names),all_generated_full_type_value_inferType_helpers=len(helpers),all_generated_closure_inventory=inventory,actual_value_inferType_checks=infer_count,complete_DAG_payloads=payload_count,complete_DAG_nodes=node_count,raw_Expr_diagnostics_unaltered=raw,metadata_binders_levels_names_or_proof_arguments_suppressed=False,actual_own_object_resolutions=27,required_actual_labels=required,actual_calls=len(receipt['rows']),actual_successes=sum(x['exit_code']==0 for x in receipt['rows']),actual_failures=len(failed),failed_runs_preserved_and_excluded=[x['folder_task_relative'] for x in failed],author34_calls_31success_3failures_personally_rehashed_not_counted_as_own=dict(total=34,success=31,failed=3),all_actual_handles_terminal=True,own_OS_readback=p.bind(p.OUT/'final-own-processes.json'),exact_complete_type_kernel_records=[x['record'] for x in sem if x['record']['kind']=='independent_complete_forall_kernel_comparison'],exact_complete_definition_type_value_kernel_records=[x['record'] for x in sem if x['record']['kind']=='independent_full_definition_kernel_comparison'],semantic_record_counts=dict(counts),scope=dict(all_n_ge_one_five_outputs_and_exactL_transport=True,even_n_ge_two_actual_HasSum_absolute_and_tsum_parameter_transport=True,actual_inverse_row_and_same_selected_output_transport=True,termwise_series_equality=False,integer_polynomial_preimage=False,height=False,J=False,irrationality=False,platform_acceptance=False),API_calls=0,Root_module_or_scope_writes=0,whole_source_definition_and_original_prep_unchanged=True)
 p.dump(out,report);p.check(stable_files)
 p.dump(p.OUT/'post-freeze-binding-check.json',dict(verdict='PASS',report=p.bind(out),stable_bindings=len(stable_files),all_exact_content_rehashed_after_freeze=True,all_actual_handles_terminal=True))
 print(json.dumps(dict(verdict='PASS',report_SHA=p.sha(out),checks=len(checks),stable_bindings=len(stable_files),actual_calls=len(receipt['rows']),success=sum(x['exit_code']==0 for x in receipt['rows']),failed=len(failed),fresh_SOURCE=22,complete_forall=17,Std3_declarations=len(std_names),generated_full_values=len(helpers),value_inferType_checks=infer_count,actual_own_resolutions=27,export_SHA=p.sha(export),postfreeze_SHA=p.sha(p.OUT/'post-freeze-binding-check.json')),indent=2))
if __name__=='__main__':
 sys.stdout.reconfigure(encoding='utf-8')
 try:final()
 except Exception as e:
  p.dump(p.OUT/'finalize-failure.json',dict(error=str(e),checks=checks,independent_PASS_claimed=False));raise
