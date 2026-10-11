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
 out=p.OUT/'independent-audit.json';assert not out.exists()
 import run_independent as engine
 engine.gate()
 ck('all actual compiler handles terminal with OS own0',p.load(p.OUT/'final-own-processes.json')==[] and p.load(p.OUT/'controls-terminal.json')['all_actual_handles_terminal'])
 prep=p.load(p.OUT/'source-preparation.json');plan=p.load(p.OUT/'target-plan.json');controls=p.load(p.OUT/'control-preparation.json');receipt=p.load(p.OUT/'execution-receipt.json')
 ck('native independent final report exact pinned',p.sha(p.INDEP/'independent-audit.json')==p.INDEP_SHA)
 ck('native independent Root26076 full binding gate exact',p.load(p.ROOT_GATE)['mismatches']==0 and p.load(p.ROOT_GATE)['Root_personally_stream_rehashed_all'])
 p.check(prep['stable_files'])
 failed=[r for r in receipt['rows'] if r['exit_code']!=0]
 required=[('native','runtime')]+[(c['tag'],r['label']) for c in prep['contexts'] for r in c['math_sources']]+[(c['tag'],r['label']) for c in controls['contexts'] for r in c['rows']]
 for tag,label in required:ck('actual0 '+tag+'/'+label,any(r['tag']==tag and r['label']==label and r['exit_code']==0 and r['all_actual_handles_terminal'] for r in receipt['rows']))
 ck('exact42 required calls',len(required)==42)
 for row in receipt['rows']:
  directory=p.TASK/row['folder_task_relative'];ck('actual exit receipt '+row['tag']+'/'+row['label'],int((directory/'exit.txt').read_text())==row['exit_code'])
  paths=p.load(directory/'selected-paths.json');ctx=p.PROJECT/row['tag']
  for key in ['LEAN_PATH','LEAN_SRC_PATH']:
   own=ctx/('b/lib/lean' if key=='LEAN_PATH' else '')
   names=[x['name'] for x in p.load(ctx/'lake-manifest.json')['packages']]
   exact={str(x.resolve()).casefold() for x in [own]+[p.ROOT/'.lake/packages'/n/('.lake/build/lib/lean' if key=='LEAN_PATH' else '') for n in names] if x.is_dir()}
   ck('own context or pinned packages only '+row['tag']+'/'+row['label']+' '+key,{str(Path(x).resolve()).casefold() for x in paths[key]['allowed_exact_set']}==exact and all(str(Path(x).resolve()).casefold() in exact for x in paths[key]['filtered']))
  for pair in row['immutable_snapshots']:ck('immutable original snapshot SHA '+pair['retained']['task_relative'],pair['original']['bytes']==pair['retained']['bytes'] and pair['original']['sha256']==pair['retained']['sha256'])
 def get_records(tag,label):
  row=next(r for r in reversed(receipt['rows']) if r['tag']==tag and r['label']==label and r['exit_code']==0)
  path=p.TASK/row['folder_task_relative']/'stdout.log'
  result=[]
  for line in path.open(encoding='utf-8'):
   if line.startswith('{'):
    item=json.loads(line)
    if 'kind'in item:result.append(item)
  return result
 summary={};raw=[];payload_count=0;node_count=0;stock_files={};all_proof_modules=[]
 for context in controls['contexts']:
  tag=context['tag'];semantic=get_records(tag,'control-semantic');resolver=get_records(tag,'control-resolver');fixture=get_records(tag,'own-PhasePlatformExprDagValidationV1');counts=Counter(r['kind'] for r in semantic)
  ck('whole seven actual definition records '+tag,counts['actual_full_definition']==7 and counts['oracle_full_definition']==7 and counts['independent_full_definition_kernel_comparison']==7 and counts['actual_whole_function_rfl']==7)
  if context['proof_context']:ck('all34 exact actual and oracle fullforall plus15bounds '+tag,counts['actual_original_forall']==counts['oracle_original_forall']==34 and counts['actual_complete_solution']==1 and counts['independent_complete_forall_kernel_comparison']==35 and counts['actual_typed_boundary']==15)
  for record in semantic+fixture:
   name=record.get('declaration',record.get('source_name',record['kind']))
   if 'axioms'in record:ck('actual Std3 '+tag+' '+name,set(record['axioms'])<=STD3)
   for key in ['closed_complete_type_and_value','closed_complete_type','actual_value_inferType_kernel_equal','all_fields_Expr_equal_roundtrip','type_roundtrip_kernel_equal','value_roundtrip_kernel_equal','whole_type_kernel_equal','type_kernel_equal','value_kernel_equal','all_fields_roundtrip','raw_repr_reconstruction_equal']:
    if key in record:ck(key+' '+tag+' '+name,record[key] is True)
   for key,value in record.items():
    if isinstance(value,dict) and 'nodes'in value:node_count+=validate_payload(value);payload_count+=1;ck('full DAG topology '+tag+' '+name+' '+key,True)
   for key in ['type_Expr_equal_diagnostic','value_Expr_equal_diagnostic']:
    if key in record:raw.append(dict(tag=tag,declaration=name,key=key,raw_result=record[key]))
  inventory=[r for r in semantic if r['kind']=='independent_complete_generated_closure_inventory'];ck('one actual full helper inventory '+tag,len(inventory)==1)
  inventory=inventory[0];helpers=[r for r in semantic if r['kind']=='independent_all_generated_complete_type_and_value'];std=[r for r in semantic if r['kind']=='independent_all_actual_declaration_Std3']
  ck('complete native oracle and actual module inventories '+tag,set(inventory['modules'])==set(context['own_mathematical_modules']))
  ck('all actual declarations Std3 covered '+tag,len(std)==len(set(r['declaration'] for r in std)) and {r['declaration'] for r in std}==set(inventory['all_declarations']))
  ck('all actual helper full type value and inferType covered '+tag,len(helpers)==len(set(r['declaration'] for r in helpers)) and {r['declaration'] for r in helpers}==set(inventory['all_generated_helpers']))
  if context['proof_context']:
   complete_values=[r for r in semantic if 'actual_value_inferType_kernel_equal' in r]
   ck('EVERY original proof definition wrapper boundary and reachable helper has full value/inferType '+tag,len(complete_values)==len({r['declaration'] for r in complete_values}) and {r['declaration'] for r in complete_values}==set(inventory['all_declarations']))
  own=[r for r in resolver if r['kind']=='actual_own_object_resolution'];ck('all own actual object resolver names '+tag,{r['module'] for r in own}==set(context['own_resolver_expected']) and all(r['own_exact'] for r in own))
  packages=[p.ROOT/'.lake/packages'/n/'.lake/build/lib/lean' for n in [x['name'] for x in p.load(p.PROJECT/tag/'lake-manifest.json')['packages']]]
  ownroot=(p.PROJECT/tag/'b/lib/lean').resolve();intrinsic=Path(r'C:\Users\anche\.elan\toolchains\leanprover--lean4---v4.33.1\lib\lean').resolve()
  imports=[r for r in resolver if r['kind']=='actual_import_origin']
  for record in imports:
   path=Path(record['realPath']).resolve();ok=path.is_relative_to(ownroot) or path.is_relative_to(intrinsic) or any(path.is_relative_to(x.resolve()) for x in packages)
   ck('actual imported module origin own stock or intrinsic '+tag+' '+record['module'],ok and path.is_file())
   for file in path.parent.glob(path.name+'*'):
    if file.is_file():stock_files[str(file.resolve()).casefold()]=p.bind(file)
  summary[tag]=dict(semantic_counts=dict(counts),declarations_Std3=len(std),generated_helpers_full_values=len(helpers),actual_import_modules=len(imports),actual_own_object_resolutions=len(own),value_inferType_checks=sum('actual_value_inferType_kernel_equal'in r for r in semantic),whole_definitions=7,whole_function_rfl=7,full_forall=34 if context['proof_context'] else 0,typed_boundaries=15 if context['proof_context'] else 0,whole_definition_kernel_pairs=[r for r in semantic if r['kind']=='independent_full_definition_kernel_comparison'],whole_type_kernel_pairs=[r for r in semantic if r['kind']=='independent_complete_forall_kernel_comparison'])
 for payload in prep['payloads']:
  p.check([payload['binding'],payload['author_source'],payload['publication_copy']])
  ck('exact business SOURCE bytes author/own/publication '+payload['path'],p.resolve(payload['binding']).read_bytes()==p.resolve(payload['author_source']).read_bytes()==p.resolve(payload['publication_copy']).read_bytes())
 ck('seven exact payloads staged',len(prep['payloads'])==7)
 # Statements deliberately contain sorry only as formal type catalog, never imported by a proof.
 for target in plan['targets']:
  solution=(p.OUT/'staged'/target['local_solution']).read_text(encoding='utf-8');reference=(p.OUT/'staged'/target['local_reference']).read_text(encoding='utf-8')
  ck('complete proof lacks holes and catalog imports '+target['theorem_name'],not re.search(r'\b(sorry|admit|axiom|native_decide)\b',solution) and 'import Theorems.' not in solution)
  for declaration in prep['native_theorems']:ck('all original34 header preserved in exact payload '+target['theorem_name']+' '+declaration['name'],solution.count(declaration['header']+' :=')==1)
  ck('exact registered endpoint original header '+target['theorem_name'],target['exact_original_header'].replace('theorem '+target['theorem_name'].rsplit('.',1)[-1],'theorem '+target['theorem_name'],1)+' := by sorry' in reference)
 stable={str(p.resolve(b).resolve()).casefold():b for b in prep['stable_files']}
 for payload in prep['payloads']:
  for field in ['author_source','publication_copy']:
   b=payload[field];stable[str(p.resolve(b).resolve()).casefold()]=b
 for key,b in stock_files.items():stable[key]=b
 for base in [p.OUT,p.PROJECT]:
  for directory,dirs,files in os.walk(base,followlinks=False):
   dirs[:]=[d for d in dirs if d not in ['__pycache__','packages'] and not (Path(directory)/d).is_junction() and not (Path(directory)/d).is_symlink()]
   for name in files:
    if name in ['independent-audit.json','post-freeze-binding-check.json','finalize-failure.json']:continue
    path=Path(directory)/name;stable[str(path.resolve()).casefold()]=p.bind(path)
 stable_files=[stable[k] for k in sorted(stable)]
 def exact(row):
  path=p.resolve(row);return path,path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for path,ok in pool.map(exact,stable_files):ck('exact frozen binding '+str(path),ok)
 report=dict(verdict='PASS',role='Analytic Phase platform INDEPENDENT; distinct from platform and native authors',checks=checks,stable_files=stable_files,native_author_report=p.bind(p.AUTHOR/'author-audit.json'),native_independent_report=p.bind(p.INDEP/'independent-audit.json'),Root_native_full_binding_gate=p.bind(p.ROOT_GATE),payloads=prep['payloads'],platform_author_report=p.bind(p.BATCH/'author-audit.json'),personal_author_full_binding_rehash=p.bind(p.OUT/'personal-author-complete-binding-rehash.json'),target_plan=p.bind(p.OUT/'target-plan.json'),context_results=summary,all_contexts_initially_absent=True,actual_calls=len(receipt['rows']),actual_successes=sum(r['exit_code']==0 for r in receipt['rows']),actual_failures=len(failed),whole_failed_runs_preserved_and_excluded=[r['folder_task_relative'] for r in failed],all_actual_handles_terminal=True,actual_OS_readback=p.bind(p.OUT/'final-own-processes.json'),raw_Expr_diagnostics_unaltered=raw,raw_Expr_namespace_alias_differences_are_not_erased=True,complete_DAG_payloads=payload_count,complete_DAG_nodes=node_count,whole7_definition_source_bytes_and34_original_headers_preserved=True,all_source_standalone_Mathlib_plus_one_actual_Definition=True,foreign_math_olean_borrowed=False,each_solution_own_fresh_source_context_required_and_verified=True,namespace_oracle_SOURCE_only_reuse_disclosed=True,native_boundary_and_generic_meta_serializer_SOURCE_reuse_disclosed=True,statement_references_are_only_type_catalog_never_complete_proofs=True,Scope=dict(actual_phase_domain_x_gt_one=True,actual_certified_bound_strict_minus10564011_over1000000=True,actual_global_bound_minus2641_over250=True,full_Z9_A=False,J=False,integer_height=False,irrationality=False),API_calls=0,Root_scope_shared_module_writes=0,platform_independent_review_completed=True,platform_publication_or_acceptance_claimed=False)
 categories=Counter()
 for row in receipt['rows']:
  if row['label']=='runtime':category='runtime'
  elif row['label'].startswith('control-'):category='controls'
  elif row['label'].startswith('reference-type-only-'):category='statement_type_catalog_SOURCE'
  elif row['label'].startswith('own-PhasePlatformExprDag'):category='generic_serializer_SOURCE'
  else:category='complete_mathematical_SOURCE'
  categories[category]+=1
 report['actual_call_categories']=dict(categories)
 report['all_actual_proof_context_declarations_have_full_value_and_inferType']=True
 report['all_seven_author_own_and_publication_SOURCE_bytes_verified']=True
 p.dump(out,report);p.check(stable_files);p.dump(p.OUT/'post-freeze-binding-check.json',dict(verdict='PASS',report=p.bind(out),stable_bindings=len(stable_files),all_exact_after_freeze=True))
 print(json.dumps(dict(verdict='PASS',report_SHA=p.sha(out),checks=len(checks),bindings=len(stable_files),actual_calls=len(receipt['rows']),success=sum(r['exit_code']==0 for r in receipt['rows']),failures=len(failed),payloads=7,context_summaries={k:{kk:vv for kk,vv in v.items() if kk not in ['whole_definition_kernel_pairs','whole_type_kernel_pairs','semantic_counts']} for k,v in summary.items()},postfreeze_SHA=p.sha(p.OUT/'post-freeze-binding-check.json')),indent=2))
if __name__=='__main__':
 sys.stdout.reconfigure(encoding='utf-8')
 try:final()
 except Exception as e:p.dump(p.OUT/'finalize-v2-failure.json',dict(error=str(e),checks=checks,independent_PASS_claimed=False));raise
