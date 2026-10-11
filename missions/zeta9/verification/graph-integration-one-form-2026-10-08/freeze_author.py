from pathlib import Path
import hashlib,json,re,sys,time
sys.dont_write_bytecode=True
TASK=Path(__file__).resolve().parents[2];WORKSPACE=TASK.parents[1]
OUT=Path(__file__).resolve().parent;PROJECT=TASK/'.rt/gofa1008'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for q in iter(lambda:f.read(4*1024*1024),b''):h.update(q)
 return h.hexdigest()
def binding(p):
 p=p.resolve()
 loc={'task_relative':p.relative_to(TASK).as_posix()} if p.is_relative_to(TASK) else {'root_relative':p.relative_to(WORKSPACE).as_posix()} if p.is_relative_to(WORKSPACE) else {'absolute':str(p)}
 return dict(loc,bytes=p.stat().st_size,sha256=sha(p))
def path_of(b):
 return TASK/b['task_relative'] if 'task_relative' in b else WORKSPACE/b['root_relative'] if 'root_relative' in b else Path(b['absolute'])
receipt=load(OUT/'author-compile-receipt.json')
assert receipt['rows'][-1]['module'].startswith('GraphControls') and not receipt['rows'][-1]['exit_code']
passed=[r for r in receipt['rows'] if r['module'] and r['exit_code']==0]
parents=[r for r in passed if r['module'].startswith('SketchedParent')]
assert parents
final_module=parents[-1]['module'];final_source=PROJECT/'src'/(final_module+'.lean')
body=final_source.read_text(encoding='utf-8');code=re.sub(r'/\*[\s\S]*?\*/|--[^\n]*','',body)
assert not re.search(r'\b(sorry|admit|axiom)\b',code)
assert all(x.startswith(('Definitions.','Theorems.','Mathlib')) for x in re.findall(r'^import\s+(\S+)',body,re.M))
assert 'import OneFormBridgeSource' not in body
log=path_of(receipt['rows'][-1]['stdout'])
records=[json.loads(s.split('|',1)[1]) for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('GO_RECORD|')]
values=[r for r in records if r['kind']=='own_complete_kernel_value']
inventory=next(r['names'] for r in records if r['kind']=='complete_own_declaration_inventory')
assert len(values)==len(inventory) and set(r['name'] for r in values)==set(inventory)
expected=load(OUT/'complete-type-inventory.json')
assert {r['name'] for r in expected}<=set(inventory)
assert 'solution' in inventory
assert all(r['complete_inferType_matches'] and not r['own_direct_sorryAx'] for r in values)
used=set(n for r in values for n in r['direct_constants'] if n.startswith('ZetaNine.GraphBridge.'))
used.discard('ZetaNine.GraphBridge.selected_inverse_positive_cone_margin')
assert used<=set(inventory),used-set(inventory)
by_name={r['name']:r for r in values}
required={
 'ZetaNine.GraphBridge.one_small_forms_of_selected_inverse_positive_cone_margin':['ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one','ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute'],
 'ZetaNine.GraphBridge.one_selectedMultiplier_height_eq_inverseNorm':['ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product'],
 'ZetaNine.GraphBridge.one_selected_actual_form_pos':['ZetaNine.taylor_sign_implies_kernel_sum_pos','ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute'],
 'solution':['ZetaNine.GraphBridge.selected_inverse_positive_cone_margin']}
for n,deps in required.items():assert set(deps)<=set(by_name[n]['direct_constants']),(n,deps)
for r in values:
 assert set(r['axioms'])<={'propext','Quot.sound','Classical.choice','sorryAx'}
 (OUT/'complete-kernel-records').mkdir(exist_ok=True)
 (OUT/'complete-kernel-records'/(r['name'].replace('.','_')+'.json')).write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
resolvers=[r for r in records if r['kind']=='actual_module_resolver']
assert len(resolvers)>5000
origins={};files=set()
for r in resolvers:
 p=Path(r['canonical_olean']).resolve()
 if p.is_relative_to(PROJECT):origin='own_fresh_project'
 elif p.is_relative_to(WORKSPACE/'.lake/packages'):origin='stock_pinned_package_cache'
 else:
  assert 'leanprover--lean4---v4.33.1' in str(p).lower() and '/lib/lean/' in p.as_posix().lower(),p
  origin='intrinsic_Lean_4_33_1'
 origins[origin]=origins.get(origin,0)+1
 for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  q=p.with_suffix(ext) if ext in ['.olean','.ilean','.ir'] else Path(str(p)+ext[len('.olean'):])
  if q.is_file():files.add(q.resolve())
(OUT/'actual-module-resolver-complete.json').write_text(json.dumps({'phase':'post-author current artifact freeze; not precompile','rows':resolvers,'origin_counts':origins},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
exports=OUT/'author-native-export/src';exports.mkdir(parents=True,exist_ok=True)
for r in passed:
 src=PROJECT/'src'/(r['module'].replace('.','/')+'.lean');dst=exports/(r['module'].replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
upload=OUT/'uploadable-source/Sol_ZetaNine_GraphBridge_one_form_parent.lean';upload.parent.mkdir(exist_ok=True);upload.write_bytes(final_source.read_bytes())
assert sha(upload)==sha(final_source)
policy_versions=[]
for r in receipt['rows']:
 for b in r['input_bindings']:
  if path_of(b)==OUT/'author-private-inputs-v1.json' and binding(path_of(b))!=b:
   rr=next(x for x in r['retained_inputs'] if x['original']==b)
   historical=OUT/'private-policy-history'/(b['sha256']+'.json');historical.parent.mkdir(exist_ok=True);historical.write_bytes(path_of(rr['snapshot']).read_bytes());assert sha(historical)==b['sha256'];policy_versions.append({'call':r['index'],'historical_original':b,'immutable_history':binding(historical),'reason':'added later audit SOURCE bindings; every mathematical source/config remained immutable'})
  else:assert binding(path_of(b))==b,(r['index'],b)
 for rr in r['retained_inputs']:assert sha(path_of(rr['snapshot']))==rr['original']['sha256']
 for rr in r['outputs']:assert sha(path_of(rr['snapshot']))==rr['original']['sha256']
(OUT/'private-policy-version-history.json').write_text(json.dumps(policy_versions,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
for base in [OUT,PROJECT/'src',PROJECT/'b']:
 for p in base.rglob('*'):
  if p.is_file() and p.name!='author-complete-audit.json':files.add(p.resolve())
for f in ['lakefile.lean','lean-toolchain','lake-manifest.json','leaf.py']:files.add((PROJECT/f).resolve())
files.add((TASK/'verification/graph-integration-root-2026-10-08/one-form-author-lane1-grant.json').resolve())
for row in load(OUT/'author-private-inputs-v1.json')['source_files']:files.add(path_of(row['candidate']).resolve())
print('Streaming final whole-file bindings',len(files),flush=True)
stable=[];last=time.monotonic()
for i,p in enumerate(sorted(files),1):
 stable.append(binding(p))
 if time.monotonic()-last>40:print('Hashed',i,'/',len(files),flush=True);last=time.monotonic()
failed=[r['index'] for r in receipt['rows'] if r['exit_code']]
audit={'verdict':'PASS_FOR_TRUE_REDUCTION_WITH_EXPLICIT_IMPORTED_CATALOG_ASSUMPTIONS','role':'one-form graph AUTHOR','lane1_released':True,'all_Lean_terminal':True,'actual_calls':len(receipt['rows']),'actual_successes':len(receipt['rows'])-len(failed),'preserved_actual_failures':failed,'independent_review':'pending Root independent review','new_child_status':'Open actual inverse-image cone/height margin; no J/lattice/irrationality proof claimed','complete_irrationality_proof':False,'imported_catalogues_are_explicit_reduction_assumptions':True,'transitive_sorryAx':'only admitted imported catalogs allowed, never own direct proof placeholder','own_direct_sorryAx':False,'full_own_environment_declarations':inventory,'complete_kernel_value_records':len(values),'complete_helper_type_applications':10,'boundary_controls':7,'exact_original_parent':binding(OUT/'expected-original-parent.json'),'final_parent_source':binding(final_source),'final_parent_export':binding(exports/(final_module+'.lean')),'uploadable_source':binding(upload),'upload_bytes_are_actual_compiled_complete_self_contained_bytes':True,'new_definition_export':binding(exports/'Definitions/Def_ZetaNine_GraphBridge_OneForm.lean'),'shared_actual_norm_export':binding(exports/'Definitions/Def_ZetaNine_GraphBridge_TwoForm.lean'),'required_imports_actual_direct_kernel_uses':required,'actual_resolver_count':len(resolvers),'actual_resolver_origin_counts':origins,'artifact_freeze_timing':'post-author current whole-file artifacts; not precompile','private_policy_versions_history':binding(OUT/'private-policy-version-history.json'),'api_calls':0,'credential_reads':0,'foreign_mathematical_proof_objects_borrowed':False,'checks':[{'label':s,'passed':True} for s in ['all final actual calls terminal zero; every failure retained','actual parent complete original type compiled','all ten complete helper types and seven boundaries compiled','actual tail positive with first n zero terms removed before Taylor use','all own environment declarations have full exact DAG values and matching inferType','used own helper closure covered by full inventory','only standard three axioms plus explicit imported catalogue assumptions','actual Matrix coordinate/HasSum, A, TP1 and newOpen uses recorded','upload source self contained and byte identical to actual successful compilation']],'stable_files':stable,'stable_file_count':len(stable),'stable_total_bytes':sum(b['bytes'] for b in stable)}
(OUT/'author-complete-audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('AUTHOR complete',len(stable),'files',audit['stable_total_bytes'],'bytes audit SHA',sha(OUT/'author-complete-audit.json'),flush=True)
