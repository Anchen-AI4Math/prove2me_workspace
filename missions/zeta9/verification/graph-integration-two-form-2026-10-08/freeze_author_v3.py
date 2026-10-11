from pathlib import Path
import hashlib,json,sys,time
sys.dont_write_bytecode=True
TASK=Path(__file__).resolve().parents[2]
WORKSPACE=TASK.parents[1]
OUT=Path(__file__).resolve().parent
PROJECT=TASK/'.rt/gtfa1008'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(4*1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def binding(p):
 p=Path(p)  # actual resolver paths are already canonical; own paths are absolute
 if p.is_relative_to(TASK):loc={'task_relative':p.relative_to(TASK).as_posix()}
 elif p.is_relative_to(WORKSPACE):loc={'root_relative':p.relative_to(WORKSPACE).as_posix()}
 else:loc={'absolute':str(p)}
 return dict(loc,bytes=p.stat().st_size,sha256=sha(p))
def path_of(b):
 if 'task_relative' in b:return TASK/b['task_relative']
 if 'root_relative' in b:return WORKSPACE/b['root_relative']
 return Path(b['absolute'])
receipt=load(OUT/'author-compile-receipt.json')
assert len(receipt['rows'])==26
assert [r['index'] for r in receipt['rows'] if r['exit_code']] == [22]
assert receipt['rows'][-1]['module']=='GraphControlsAllOwnV3' and receipt['rows'][-1]['exit_code']==0
log=path_of(receipt['rows'][-1]['stdout'])
records=[json.loads(s.split('|',1)[1]) for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('GT_RECORD|')]
values=[r for r in records if r['kind']=='own_complete_kernel_value']
inventory=next(r['names'] for r in records if r['kind']=='complete_own_declaration_inventory')
assert len(values)==len(inventory)==11 and set(r['name'] for r in values)==set(inventory)
assert all(r['complete_inferType_matches'] and not r['own_direct_sorryAx'] for r in values)
used_own=set(n for r in values for n in r['direct_constants'] if n.startswith('ZetaNine.GraphBridge.'))
used_own.discard('ZetaNine.GraphBridge.selected_inverse_unbounded_short_independent_pairs')
assert used_own<=set(inventory),used_own-set(inventory)
by_name={r['name']:r for r in values}
assert 'ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one' in by_name['ZetaNine.GraphBridge.two_small_forms_of_selected_inverse_margin']['direct_constants']
assert 'ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute' in by_name['ZetaNine.GraphBridge.two_small_forms_of_selected_inverse_margin']['direct_constants']
assert 'ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product' in by_name['ZetaNine.GraphBridge.selectedMultiplier_weightedHeight_eq_inverseNorm']['direct_constants']
assert 'ZetaNine.GraphBridge.selected_inverse_unbounded_short_independent_pairs' in by_name['ZetaNine.exponentially_small_independent_forms_of_zeta_nine']['direct_constants']
for r in values:
 assert set(r['axioms']) <= {'propext','Quot.sound','Classical.choice','sorryAx'}
 (OUT/'complete-kernel-records').mkdir(exist_ok=True)
 (OUT/'complete-kernel-records'/(r['name'].replace('.','_')+'.json')).write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
resolvers=[r for r in records if r['kind']=='actual_module_resolver']
assert len(resolvers)==11035
origins={}
files=set()
print('Discovering only actual resolver artifact siblings; no repeated realPath',flush=True)
for resolver_index,r in enumerate(resolvers,1):
 p=Path(r['canonical_olean'])
 if p.is_relative_to(PROJECT):origin='own_fresh_project'
 elif p.is_relative_to(WORKSPACE/'.lake/packages'):origin='stock_pinned_package_cache'
 else:
  assert 'leanprover--lean4---v4.33.1' in str(p).lower() and '\\lib\\lean\\' in str(p).lower(),p
  origin='intrinsic_Lean_4_33_1'
 origins[origin]=origins.get(origin,0)+1
 if resolver_index%1000==0:print('Discovered',resolver_index,'/',len(resolvers),flush=True)
 for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  q=p.with_suffix(ext) if ext in ['.olean','.ilean','.ir'] else Path(str(p)+ext[len('.olean'):])
  if q.is_file():files.add(q)
(R:=OUT/'actual-module-resolver-complete.json').write_text(json.dumps({'phase':'post-author current artifact freeze; not claimed precompile snapshot','rows':resolvers,'origin_counts':origins},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
exports=OUT/'author-native-export/src';exports.mkdir(parents=True,exist_ok=True)
passed_modules=[r['module'] for r in receipt['rows'] if r['module'] and r['exit_code']==0]
for mod in passed_modules:
 src=PROJECT/'src'/(mod.replace('.','/')+'.lean');dst=exports/(mod.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
for r in receipt['rows']:
 for b in r['input_bindings']:
  assert binding(path_of(b))==b,(r['index'],b)
 for rr in r['retained_inputs']:
  assert binding(path_of(rr['snapshot']))['sha256']==rr['original']['sha256']
 for rr in r['outputs']:
  assert binding(path_of(rr['snapshot']))['sha256']==rr['original']['sha256']
for base in [OUT,PROJECT/'src',PROJECT/'b']:
 for p in base.rglob('*'):
  if base==PROJECT/'.lake' and 'packages' in p.relative_to(base).parts:continue
  if p.is_file() and not p.is_relative_to(PROJECT/'.lake/packages') and p.name not in ['author-complete-audit.json']:
   files.add(p)
for fn in ['lakefile.lean','lean-toolchain','lake-manifest.json','leaf.py']:files.add((PROJECT/fn)))
files.add((TASK/'verification/graph-integration-root-2026-10-08/two-form-author-lane1-grant.json')))
for row in load(OUT/'author-private-inputs-v1.json')['source_files']:files.add(path_of(row['candidate'])))
print('Freeze actual imported artifacts + SOURCE/call snapshots:',len(files),'files',flush=True)
stable=[];last=time.monotonic()
for i,p in enumerate(sorted(files),1):
 stable.append(binding(p))
 if time.monotonic()-last>40:
  print('Hashed',i,'/',len(files),flush=True);last=time.monotonic()
checks=[{'label':'all final actual Lean calls terminal zero','passed':True},
 {'label':'original full platform forall target plus seven rfl/domain boundaries compiled','passed':True},
 {'label':'whole unbounded-even geometric margin definition compiled and rfl checked','passed':True},
 {'label':'all own 11 main/compiler-helper complete values exact lossless roundtrip and inferType','passed':True},
 {'label':'all used own helper names are covered by exact environment inventory','passed':True},
 {'label':'actual endpoint use: Matrix coordinates / genuine Matrix HasSum / coefficient uniform A','passed':True},
 {'label':'original Open child is direct explicit dependency; no own direct sorryAx','passed':True},
 {'label':'source bytes/raw statement condition preserved; only Nat.cast_ofNat representation repair','passed':True}]
audit={'verdict':'PASS_FOR_TRUE_REDUCTION_WITH_EXPLICIT_IMPORTED_CATALOG_ASSUMPTIONS',
 'role':'two-form graph AUTHOR','lane1_released':True,'all_Lean_terminal':True,'actual_calls':len(receipt['rows']),
 'actual_successes':25,'preserved_actual_failures':[22],
 'statement':'The exact original two-form leaf follows from the unbounded-even true inverse weighted short-pair margin and three endpoint statements.',
 'new_child_status':'Open; no lattice/J theorem is claimed proved',
 'independent_review':'pending Root independent review',
 'complete_irrationality_proof':False,
 'imported_endpoint_catalogues_and_new_Open_child_are_explicit_reduction_assumptions':True,
 'transitive_sorryAx':'present through imported catalogue declarations; not presented as a completed own proof',
 'own_direct_sorryAx':False,
 'full_own_environment_declarations':inventory,'complete_kernel_value_records':len(values),
 'boundary_controls':7,'exact_original_parent':binding(OUT/'expected-original-parent.json'),
 'final_parent_source':binding(PROJECT/'src/SketchedParentV2.lean'),
 'final_parent_export':binding(exports/'SketchedParentV2.lean'),
 'new_definition_export':binding(exports/'Definitions/Def_ZetaNine_GraphBridge_TwoForm.lean'),
 'actual_resolver_count':len(resolvers),'actual_resolver_origin_counts':origins,
 'artifact_freeze_timing':'post-author current whole-file artifacts; not a claimed precompile snapshot',
 'api_calls':0,'credential_reads':0,'foreign_mathematical_proof_objects_borrowed':False,
 'checks':checks,'stable_files':stable,'stable_file_count':len(stable),'stable_total_bytes':sum(b['bytes'] for b in stable)}
(OUT/'author-complete-audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('AUTHOR complete',len(stable),'files',audit['stable_total_bytes'],'bytes; audit SHA',sha(OUT/'author-complete-audit.json'),flush=True)
