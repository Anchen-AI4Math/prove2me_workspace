"""Build the genuine Equiv proof field from actual fresh graph/parser outputs.
This helper executes no Lean. It refuses absent/incomplete source oracles.
"""
from pathlib import Path
import hashlib,json,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT/'p';BUILD=TASK/'.rt/k1/b'
NS='ZetaNine.CoefficientMapKernelBridge';SEED=NS+'.original_five_dimensional_map_bijective'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(l) for l in p.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,j):write(p,json.dumps(j,ensure_ascii=False,indent=2)+'\n')
def edit(data,edits):
 edge=len(data)
 for a,b,v in sorted(set(edits),reverse=True):
  assert 0<=a<=b<=edge,'Conflicting parser-owned source edits'
  data=data[:a]+v+data[b:];edge=a
 return data
plan=load(OUT/'preparation-state.json');expected=plan['sources_sha256']
receipt=load(OUT/'compile-receipt.json')
assert receipt['source_sha256']==expected and receipt.get('native_and_staged_objects_borrowed') is False
successful={r['label']:r for r in receipt['rows'] if r['exit_code']==0}
labels=['build-native','stage1-extract','stage2-header']+['stage2-'+n for n in expected]+['stage2-Def_ZetaNine_HarmonicStability']
for label in labels:
 r=successful[label]
 assert sha(OUT/r['log'])==r['log_sha256'] and (OUT/(label+'-exit.txt')).read_text().strip()=='0'
for name,h in expected.items():
 assert sha(TASK/'formalization'/(name+'.lean'))==h==sha(PROJECT/'missions/zeta9/formalization'/(name+'.lean'))
for p in plan['required_parent_definitions']:
 assert sha(TASK/p['task_relative'])==p['sha256']==sha(PROJECT/p['root_relative'])
assert not plan['missing_parent_definitions'],'Wait the true Telescoper author freeze; no placeholders'
graph=rows(OUT/'decl_graph.jsonl');byname={g['name']:g for g in graph}
assert not any(g['kind']=='axiom' for g in graph)
source={n:(OUT/('oracle-input.lean' if n.endswith('PartialFractions') else n+'-oracle-input.lean')).read_bytes() for n in expected}
for name,h in expected.items():assert hashlib.sha256(source[name]).hexdigest()==h
facts={n:rows(OUT/('sketch_info.jsonl' if n.endswith('PartialFractions') else n+'-sketch_info.jsonl')) for n in expected}
reached=set();queue=[SEED]
while queue:
 name=queue.pop()
 if name in reached:continue
 reached.add(name);g=byname[name];queue.extend(g['typeDeps']+g['valueDeps'])
assert not any(NS+'.'+n in reached for n in ['actualAggregateEquiv','inverseMultiplier','prescribedL']), 'Equiv field closure must not depend on itself, its inverse, or prescribed output'
proofs=[byname[n] for n in reached if byname[n]['kind']=='theorem' and byname[n]['startLine']>0]
proofs.sort(key=lambda g:(list(expected).index(g['module'].split('.')[-1]),g['startLine']))
local_names={g['name']:'embedded_'+g['name'].replace('.','__') for g in proofs}
assert all(not g['isPrivate'] for g in proofs)
assert SEED in local_names
def declaration(g):
 module=g['module'].split('.')[-1]
 ds=[f for f in facts[module] if f['kind']=='decl' and f['declStart']['line']<=g['startLine']<=f['declEnd']['line']]
 assert len(ds)==1 and ds[0]['valStart'] and ds[0]['valKind']=='simple'
 return module,ds[0]
local_terms=[];transforms=[];available=set()
for g in proofs:
 module,f=declaration(g);data=source[module];a=f['declStart']['offset'];v=f['valStart']['offset'];b=f['declEnd']['offset']
 refs=[r for r in facts[module] if r['kind']=='ref' and a<=r['start']['offset'] and r['end']['offset']<=b]
 bind=[r for r in refs if r['const']==g['name'] and r['end']['offset']<=v]
 assert len(bind)==1
 start=bind[0]['end']['offset'];changes=[];calls=[]
 for r in refs:
  x,y=r['start']['offset'],r['end']['offset']
  if x<start:continue
  const=r['const']
  if const in local_names:
   assert const in available,'Local proof closure must respect true source dependency order'
   replacement=local_names[const];calls.append(const)
  else:
   if const in byname and byname[const]['kind']=='theorem' and byname[const]['startLine']>0:
    raise AssertionError('Project proof reference escaped true transitive closure: '+const)
   replacement=const
  changes.append((x-start,y-start,replacement.encode()))
 term='have '+local_names[g['name']]+edit(data[start:b],changes).decode()
 local_terms.append(term);available.add(g['name'])
 transforms.append({'original_declaration':g['name'],'local_binding':local_names[g['name']],'module':module,
  'parser_declaration_fact':f,'parser_binding_fact':bind[0],'parser_resolved_refs':refs,
  'local_proof_dependencies':sorted(set(calls)),'source_span_sha256':hashlib.sha256(data[a:b]).hexdigest(),
  'changed_only_decl_prefix_binding_and_resolved_references':True,'new_hypotheses':[]})
native_types=load(TASK/'verification/formalization-coefficient-map-kernel-2026-10-04/type-report.json')
assert len(native_types)==37
bijection_type=next(r['type'] for r in native_types if r['declaration']==SEED)
proof='((by\n'+''.join('    '+'\n    '.join(t.splitlines())+'\n' for t in local_terms)+'    exact '+local_names[SEED]+'\n  ) : '+bijection_type+')'
write(OUT/'closed-actual-aggregate-equiv-proof.lean.inc',proof+'\n')
g=byname[NS+'.actualAggregateEquiv'];module,field=declaration(g)
calls=[r for r in facts[module] if r['kind']=='ref' and r['const']==SEED and field['valStart']['offset']<=r['start']['offset'] and r['end']['offset']<=field['declEnd']['offset']]
assert len(calls)==1
call=calls[0]
defs=[byname[NS+'.'+n] for n in plan['new_actual_definitions']]
open_context=[]
for name in expected:
 first=min(g['startLine'] for g in graph if g['module'].endswith('.'+name) and g['startLine']>0)
 for f in facts[name]:
  if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.open' and f['span']['end']['line']<first:
   open_context.append({'module':name,'parser_fact':f,'text':source[name][f['span']['start']['offset']:f['span']['end']['offset']].decode()})
mathlib_imports=list(dict.fromkeys(line for name in expected for line in source[name].decode().splitlines() if line.startswith('import Mathlib.')))
assert 'import Mathlib.Tactic' in mathlib_imports
prefix='import Definitions.Def_ZetaNine_CoefficientMapTelescoper\nimport Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n'+'\n'.join(mathlib_imports)+'\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\nopen ZetaNine '+ ' '.join('ZetaNine.'+n for n in expected if n!='CoefficientMapKernelBridge')+'\n'+ '\n'.join(dict.fromkeys(o['text'] for o in open_context))+'\n\nnamespace '+NS+'\n\n'
pieces=[];deftransforms=[]
for dg in defs:
 module,f=declaration(dg);a,b=f['declStart']['offset'],f['declEnd']['offset'];chunk=source[module][a:b]
 replacements=[]
 if dg['name']==NS+'.actualAggregateEquiv':
  replacements=[(call['start']['offset']-a,call['end']['offset']-a,proof.encode())]
  chunk=edit(chunk,replacements)
 pieces.append(chunk.decode())
 deftransforms.append({'definition':dg['name'],'parser_fact':f,'constructor_proof_field_changed':bool(replacements),'new_hypotheses':[]})
definition=prefix+'\n\n'.join(pieces)+'\n\nend '+NS+'\n'
rel='Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean'
write(OUT/'staged'/rel,definition);write(PROJECT/rel,definition)
dump(OUT/'embedded-bijection-provenance.json',{'true_fresh_native_graph_sha256':sha(OUT/'decl_graph.jsonl'),
 'actual_equiv_definition':NS+'.actualAggregateEquiv','actual_closed_bijection_seed':SEED,
 'exact_original_bijection_type':bijection_type,'original_bijection_call_ref':call,'proof_closure_declarations':transforms,
 'definition_transforms':deftransforms,'true_source_open_contexts':open_context,'actual_native_Mathlib_imports':mathlib_imports,'definition_sha256':sha(OUT/'staged'/rel),
 'only_global_declarations_are_seven_original_Definitions':True,'original_data_functions_unchanged':True,
 'no_kernel_bijection_inverse_output_or_HasSum_hypotheses_added':True,'extra_hypotheses':[],
 'closure_has_no_Equiv_inverse_or_prescribed_output_cycle':True,
 'proof_field_is_closed_from_real_source_proofs':True,'Lean_execution_or_PASS_claimed_by_helper':False})
print(json.dumps({'new_Definitions':7,'true_local_proof_closure':len(local_terms),'Lean_executed_by_helper':False,'requires_actual_next_Definition_build_and_full_value_audits':True},ensure_ascii=False))
