"""Independent serial staged replay; all proof objects come from our fresh cache."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=OUT.parents[3];ROOT=TASK.parents[1]
PROJECT=OUT/'project';N=OUT/'cache/n';P=OUT/'cache/p';NS='ZetaNine.CoefficientMapAggregate'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(l) for l in p.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
def dump(p,d):p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s.encode() if isinstance(s,str) else s)
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):
  assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
controls=load(OUT/'frozen-controls.json')['controls']
def fixed():
 assert all(sha(BATCH/n)==h for n,h in controls.items())
 for r in load(BATCH/'source-manifest.json')['files']:
  f=TASK/r['task_relative'];assert sha(f)==r['sha256'] and f.stat().st_size==r['bytes']
fixed()
assert load(OUT/'native-alias-audit-receipt.json')['complete']
prior=load(OUT/'replay-compile-receipt.json')
assert not prior['complete'] and len(prior['rows'])==28 and all(r['exit_code']==0 for r in prior['rows'])
rs=list(prior['rows'])
for r in rs:
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 for field in ['log','exit_file','wrapper','output','stdout_copy']:
  if r.get(field):assert sha(OUT/r[field])==r['stdout_sha256' if field=='stdout_copy' else field+'_sha256']
 assert r['lean_working_directory']==str(PROJECT)

def run(label,source,cache,output=None,args=None,copy=None):
 old=[r for r in rs if r['label']==label]
 if old:
  assert len(old)==1 and old[0]['source_sha256']==sha(source) and old[0]['cache']==cache.relative_to(OUT).as_posix() and old[0]['exit_code']==0
  if output:assert old[0]['output']==output.relative_to(OUT).as_posix() and sha(output)==old[0]['output_sha256']
  if copy:assert old[0]['stdout_copy']==copy.name and sha(copy)==old[0]['stdout_sha256']
  print(label+': hash-guarded same independent project/cache actual exit0 reused',flush=True);return
 wrapper=OUT/(label+'.ps1')
 cmd=f'$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{PROJECT.as_posix()}"\nSet-Location -LiteralPath "{PROJECT.as_posix()}"\n& lean '
 if output:output.parent.mkdir(parents=True,exist_ok=True);cmd+='-o "'+output.as_posix()+'" '
 if args is not None:cmd+='--run '
 cmd+='"'+source.as_posix()+'"'+''.join(' "'+s+'"' for s in args or [])+'\nexit $LASTEXITCODE\n';write(wrapper,cmd)
 invocation=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(invocation,cwd=ROOT,capture_output=True);log=OUT/(label+'.log');write(log,p.stdout+p.stderr)
 ex=OUT/(label+'-exit.txt');write(ex,str(p.returncode)+'\n')
 if copy:write(copy,p.stdout)
 rs.append({'label':label,'command':invocation,'exit_code':p.returncode,'lake_env_working_directory':str(ROOT),'lean_working_directory':str(PROJECT),
  'source_root_relative':source.relative_to(ROOT).as_posix(),'source_sha256':sha(source),'log':log.name,'log_sha256':sha(log),
  'exit_file':ex.name,'exit_file_sha256':sha(ex),'wrapper':wrapper.name,'wrapper_sha256':sha(wrapper),'cache':cache.relative_to(OUT).as_posix(),
  'output':output.relative_to(OUT).as_posix() if output else None,'output_sha256':sha(output) if output and output.exists() else None,
  'stdout_copy':copy.name if copy else None,'stdout_sha256':sha(copy) if copy else None})
 dump(OUT/'replay-compile-receipt.json',{'rows':rs,'complete':False,'native_and_staged_objects_borrowed':False})
 print(label+': exit '+str(p.returncode),flush=True);fixed()
 if p.returncode:print(log.read_text(encoding='utf-8-sig'),flush=True)
 assert p.returncode==0,'Failure retained separately'
plan=load(BATCH/'root-copy-plan.json')
for r in plan['files']:
 source=TASK/r['staged_task_relative'];dest=PROJECT/r['root_relative_destination'];assert sha(source)==r['sha256'];write(dest,source.read_bytes())
 run('staged-'+dest.stem,dest,P,P/(r['root_relative_destination'].removesuffix('.lean')+'.olean'))
for name in ['types_original.lean','types_definition.lean']+[f'types_{i}_{k}.lean' for i in range(3) for k in ['solution','reference']]+[f'helpers_{i}.lean' for i in range(3)]:
 source=OUT/name;write(source,(BATCH/name).read_bytes());run('replay-'+source.stem,source,N if name=='types_original.lean' else P)
contexts=['Definitions.Def_ZetaNine_CoefficientMapAggregate']+[r['root_relative_destination'].removesuffix('.lean').replace('/','.') for r in plan['files'] if not r['root_relative_destination'].startswith('Definitions/')]
maps=['aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']
for i,context in enumerate(contexts):
 code='import '+context+'\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\nrun_meta do\n  for name in ['+', '.join('`'+NS+'.'+n for n in maps)+'] do\n'
 code+='''    let ci ← getConstInfo name
    let .defnInfo d := ci | throwError "Expected actual staged definition"
    let typ ← ppExpr d.type
    let val ← ppExpr d.value
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("full_expression_repr",Json.str (reprStr d.value)),("raw_value",Json.str val.pretty),
      ("pp_proofs",toJson true),("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 source=OUT/(f'full-context-{i}.lean');write(source,code);run(f'full-context-{i}',source,P)
graph=rows(OUT/'native-decl-graph.jsonl');by={g['name']:g for g in graph};prep=load(OUT/'prepare-compile-receipt.json')
core=[g for g in graph if g['module'].endswith('.CoefficientMapAggregate') and g['startLine']>0]
def closure(seeds):
 seen=set();todo=list(seeds)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if n in by:todo.extend(by[n]['typeDeps']+by[n]['valueDeps'])
 return seen
reached=closure([g['name'] for g in core]+[g['name'] for g in graph if g['isInstance']])
proofs=sorted(n for n in reached if n in by and by[n]['kind']=='theorem' and by[n]['startLine']>0)
assert len(core)==26 and len(proofs)==73
code='import missions.zeta9.formalization.CoefficientMapAggregate\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nrun_meta do\n  for name in ['+', '.join('`'+n for n in proofs)+'] do\n'
code+='''    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
source=OUT/'independent-native-required-proofs.lean';write(source,code);run(source.stem,source,N)
bp=load(BATCH/'stage-boundary-provenance.json');ff={};fb={}
parser=(BATCH/'extract_CoefficientMapAggregate_sketch.lean').read_text(encoding='utf-8-sig')
for label,fixture in bp['fixtures'].items():
 src=TASK/fixture['original_task_relative'];assert sha(src)==fixture['original_sha256']
 copy=PROJECT/(f'boundary-{label}-input.lean');write(copy,src.read_bytes())
 code=parser.replace('../CoefficientMapAggregate-oracle-input.lean',(OUT/(f'boundary-{label}-native-snapshot.lean')).as_posix());assert code!=parser
 extract=OUT/(f'extract-boundary-{label}.lean');write(extract,code)
 run('stage2-boundary-'+label,extract,N,args=[copy.as_posix()],copy=OUT/(f'boundary-{label}-native-facts.jsonl'))
 ff[label]=rows(OUT/(f'boundary-{label}-native-facts.jsonl'));fb[label]=(OUT/(f'boundary-{label}-native-snapshot.lean')).read_bytes()
 assert fb[label]==src.read_bytes().replace(b'\r\n',b'\n')
source_order=load(BATCH/'integration-provenance.json')['sources_sha256']
assert source_order==prep['original_sources_sha256']
sources={m:(OUT/(m+'-native-snapshot.lean')).read_bytes() for m in source_order}
facts={m:rows(OUT/(m+'-native-facts.jsonl')) for m in sources}
def declaration(g):
 fs=facts[g['module'].split('.')[-1]];ds=[f for f in fs if f['kind']=='decl' and f['declStart']['line']<=g['startLine']<=f['declEnd']['line']]
 assert len(ds)==1;return ds[0]
provided=set(proofs)
seeds={f['const'] for fs in ff.values() for f in fs if f['kind']=='ref' and f['const'] in by}
extra=[by[n] for n in closure(seeds) if n in by and by[n]['kind']=='theorem' and by[n]['startLine']>0 and n not in provided]
extra.sort(key=lambda g:(list(sources).index(g['module'].split('.')[-1]),g['startLine']))
assert len(extra)==33
bridge='';ef=[];opens=[]
for module in sources:
 hs=[g for g in extra if g['module'].endswith('.'+module)]
 if not hs:continue
 bridge+='open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.'+module+'\n\n'
 first=min(g['startLine'] for g in graph if g['module'].endswith('.'+module) and g['startLine']>0)
 os_=[f for f in facts[module] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.open' and f['span']['end']['line']<first]
 for f in os_:
  bridge+=sources[module][f['span']['start']['offset']:f['span']['end']['offset']].decode()+'\n';opens.append({'module':module,'fact':f})
 if os_:bridge+='\n'
 for g in hs:
  f=declaration(g);bridge+=sources[module][f['declStart']['offset']:f['declEnd']['offset']].decode()+'\n\n';ef.append({'module':module,'name':g['name'],'fact':f})
 bridge+='end ZetaNine.'+module+'\n\n'
assert bridge.encode()==(BATCH/'boundary-only-proof-bridge.lean.inc').read_bytes()
assert ef==bp['additional_parent_proofs_only_in_audit'] and opens==bp['additional_parent_open_context']
write(OUT/'boundary-only-proof-bridge.lean.inc',bridge)
for label in ff:
 assert ff[label]==rows(BATCH/(f'boundary-{label}-sketch_info.jsonl'))
 assert [f for f in ff[label] if f['kind']=='decl']==bp['fixtures'][label]['actual_declaration_facts']
source=OUT/'stage-boundary-audit.lean';write(source,(BATCH/source.name).read_bytes());run('replay-stage-boundary-audit',source,P)
# Native boundary oracle: the same official declaration spans, without platform renames.
stage=(BATCH/'stage-boundary-audit.lean').read_text(encoding='utf-8')
pre=stage[stage.index('open Lean Meta Polynomial Finset'):stage.index('theorem checked_five_actual_coordinates')]
native='import missions.zeta9.formalization.CoefficientMapAggregate\nimport Lean\nimport Mathlib.Tactic\n\n'+pre
for label in ff:
 for f in ff[label]:
  if f['kind']=='decl':native+=fb[label][f['declStart']['offset']:f['declEnd']['offset']].decode()+'\n\n'
tail=stage[stage.index('run_meta do'):]
tail=tail[:tail.index('  for name in [',tail.index('  for name in [')+1)]
tail=tail.replace(NS+'.checked_aggregate_zero_all_rho',NS+'.aggregate_zero_all_rho')
source=OUT/'independent-native-boundary-audit.lean';write(source,native+tail);run(source.stem,source,N)
dump(OUT/'boundary-reconstruction.json',{'actual_parser_fixtures':bp['fixtures'],'extra_helper_facts':ef,'extra_open_facts':opens,
 'bridge_sha256':sha(OUT/'boundary-only-proof-bridge.lean.inc'),'native_records':54,'audit_only_extra_helpers':33,'all_actual_parser_equal':True})
dump(OUT/'replay-compile-receipt.json',{'rows':rs,'complete':True,'native_and_staged_objects_borrowed':False,
 'native_actual_proof_names':proofs,'full_value_contexts':contexts,'direct_native_kernel_calls':6,'context_propagation_calls':21})
assert len(rs)==30 and all(r['exit_code']==0 for r in rs)
