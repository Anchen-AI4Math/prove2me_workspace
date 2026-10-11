from run_step import *
import re
verify();enroll=load(OUT/'preparation-enrollment.json');graph=rows(OUT/'decl_graph.jsonl');by={g['name']:g for g in graph}
NS='ZetaNine.CoefficientMapTelescoper';DEFS=['prefixSum','cumulativeCoefficient','telescoper','telescoperNumerator','rootNode','rootPolynomial']
TARGETS=enroll['targets'];ARGS=['n hn W hstrong hzero t hregular','n hn1 W t hregular','n hn1 hn W hstrong hzero']
checks=[]
def check(name,ok,detail=None):
 checks.append({'name':name,'pass':bool(ok),'evidence':detail});dump(OUT/'mechanical-development-checks.json',{'complete':False,'checks':checks});assert ok,name
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
def norm(rs):return {r['name']:dict(r,typeDeps=sorted(r['typeDeps']),valueDeps=sorted(r['valueDeps'])) for r in rs}
check('independent_actual_cross_module_graph_exact',norm(graph)==norm(rows(BATCH/'decl_graph.jsonl')),len(graph))
sources={};facts={}
for m in enroll['original_source_hashes']:
 sources[m]=(OUT/(m+'-s.lean')).read_bytes();facts[m]=rows(OUT/(m+'-f.jsonl'))
 oracle='oracle-input.lean' if m.endswith('PartialFractions') else m+'-oracle-input.lean';ff='sketch_info.jsonl' if m.endswith('PartialFractions') else m+'-sketch_info.jsonl'
 assert sources[m]==(TASK/'formalization'/(m+'.lean')).read_bytes().replace(b'\r\n',b'\n')==(BATCH/oracle).read_bytes()
 assert facts[m]==rows(BATCH/ff)
hs=(OUT/'HarmonicStability-s.lean').read_bytes();hf=rows(OUT/'HarmonicStability-f.jsonl')
check('nine_actual_source_Stage2_refs_decls_commands_exact',True,{m:{k:sum(f['kind']==k for f in fs) for k in ['decl','ref','command']} for m,fs in facts.items()})
check('pureHarmonic_raw_source_versus_official_CRLF_normalized_snapshot_exact',hs==(PROJECT/'Definitions/Def_ZetaNine_HarmonicStability.lean').read_bytes().replace(b'\r\n',b'\n')==(BATCH/'Def_ZetaNine_HarmonicStability-oracle-input.lean').read_bytes() and hf==rows(BATCH/'Def_ZetaNine_HarmonicStability-sketch_info.jsonl'))
source=sources['CoefficientMapTelescoper'];header=rows(OUT/'header.jsonl');check('actual_header_exact',header==rows(BATCH/'header_info.jsonl') and len(header)==1,header)
he=header[0]['end']['offset'];assert source[:he].decode().strip().splitlines()==['import missions.zeta9.formalization.CoefficientMapAggregate']
def decl(n):
 g=by[n];ds=[f for f in facts[g['module'].split('.')[-1]] if f['kind']=='decl' and f['declStart']['line']<=g['startLine']<=f['declEnd']['line']]
 assert g['startLine']>0 and len(ds)==1 and ds[0]['valStart'] is not None;return ds[0]
def closure(seed):
 seen=set();todo=list(seed)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(by[n]['typeDeps']+by[n]['valueDeps'])
 return seen
core=[g for g in graph if g['module'].endswith('.CoefficientMapTelescoper') and g['startLine']>0]
control_modules=[r['module'] for r in enroll['fixed_native_controls']]
control_roots=[g['name'] for g in graph if g['module'] in control_modules and g['startLine']>0]
reached=closure([g['name'] for g in core]+control_roots+[g['name'] for g in graph if g['isInstance']]);prov=load(BATCH/'integration-provenance.json')
bridge='';helpers=[];hfs=[];opens=[]
for m in list(sources)[:-1]:
 hs_=sorted([by[n] for n in reached if by[n]['module'].endswith('.'+m) and by[n]['kind']=='theorem' and by[n]['startLine']>0],key=lambda g:g['startLine'])
 if not hs_:continue
 first=min(g['startLine'] for g in graph if g['module'].endswith('.'+m) and g['startLine']>0)
 os_=[f for f in facts[m] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.open' and f['span']['end']['line']<first]
 bridge+='open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.'+m+'\n\n'
 for f in os_:bridge+=sources[m][f['span']['start']['offset']:f['span']['end']['offset']].decode()+'\n';opens.append({'module':m,'fact':f})
 if os_:bridge+='\n'
 for g in hs_:
  f=decl(g['name']);bridge+=sources[m][f['declStart']['offset']:f['declEnd']['offset']].decode()+'\n\n';helpers.append(g['name']);hfs.append({'module':m,'name':g['name'],'fact':f})
 bridge+='end ZetaNine.'+m+'\n\n'
check('actual31source_sixDefs25proof_and20_original_control_roots',len(core)==31 and sum(g['kind']=='def' for g in core)==6 and len(control_roots)==20 and set(control_roots)==set(prov['native_closed_control_roots']),control_roots)
check('actual81_crosshelpers_whole_proof_bodies_and_open_contexts_exact',len(helpers)==81 and helpers==prov['inline_helper_names'] and hfs==prov['inline_helper_facts'] and opens==prov['bridge_open_context_facts'] and bridge.encode()==(BATCH/'actual-proof-bridge.lean.inc').read_bytes() and sorted(reached)==prov['cross_module_core_closure'],{'helpers':helpers,'open_contexts':len(opens)})
df=[decl(NS+'.'+n) for n in DEFS];first=min(f['declStart']['offset'] for f in df)
dos=[f for f in facts['CoefficientMapTelescoper'] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.open' and f['span']['end']['offset']<first]
definition='import Definitions.Def_ZetaNine_CoefficientMapAggregate\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\n\nnamespace '+NS+'\n\n'
definition+='\n'.join(source[f['span']['start']['offset']:f['span']['end']['offset']].decode() for f in dos)+'\n\n'+'\n\n'.join(source[f['declStart']['offset']:f['declEnd']['offset']].decode() for f in df)+'\n\nend '+NS+'\n'
check('six_new_ordinaryDefs_and_parser_open_contexts_exact',df==prov['definition_facts'] and dos==prov['definition_open_context_facts'] and definition.encode()==(BATCH/'staged/Definitions/Def_ZetaNine_CoefficientMapTelescoper.lean').read_bytes(),{'bytes':len(definition.encode()),'opens':len(dos)})
refs=[f for f in facts['CoefficientMapTelescoper'] if f['kind']=='ref'];diag=[f for f in facts['CoefficientMapTelescoper'] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.printAxioms']
assert diag==prov['deleted_diagnostic_facts']
cuts=[(f['declStart']['offset'],f['declEnd']['offset'],b'') for f in df]+[(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in diag]+[(0,he,b'')]
preamble='import Definitions.Def_ZetaNine_CoefficientMapTelescoper\n\nset_option autoImplicit false\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\nopen ZetaNine '+NS+' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate\n'
solhead='import Definitions.Def_ZetaNine_CoefficientMapTelescoper\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n'+bridge
openstring='open ZetaNine '+NS+' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.HarmonicStability\n'
plan=load(BATCH/'target-plan.json');request=load(BATCH/'problems-request.json')
for i,n in enumerate(TARGETS):
 full=NS+'.'+n;d=decl(full);a,v=d['declStart']['offset'],d['valStart']['offset'];rs=[f for f in refs if f['const']==full];bindings=[f for f in rs if a<=f['start']['offset']<v];assert len(bindings)==1
 x,y=bindings[0]['start']['offset'],bindings[0]['end']['offset'];assert source[x:y].decode()==n;sig=source[y:v].decode();renames=[]
 for r in rs:
  u,w=r['start']['offset'],r['end']['offset']
  if any(ca<=u and w<=cz for ca,cz,_ in cuts):continue
  old=source[u:w].decode();assert old in [n,full];renames.append((u,w,('checked_'+n if old==n else NS+'.checked_'+n).encode()))
 sol=solhead+'\n'+edit(source,cuts+renames).decode()+'\n\n'+openstring+'\ntheorem solution'+sig+':= by\n  exact '+NS+'.checked_'+n+' '+ARGS[i]+'\n\n#print axioms solution\n'
 t=plan['targets'][i];assert t['wrapper_arguments']==ARGS[i] and sol.encode()==(BATCH/'staged'/t['local_solution']).read_bytes()
 fe=[(x-a,y-a,full.encode())]
 if d['docstring']:
  ds=d['docstring'];fe.append((ds['start']['offset']-a,ds['end']['offset']-a,b''))
 formal=edit(source[a:v],fe).decode().strip()+':= by sorry';reference=preamble+'\n'+formal+'\n'
 assert reference.encode()==(BATCH/'staged'/t['local_reference']).read_bytes()
 req=request['problems'][i];pt=prov['targets'][full]
 assert req['formal_statement']==formal and req['preamble']==preamble and pt['binding_fact']==bindings[0] and pt['declaration_fact']==d and pt['target_refs']==rs and pt['rename_spans']==[[u,w] for u,w,_ in renames] and not pt['extra_hypotheses']
 clean=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',sol,flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',clean) and not re.search(r'(?m)^import (Theorems|Solutions|missions)\.',sol)
check('three_whole_Sols_references_and_original_wrapper_signatures_exact',True,{'source_proofs':25,'actual_helpers':81,'wrapper_per_Sol':1,'no_extra_hypotheses':True})
check('complete_Sols_use_only_pure_Def_and_Mathlib_no_native_stub_or_holes',True)
dr=load(BATCH/'definitions-request.json');check('strict_Def_request_and_public_frozen_environment_exact',len(dr)==1 and dr[0]['definition']==definition and dr[0]['env']==request['env'] and dr[0]['private'] is False and request['private'] is False)
check('no_actual_axioms_or_new_external_proof_boundaries',not any(g['kind']=='axiom' for g in graph) and not prov['new_external_theorem_boundaries'])
all_defs=[g['name'] for g in graph if g['kind']=='def' and g['startLine']>0];check('actual55_sourceDefs_for_seven_contexts',len(all_defs)==55,all_defs)
for i,r in enumerate(enroll['fixed_native_controls']):
 actual=(PROJECT/(r['module']+'.lean')).read_bytes();snap=(OUT/(f'control{i}-s.lean')).read_bytes();assert snap==actual.replace(b'\r\n',b'\n')
 fs=[f for f in rows(OUT/(f'control{i}-f.jsonl')) if f.get('kind') in ['decl','ref','command']];source_decls=[f for f in fs if f['kind']=='decl'];assert len(source_decls)==(4 if i==0 else 16)
check('two_actual_control_parsers_show4plus16_source_declarations_not35plus54',True,{'original_type_records':35,'independent_type_records':54})
dump(OUT/'mechanical-checks.json',{'complete':True,'checks':checks,'actual_cross_helpers':helpers,'actual_defs':all_defs,'core_proof_names':[g['name'] for g in core if g['kind']=='theorem'],'targets':TARGETS,
 'root_and_frozen_gate':load(OUT/'frozen-handoff.json'),'newDef_sha256':sha(BATCH/'staged/Definitions/Def_ZetaNine_CoefficientMapTelescoper.lean')})
print('Tel independent actual source/span reconstruction:',len(checks),'checks PASS',flush=True)
