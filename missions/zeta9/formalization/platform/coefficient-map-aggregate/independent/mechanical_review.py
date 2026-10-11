"""Independent graph/parser/span reconstruction and fixed root audit."""
from pathlib import Path
import json,hashlib,re,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=OUT.parents[3];ROOT=TASK.parents[1]
NS='ZetaNine.CoefficientMapAggregate';ALIAS=NS+'ValueComparison'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
MATHLIB=['Mathlib.Algebra.Polynomial.Eval.SMul','Mathlib.Algebra.Polynomial.BigOperators']
DEFS=['aggregate','coordinatePolynomial','polynomialCoordinates','aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']
TARGETS=['aggregate_add','polynomial_restore','aggregate_zero_all_rho']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def dump(p,d):p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
def code(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
def edit(b,es):
 edge=len(b)
 for a,z,v in sorted(set(es),reverse=True):
  assert 0<=a<=z<=edge;b=b[:a]+v+b[z:];edge=a
 return b
checks=[]
def check(n,ok,d=None):
 checks.append({'name':n,'pass':bool(ok),'detail':d});dump(OUT/'mechanical-development-checks.json',{'checks':checks,'complete':False});assert ok,n
controls=load(OUT/'frozen-controls.json')['controls'];manifest=load(BATCH/'source-manifest.json')
check('four_frozen_author_controls_exact',all(sha(BATCH/n)==h for n,h in controls.items()),controls)
check('all_291_frozen_source_manifest_members_exact',len(manifest['files'])==291 and all(sha(TASK/r['task_relative'])==r['sha256'] and (TASK/r['task_relative']).stat().st_size==r['bytes'] for r in manifest['files']))
sums=[s.split('  ',1) for s in (BATCH/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines() if s.strip()]
check('all_293_SHA256SUMS_members_exact',len(sums)==293 and all(sha(BATCH/n)==h for h,n in sums))
prep=load(OUT/'prepare-compile-receipt.json')
check('eight_actual_native_and_eight_pure_Def_sources_exact',len(prep['original_sources_sha256'])==8 and len(prep['existing_pure_Def_sources_sha256'])==8 and all(sha(TASK/('formalization/'+m+'.lean'))==h for m,h in prep['original_sources_sha256'].items()) and all(sha(ROOT/('Definitions/'+m+'.lean'))==h for m,h in prep['existing_pure_Def_sources_sha256'].items()))
graph=rows(OUT/'native-decl-graph.jsonl')
def normgraph(rs):return {r['name']:dict(r,typeDeps=sorted(r['typeDeps']),valueDeps=sorted(r['valueDeps'])) for r in rs}
check('fresh_actual_Stage1_all_graph_records_exact',normgraph(graph)==normgraph(rows(BATCH/'decl_graph.jsonl')),len(graph))
by={g['name']:g for g in graph};sources={};facts={}
for m in prep['original_sources_sha256']:
 sources[m]=(OUT/(m+'-native-snapshot.lean')).read_bytes();facts[m]=rows(OUT/(m+'-native-facts.jsonl'))
 suffix='oracle-input.lean' if m.endswith('PartialFractions') else m+'-oracle-input.lean'
 fact='sketch_info.jsonl' if m.endswith('PartialFractions') else m+'-sketch_info.jsonl'
 assert sources[m]==(BATCH/suffix).read_bytes()==(TASK/('formalization/'+m+'.lean')).read_bytes()
 assert facts[m]==rows(BATCH/fact)
hraw=(ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean').read_bytes()
hs=(OUT/'HarmonicStability-native-snapshot.lean').read_bytes();hf=rows(OUT/'HarmonicStability-native-facts.jsonl')
check('official_Harmonic_parser_exact_CRLF_to_LF_and_raw_source_fixed',hs==hraw.replace(b'\r\n',b'\n')==(BATCH/'HarmonicStability-oracle-input.lean').read_bytes() and hf==rows(BATCH/'HarmonicStability-sketch_info.jsonl') and sha(ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean')=='5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92')
check('nine_actual_Stage2_decl_command_ref_outputs_exact',True,{**{m:{k:sum(f['kind']==k for f in fs) for k in ['decl','ref','command']} for m,fs in facts.items()},'HarmonicStability':{k:sum(f['kind']==k for f in hf) for k in ['decl','ref','command']}})
header=rows(OUT/'native-header.jsonl');source=sources['CoefficientMapAggregate'];assert header==rows(BATCH/'header_info.jsonl') and len(header)==1
he=header[0]['end']['offset']
check('actual_Aggregate_header_three_imports_exact',source[:he].decode().strip().splitlines()==['import missions.zeta9.formalization.CoefficientMapSummation']+['import '+m for m in MATHLIB],header[0])
def declaration(n):
 g=by[n];ds=[f for f in facts[g['module'].split('.')[-1]] if f['kind']=='decl' and f['declStart']['line']<=g['startLine']<=f['declEnd']['line']]
 assert g['startLine']>0 and len(ds)==1 and ds[0]['valStart'];return ds[0]
def closure(seeds):
 seen=set();todo=list(seeds)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(by[n]['typeDeps']+by[n]['valueDeps'])
 return seen
core=[g for g in graph if g['module'].endswith('.CoefficientMapAggregate') and g['startLine']>0]
reached=closure([g['name'] for g in core]+[g['name'] for g in graph if g['isInstance']]);prov=load(BATCH/'integration-provenance.json')
bridge='';helpers=[];hfs=[];opens=[]
for m in list(sources)[:-1]:
 gs=sorted([by[n] for n in reached if by[n]['module'].endswith('.'+m) and by[n]['kind']=='theorem' and by[n]['startLine']>0],key=lambda g:g['startLine'])
 if not gs:continue
 first=min(g['startLine'] for g in graph if g['module'].endswith('.'+m) and g['startLine']>0)
 os_=[f for f in facts[m] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.open' and f['span']['end']['line']<first]
 bridge+='open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.'+m+'\n\n'
 for f in os_:
  bridge+=sources[m][f['span']['start']['offset']:f['span']['end']['offset']].decode()+'\n';opens.append({'module':m,'fact':f})
 if os_:bridge+='\n'
 for g in gs:
  f=declaration(g['name']);bridge+=sources[m][f['declStart']['offset']:f['declEnd']['offset']].decode()+'\n\n';helpers.append(g['name']);hfs.append({'module':m,'name':g['name'],'fact':f})
 bridge+='end ZetaNine.'+m+'\n\n'
check('all_26_native_declarations_and_53_actual_cross_helpers_closed',len(core)==26 and len(helpers)==53 and helpers==prov['inline_helper_names'] and hfs==prov['inline_helper_facts'] and sorted(reached)==prov['cross_module_core_closure'],{'six_Def':6,'twenty_original_proofs':20,'actual_helpers':helpers})
check('actual_cross_helper_open_contexts_and_complete_bridge_bytes_exact',opens==prov['bridge_open_context_facts'] and bridge.encode()==(BATCH/'actual-proof-bridge.lean.inc').read_bytes(),len(opens))
check('no_actual_axioms_or_new_external_proof_boundaries',not any(g['kind']=='axiom' for g in graph) and not prov['new_external_theorem_boundaries'])
dfacts=[declaration(NS+'.'+n) for n in DEFS];first=min(f['declStart']['offset'] for f in dfacts)
dos=[f for f in facts['CoefficientMapAggregate'] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.open' and f['span']['end']['offset']<first]
check('six_actual_Def_spans_and_three_open_contexts_exact',dfacts==prov['definition_facts'] and dos==prov['definition_open_context_facts'] and len(dos)==3)
fieldprov=load(BATCH/'embedded-field-provenance.json');typerows={r['declaration']:r for r in rows(OUT/'independent-embedded-types.log')};refs=[f for f in facts['CoefficientMapAggregate'] if f['kind']=='ref']
fieldroots={'aggregateLinearMap':['aggregate_add','aggregate_smul'],'coordinateLinearMap':['coordinatePolynomial_add','coordinatePolynomial_smul']}
fields=[];spans=[];allhelpers=set()
for short,d in zip(DEFS,dfacts):
 a,z=d['declStart']['offset'],d['declEnd']['offset'];es=[]
 for callee in fieldroots.get(short,[]):
  full=NS+'.'+callee;cs=closure([full]);gs=sorted([by[n] for n in cs if by[n]['module'].endswith('.CoefficientMapAggregate') and by[n]['kind']=='theorem' and by[n]['startLine']>0],key=lambda g:g['startLine'])
  names=[g['name'] for g in gs];allhelpers.update(names)
  occurrence=[r for r in refs if r['const']==full and a<=r['start']['offset']<r['end']['offset']<=z];assert len(occurrence)==1;r=occurrence[0]
  chunks=[];lfs=[]
  for g in gs:
   hd=declaration(g['name']);ha,hz,hv=hd['declStart']['offset'],hd['declEnd']['offset'],hd['valStart']['offset']
   bindings=[r for r in refs if r['const']==g['name'] and ha<=r['start']['offset']<hv];assert len(bindings)==1;binding=bindings[0];end=binding['start']['offset']
   assert hd['docstring'] is None and hd['privateTok'] is None and source[ha:end].decode().strip()=='theorem'
   snippet=edit(source[ha:hz],[(0,end-ha,b'have ')]).decode();chunks.append('\n'.join('    '+l for l in snippet.splitlines()))
   lfs.append({'name':g['name'],'declaration_fact':hd,'binding_fact':binding,'only_prefix_change':{'start':ha,'end':end,'replacement':'have '}})
  typ=typerows[full]['original_type'];term='((by\n'+'\n'.join(chunks)+'\n    exact '+callee+') :\n    ('+typ.replace('\n','\n    ')+'))'
  x,y=r['start']['offset'],r['end']['offset'];assert source[x:y].decode()==callee;es.append((x-a,y-a,term.encode()))
  fields.append({'definition':NS+'.'+short,'actual_proof_callee':full,'reference_fact':r,'helper_names':names,'helper_facts':lfs,'actual_original_type':typ,'actual_semantically_remapped_alias_type':typerows[full]['alias_type'],'replacement_proof_term':term,'data_fields_edited':False})
 spans.append(edit(source[a:z],es).decode())
definition='\n'.join('import '+m for m in ['Definitions.Def_ZetaNine_CoefficientMapSummation']+MATHLIB+['Mathlib.Tactic.FinCases','Mathlib.Tactic.Ring'])+'\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace '+NS+'\n\n'
definition+='\n'.join(source[f['span']['start']['offset']:f['span']['end']['offset']].decode() for f in dos)+'\n\n'+'\n\n'.join(spans)+'\n\nend '+NS+'\n'
check('four_actual_constructor_proof_refs_closed_using_ten_genuine_local_helpers',len(fields)==4 and len(allhelpers)==10 and fields==fieldprov['fields'] and sorted(allhelpers)==fieldprov['actual_original_helpers'] and not fieldprov['new_global_helper_theorems'])
check('full_six_Def_reconstruction_exact_data_spans_preserved',definition.encode()==(BATCH/'staged/Definitions/Def_ZetaNine_CoefficientMapAggregate.lean').read_bytes() and not re.search(r'\b(theorem|lemma|axiom|sorry|admit)\b',code(definition)),{'bytes':len(definition.encode()),'only_four_proof_references_edited':True})
diag=[f for f in facts['CoefficientMapAggregate'] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.printAxioms'];assert diag==prov['deleted_diagnostic_facts']
cuts=[(f['declStart']['offset'],f['declEnd']['offset'],b'') for f in dfacts]+[(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in diag]+[(0,he,b'')]
plan=load(BATCH/'target-plan.json');request=load(BATCH/'problems-request.json')
openstring='open ZetaNine '+NS+' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability\n'
preamble='import Definitions.Def_ZetaNine_CoefficientMapAggregate\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\n'+openstring
solhead='import Definitions.Def_ZetaNine_CoefficientMapAggregate\nimport Mathlib.Tactic\n'+'\n'.join('import '+m for m in MATHLIB)+'\n\n'+bridge
for i,n in enumerate(TARGETS):
 full=NS+'.'+n;d=declaration(full);a,v=d['declStart']['offset'],d['valStart']['offset'];rs=[r for r in refs if r['const']==full];bs=[r for r in rs if a<=r['start']['offset']<v];assert len(bs)==1
 x,y=bs[0]['start']['offset'],bs[0]['end']['offset'];assert source[x:y].decode()==n;sig=source[y:v].decode();renames=[]
 for r in rs:
  x_,y_=r['start']['offset'],r['end']['offset']
  if any(ca<=x_ and y_<=cz for ca,cz,_ in cuts):continue
  old=source[x_:y_].decode();assert old in [n,full];renames.append((x_,y_,('checked_'+n if old==n else NS+'.checked_'+n).encode()))
 sol=solhead+'\n'+edit(source,cuts+renames).decode()+'\n\n'+openstring+'\ntheorem solution'+sig+':= by\n  exact '+NS+'.checked_'+n+' '+plan['targets'][i]['wrapper_arguments']+'\n\n#print axioms solution\n'
 assert sol.encode()==(BATCH/'staged'/plan['targets'][i]['local_solution']).read_bytes()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code(sol)) and not re.search(r'(?m)^import (Theorems|Solutions|missions)\.',sol)
 fe=[(x-a,y-a,full.encode())]
 if d['docstring']:
  ds=d['docstring'];fe.append((ds['start']['offset']-a,ds['end']['offset']-a,b''))
 formal=edit(source[a:v],fe).decode().strip()+':= by sorry';ref=preamble+'\n'+formal+'\n'
 assert ref.encode()==(BATCH/'staged'/plan['targets'][i]['local_reference']).read_bytes()
 req=request['problems'][i];p=prov['targets'][full]
 assert req['formal_statement']==formal and req['preamble']==preamble and req['theorem_name']==full
 assert p['declaration_fact']==d and p['binding_fact']==bs[0] and p['target_refs']==rs and p['original_signature']==sig and not p['extra_hypotheses'] and p['rename_spans']==[[x,y] for x,y,_ in renames]
check('three_Sol_reference_and_request_source_splices_exact_no_extra_hypotheses',True,{'original_proofs':20,'cross_helpers':53,'wrapper_per_Sol':1})
check('three_Sol_import_only_pure_Def_and_Mathlib_no_proof_stubs',True,{'native_Theorems_Solutions_imports':[],'proof_holes':[]})
dreq=load(BATCH/'definitions-request.json');ad={'definition_name','definition_title','definition','natural_language_statement','source','tags','env','private'};ap={'theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source','tags'}
check('strict_offline_requests_exact_Def_bytes_and_env_public_flag',len(dreq)==1 and set(dreq[0])<=ad and dreq[0]['definition']==definition and dreq[0]['env']==REV and dreq[0]['private'] is False and set(request)=={'env','private','problems'} and request['env']==REV and request['private'] is False and len(request['problems'])==3 and all(set(p)<=ap and 0<len(p['theorem_title'])<=200 for p in request['problems']),{'API_called':False})
oldmath=TASK/'verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-review.json';math=load(oldmath)
check('fixed_native_independent_math_review_PASS_15_checks_107_bindings',sha(oldmath)=='d2f50aa65f5dec147e632642c78cd27aaa7d8b7ba554067b389d5cc669002ddc' and math['verdict']=='PASS' and len(math['checks'])==15 and len(math['stable_files'])==107 and all(sha(ROOT/r['root_relative'])==r['sha256'] and (ROOT/r['root_relative']).stat().st_size==r['bytes'] for r in math['stable_files']),{'prior_cache_bound_only_not_used':True})
rootHashes={'root-install-receipt.json':'52e35ecd77b4dc59a10265a185c7b6cfc12f0c0a60eb45bf05eb3b58407d6a6a','task-build.log':'6a4848cb811decb124dd050da86b13ccb4520e6fc7482c75750efbd165487d54','task-build-exit.txt':'13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354','task-check.log':'01a8be04d7e8271bbb089327220d24f487ddca4d688419fd1bcead7f081a02bb','task-check-exit.txt':'f1b2f662800122bed0ff255693df89c4487fbdcf453d3524a42d4ec20c3d9c04'}
check('five_parent_root_receipt_build_check_hashes_fixed',all(sha(BATCH/n)==h for n,h in rootHashes.items()),rootHashes)
copyplan=load(BATCH/'root-copy-plan.json');install=load(BATCH/'root-install-receipt.json');rootpaths=[]
for r in copyplan['files']:
 root=ROOT/r['root_relative_destination'];stage=TASK/r['staged_task_relative'];assert root.read_bytes()==stage.read_bytes() and sha(root)==r['sha256'] and root.stat().st_size==r['bytes'];rootpaths.append(root.relative_to(ROOT).as_posix())
for r in copyplan['required_existing_Definitions']:
 root=ROOT/r['root_relative'];assert root.read_bytes()==(TASK/r['task_relative']).read_bytes() and sha(root)==r['sha256'];rootpaths.append(root.relative_to(ROOT).as_posix())
check('seven_installed_and_eight_existing_root_Def_modules_same_bytes',len(copyplan['files'])==7 and len(copyplan['required_existing_Definitions'])==8 and install['frozen_author_audit_sha256']==controls['author-audit.json'] and install['frozen_root_copy_plan_sha256']==controls['root-copy-plan.json'] and install['root_bytes_match_frozen_stage'] and install['results']=={'check':1,'build':0},rootpaths)
build=(BATCH/'task-build.log').read_text(encoding='utf-8-sig');jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)\.',build).group(1))
check('parent_supported_scoped_build_actual_exit_zero_3803_jobs',jobs==3803 and (BATCH/'task-build-exit.txt').read_text().strip()=='0' and all('Sol_ZetaNine_CoefficientMapAggregate_'+n in build for n in TARGETS),jobs)
scope=load(TASK/'scope.json');check('three_current_task_Sol_build_entries_owned',all('Solutions/Sol_ZetaNine_CoefficientMapAggregate_'+n+'.lean' in scope['build'] for n in TARGETS),{'scope_not_modified_or_hashed':True})
issues=[s for s in (BATCH/'task-check.log').read_text(encoding='utf-8-sig').splitlines() if s.strip()]
check('workspace_check_only_two_old_Tao_unassigned_files',len(issues)==2 and all('Sol_TaoFivePrimes_' in s and 'Unassigned solution' in s for s in issues) and (BATCH/'task-check-exit.txt').read_text().strip()=='1',issues)
oldmanifests=[];oldcounts=[]
for batch in ['coefficient-map','coefficient-map-jet','coefficient-map-injectivity','coefficient-map-partial-fractions','coefficient-map-reflection','coefficient-map-finite-sum','coefficient-map-summation']:
 m=TASK/'formalization/platform'/batch/'SHA256SUMS.txt';ls=[l.split('  ',1) for l in m.read_text(encoding='utf-8-sig').splitlines() if l.strip()];assert all(sha(m.parent/n)==h for h,n in ls);oldcounts.append(len(ls));oldmanifests.append(m.relative_to(ROOT).as_posix())
check('all_1106_earlier_platform_freeze_members_unchanged',oldcounts==[96,111,134,174,172,220,199],oldcounts)
priors={'coefficient-map-reflection':'954a72aeed9af3188e62ed16030cdae9212da68d3c1d93eb6b75c2e854d50241','coefficient-map-finite-sum':'dea9dff29978c2576d9a3955bf7aa4a265a70edb60e4b6a9a7f9acd31815df50','coefficient-map-summation':'83d08d7146f472a2674f48158dd1154803ace82e2890506797d735b12041822e'}
for batch,h in priors.items():
 p=TASK/'formalization/platform'/batch/'independent/independent-integration-review.json';r=load(p);assert sha(p)==h and r['verdict']=='PASS';assert all(sha(ROOT/f['root_relative'])==f['sha256'] and (ROOT/f['root_relative']).stat().st_size==f['bytes'] for f in r['stable_files'])
check('all_three_earlier_independent_transplant_freezes_unchanged',True,priors)
dump(OUT/'mechanical-checks.json',{'complete':True,'checks':checks,'author_frozen_controls':controls,'root_evidence_sha256':rootHashes,'actual_cross_helpers':helpers,'root_paths':rootpaths,'old_frozen_manifests':oldmanifests,'prior_independent_reviews':priors})
print('Aggregate independent mechanical checks: '+str(len(checks))+' PASS')
