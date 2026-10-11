"""Author gate for actual Summation transplantation; independent review follows separately."""
from pathlib import Path
import hashlib,json,re,sys,subprocess
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[2]; ROOT=TASK.parents[1]; PROJECT=OUT/'project'
NS='ZetaNine.CoefficientMapSummation'; STD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(l) for l in p.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
def dump(p,d):p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def write(p,s):p.write_text(s,encoding='utf-8',newline='\n')
def edit(data,edits):
 edge=len(data)
 for a,b,v in sorted(set(edits),reverse=True):
  assert 0<=a<=b<=edge
  data=data[:a]+v+data[b:];edge=a
 return data
checks=[]
def check(name,okay,evidence=None):
 checks.append({'name':name,'pass':bool(okay),'evidence':evidence});assert okay,name
receipt=load(OUT/'compile-receipt.json'); plan=load(OUT/'target-plan.json'); prov=load(OUT/'integration-provenance.json')
check('seven_original_frozen_actual_sources_unchanged',len(receipt['source_sha256'])==7 and all(sha(TASK/'formalization'/f'{n}.lean')==h for n,h in receipt['source_sha256'].items()),receipt['source_sha256'])
mathfile=TASK/'verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-review.json'; math=load(mathfile)
check('actual_prior_native_independent_math_PASS_bound',sha(mathfile)=='fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa' and math['verdict']=='PASS' and len(math['checks'])==16 and all(sha(ROOT/r['root_relative'])==r['sha256'] for r in math['stable_files']),{'checks':16,'bindings':94,'new_independent_transplantation_review_claimed':False})
check('all_thirty_seven_author_execution_rows_actually_zero',receipt.get('complete') is True and len(receipt['rows'])==37 and all(r['exit_code']==0 and sha(OUT/r['log'])==r['log_sha256'] and (OUT/(r['label']+'-exit.txt')).read_text().strip()=='0' for r in receipt['rows']),{'observed_runs':len(receipt['rows']),'source_native_objects_borrowed':receipt.get('native_and_staged_objects_borrowed')})
mathlib=next(p for p in load(PROJECT/'lake-manifest.json')['packages'] if p['name']=='mathlib')
gitrev=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
(OUT/'mathlib-revision.log').write_bytes(gitrev.stdout+gitrev.stderr)
check('actual_pinned_environment','version 4.33.1' in (OUT/'toolchain.log').read_text(encoding='utf-8-sig') and mathlib['rev']=='0df444a360eaa60ab8c11dca51a86af692955474' and gitrev.returncode==0 and gitrev.stdout.decode().strip()==mathlib['rev'],{'toolchain':(PROJECT/'lean-toolchain').read_text().strip(),'mathlib_rev':mathlib['rev']})
native={r['label']:r for r in rows(OUT/'types_original.log')}
contexts=['types_definition']+[f'types_{i}_{kind}' for i in range(3) for kind in ['solution','reference']]
reports={label:{r['label']:r for r in rows(OUT/(label+'.log'))} for label in contexts}
defs=[r for r in native.values() if r['value'] is not None]; comparisons=[]
for d in defs:
 for label,rs in reports.items():
  got=rs[d['label']];comparisons.append({'declaration':d['declaration'],'context':label,
   'type_equal':got['type']==d['type'],'value_equal':got['value']==d['value'],'axioms':got['axioms']})
check('forty_three_actual_definition_types_values_in_seven_contexts_exact',len(defs)==43 and len(comparisons)==301 and all(r['type_equal'] and r['value_equal'] and set(r['axioms'])<=STD for r in comparisons),{'Base':9,'Jet':9,'Injectivity':7,'PF':5,'Reflection':4,'FiniteSum':4,'Summation':3,'HarmonicStability':2,'comparisons':301})
targets=[]
for i,t in enumerate(plan['targets']):
 full=t['theorem_name']; o=native[full]; s=reports[f'types_{i}_solution'][full]; r=reports[f'types_{i}_reference'][full]
 targets.append({'theorem':full,'actual_original_type':o['type'],'original_solution_reference_type_equal':o['type']==s['type']==r['type'],
  'original_axioms':o['axioms'],'solution_axioms':s['axioms'],'reference_axioms':r['axioms']})
check('three_endpoint_original_solution_reference_types_exact',len(targets)==3 and all(t['original_solution_reference_type_equal'] for t in targets),targets)
check('all_three_complete_proofs_exact_standard_three_axioms',all(set(t['solution_axioms'])==STD==set(t['original_axioms']) for t in targets),sorted(STD))
per=22+len(prov['inline_helper_names']); helpers=[rows(OUT/f'helpers_{i}.log') for i in range(3)]
check('all_twenty_one_source_proofs_parent_closure_wrapper_standard_three',all(len(rs)==per and all(set(r['axioms'])<=STD for r in rs) for rs in helpers),{'records_per_solution':per,'total':3*per,'parent_helpers':prov['inline_helper_names']})
check('no_external_Theorems_Solutions_or_mission_proof_import',not prov['new_external_theorem_boundaries'] and all(not any(l.startswith(('import Theorems.','import Solutions.','import missions.')) for l in (OUT/'staged'/t['local_solution']).read_text(encoding='utf-8').splitlines()) for t in plan['targets']))
check('only_statement_references_have_sorryAx',all('sorryAx' in t['reference_axioms'] for t in targets))
check('actual_source_core_and_new_three_Definitions',prov['source_declarations']==24 and prov['source_defs']==3 and prov['source_proofs']==21 and len(prov['definition_facts'])==3)
req=load(OUT/'problems-request.json'); dreq=load(OUT/'definitions-request.json')[0]
check('documented_API_request_fields_only_and_no_API_calls',set(req)=={'env','private','problems'} and all(t['formal_statement'].endswith(':= by sorry') and len(t['theorem_title'])<=200 and set(t)<={'theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source','tags'} for t in req['problems']) and set(dreq)<={'definition_name','definition_title','definition','natural_language_statement','source','tags','env','private'})
check('definition_request_is_exact_staged_source',dreq['definition'].encode()==(OUT/'staged'/plan['local_definition']).read_bytes())
check('strong_even_integer_domains_and_HasSum_prose_faithful','No Even n premise' in req['problems'][0]['natural_language_statement'] and 'no HasSum' in req['problems'][1]['natural_language_statement'] and 'n\\ge2' in req['problems'][2]['natural_language_statement'] and 'W\\in\\mathbb Z[X]' in req['problems'][2]['natural_language_statement'])
check('all_seven_exact_genuine_parent_Definitions_bound',len(plan['existing_definitions'])==7 and all(sha(TASK/d['task_relative'])==d['sha256']==sha(PROJECT/d['root_relative']) for d in plan['existing_definitions']),plan['existing_definitions'])
check('pure_Harmonic_definition_is_existing_actual_byte_copy',any(d['root_relative']=='Definitions/Def_ZetaNine_HarmonicStability.lean' and d['sha256']=='5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92' and sha(ROOT/d['root_relative'])==d['sha256'] for d in plan['existing_definitions']))
fs_batch=TASK/'formalization/platform/coefficient-map-finite-sum'; fs_audit=load(fs_batch/'author-audit.json')
fs_bindings=[]
for line in (fs_batch/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
 h,path=line.split('  ',1);fs_bindings.append({'task_relative':(fs_batch/path).relative_to(TASK).as_posix(),'sha256':h});assert sha(fs_batch/path)==h
fs_parent={'author_audit_sha256':sha(fs_batch/'author-audit.json'),'source_manifest_sha256':sha(fs_batch/'source-manifest.json'),'SHA256SUMS_sha256':sha(fs_batch/'SHA256SUMS.txt'),'staged_definition_sha256':sha(fs_batch/'staged/Definitions/Def_ZetaNine_CoefficientMapFiniteSum.lean'),'frozen_bindings':fs_bindings,'independent_platform_review_claimed':False}
check('actual_fixed_FiniteSum_parent_author_freeze_bound',fs_audit['verdict']=='PASS' and len(fs_audit['checks'])==29 and all(c['pass'] for c in fs_audit['checks']) and len(fs_bindings)==220 and fs_parent['author_audit_sha256']=='b3b91da77d5c2523fdd9b091351ac302540206d4a882f24e8c0d6476e504eaf0' and fs_parent['source_manifest_sha256']=='2bfe608fb62026d1e8f51d066d309d2e094dfea4746b2b047d51c3c453166255' and fs_parent['SHA256SUMS_sha256']=='74e33ca45597a15e52a1b37f03db8f729398371a7103c8ffad4a3440612e169a' and fs_parent['staged_definition_sha256']=='d1b41541e0fc7e359f96d51e4190206deb4656468896d871b95d449cddcd7fc5',{'author_checks':29,'bindings':len(fs_bindings),'independent_platform_review_claimed':False})
old_count=0
for name in ['coefficient-map','coefficient-map-jet','coefficient-map-injectivity','coefficient-map-partial-fractions','coefficient-map-reflection']:
 old=TASK/'formalization/platform'/name
 for line in (old/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
  h,path=line.split('  ',1);assert sha(old/path)==h;old_count+=1
check('previous_five_author_batches_frozen_bytes_unchanged',old_count>515,{'frozen_members_recomputed':old_count,'old_batch_writes':False})
graph=rows(OUT/'decl_graph.jsonl'); check('real_Stage1_graph_no_axioms_or_proof_boundary',len(graph)==prov['graph_records'] and not any(g['kind']=='axiom' for g in graph))
sources={n:(TASK/'formalization'/f'{n}.lean').read_bytes() for n in receipt['source_sha256']};bridge=''
for module in ['CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity','CoefficientMapPartialFractions','CoefficientMapReflection','CoefficientMapFiniteSum']:
 hs=[f for f in prov['inline_helper_facts'] if f['module']==module]
 if not hs:continue
 bridge+='open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.'+module+'\n\n'
 opens=[f['fact'] for f in prov['bridge_open_context_facts'] if f['module']==module]
 for f in opens:bridge+=sources[module][f['span']['start']['offset']:f['span']['end']['offset']].decode()+'\n'
 if opens:bridge+='\n'
 for h in hs:
  f=h['fact'];bridge+=sources[module][f['declStart']['offset']:f['declEnd']['offset']].decode()+'\n\n'
 bridge+='end ZetaNine.'+module+'\n\n'
check('actual_parent_proof_spans_parser_open_context_exact',bridge.encode()==(OUT/'actual-proof-bridge.lean.inc').read_bytes() and hashlib.sha256(bridge.encode()).hexdigest()==prov['bridge_sha256'])
source=sources['CoefficientMapSummation']; facts=rows(OUT/'CoefficientMapSummation-sketch_info.jsonl');refs=[f for f in facts if f['kind']=='ref']
check('actual_Summation_parser_snapshot_counts_exact',{k:sum(f['kind']==k for f in facts) for k in ['decl','ref','command']}==prov['source_fact_counts'] and sum(f['kind']=='decl' for f in facts)==24,prov['source_fact_counts'])
cuts=[(f['declStart']['offset'],f['declEnd']['offset'],b'') for f in prov['definition_facts']]+[(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in prov['deleted_diagnostic_facts']]+[(0,prov['header']['end']['offset'],b'')]
mathimports=['Mathlib.NumberTheory.LSeries.RiemannZeta','Mathlib.Analysis.PSeries','Mathlib.Analysis.Normed.Group.InfiniteSum','Mathlib.Analysis.Normed.Module.FiniteDimension']
openline='open ZetaNine '+NS+' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\n'
splices=[]
for t in plan['targets']:
 full=t['theorem_name'];name=full.split('.')[-1];changes=[]
 for r in refs:
  if r['const']!=full:continue
  a,b=r['start']['offset'],r['end']['offset']
  if any(x<=a and b<=y for x,y,_ in cuts):continue
  old=source[a:b].decode();assert old in [name,full]
  changes.append((a,b,('checked_'+name if old==name else NS+'.checked_'+name).encode()))
 prefix='import Definitions.Def_ZetaNine_CoefficientMapSummation\nimport Mathlib.Tactic\n'+'\n'.join('import '+m for m in mathimports)+'\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n'+bridge
 result=prefix+'\n'+edit(source,cuts+changes).decode()+'\n\n'+openline+'\ntheorem solution'+prov['targets'][full]['original_signature']+':= by\n  exact '+NS+'.checked_'+name+' '+t['wrapper_arguments']+'\n\n#print axioms solution\n'
 splices.append(result.encode()==(OUT/'staged'/t['local_solution']).read_bytes())
check('complete_original_twenty_one_proofs_and_three_parser_splices_exact',all(splices) and len(prov['deleted_diagnostic_facts'])==12,{'proofs_retained_per_Sol':21,'extra_hypotheses':[]})
definition='import Definitions.Def_ZetaNine_CoefficientMapReflection\nimport Definitions.Def_ZetaNine_CoefficientMapFiniteSum\n'+'\n'.join('import '+m for m in mathimports)+'\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace '+NS+'\n\n'
definition+='\n'.join(source[f['span']['start']['offset']:f['span']['end']['offset']].decode() for f in prov['definition_open_context_facts'])+'\n\n'
definition+='\n\n'.join(source[f['declStart']['offset']:f['declEnd']['offset']].decode() for f in prov['definition_facts'])+'\n\nend '+NS+'\n'
check('new_Def_exact_three_actual_definition_spans_and_context',definition.encode()==(OUT/'staged'/plan['local_definition']).read_bytes())
boundary=load(OUT/'stage-boundary-report.json'); native_boundary=load(TASK/'verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-boundary-types.json')
normalize=lambda s:s.replace('.checked_actualSeries_hasSum_exactL','.actualSeries_hasSum_exactL')
native_by={r['declaration']:r for r in native_boundary}; boundary_comparisons=[]
for r in boundary['records']:
 d=normalize(r['declaration']);o=native_by[d]
 boundary_comparisons.append({'declaration':d,'native_type_exact':normalize(r['type'])==o['type'],'native_definition_value_exact':r['definitionValue']==o['definitionValue'],'axioms':r['axioms']})
check('actual_staged_HasSum_and_all_original_analytic_boundary_records_exact',boundary['exit_code']==0 and (OUT/'stage-boundary-audit-exit.txt').read_text().strip()=='0' and len(boundary_comparisons)==56 and boundary['all_standard_axioms'] and all(r['native_type_exact'] and r['native_definition_value_exact'] for r in boundary_comparisons),{'records':56,'closed_boundaries':'n0X4 harmonic no HasSum / totalized tsum0; n0X3 actual zeta3; odd absolute summability; original Even n>=2 integer quartic'})
check('native_analytic_scope_and_open_limits_match_math_report',math['actual_series_absolute_summability_closed'] is True and math['actual_HasSum_exactL_closed'] is True and math['original_integer_quartic_actual_infinite_L_closed'] is True and math['irrationality_closed'] is False)
copyfiles=[]
for rel in [plan['local_definition']]+[t[k] for t in plan['targets'] for k in ['local_solution','local_reference']]:
 p=OUT/'staged'/rel;dest=ROOT/rel
 copyfiles.append({'staged_task_relative':p.relative_to(TASK).as_posix(),'root_relative_destination':rel,'bytes':p.stat().st_size,'sha256':sha(p),'destination_exists_at_author_freeze':dest.exists()})
 if dest.exists():assert sha(dest)==sha(p)
copyplan={'source_sha256':receipt['source_sha256']['CoefficientMapSummation'],'sources_sha256':receipt['source_sha256'],
 'required_existing_Definitions':plan['existing_definitions'],'author_scope':'new task-local offline staged/project only; parent installs','overwrite_allowed':False,
 'files':copyfiles,'scope_build_entrypoints_for_parent':[t['local_solution'].removesuffix('.lean').replace('/','.') for t in plan['targets']]}
dump(OUT/'root-copy-plan.json',copyplan)
dump(OUT/'decl-plan.json',{'selected_public_endpoints':[t['theorem_name'] for t in plan['targets']],'actual_cross_module_graph_records':prov['graph_records'],
 'retained_Summation_declarations':24,'moved_genuine_Definitions':3,'inline_original_Summation_proofs':21,
 'actual_cross_module_core_closure':prov['cross_module_core_closure'],'inline_parent_helpers':prov['inline_helper_names'],
 'generated_records':prov['generated_records'],'new_external_theorem_boundaries':[]})
limitations=['Absolute summability holds for all natural n under the actual strong degree bound, without Even n. Exact odd-zeta HasSum keeps Even n. The original integer-quartic endpoint keeps even n>=2 and degree<=4.',
 'No extra rho, summability, zeta-limit or abstract rational-function premise is introduced. True simple-pole cancellation groups potentially divergent terms before actual summability is proved.',
 'n0X4 is strict proper but not strong: actual harmonic series, no HasSum to any real, yet totalized tsum0. n0X3 is actual convergent zeta3. These original exact boundaries are recompiled against the complete staged proof.',
 'This batch closes actual p9,q1,m=n,d0 infinite sum identities and original integer-quartic specialization only. Rational F inverse was separately proved in KernelBridge; inverse height/integrality, small nonzero integer forms, general parameters, J and irrationality are not claims of this batch.',
 'Reference stubs carry sorryAx intentionally and are not proof evidence. Complete solutions and all inlined helpers have only standard3 axioms. Author gate is separate from independent transplantation, root build and external acceptance.']
write(OUT/'README.md','# Actual Summation offline author batch\n\nThree exact native endpoints are staged: actualSeries_norm_summable, actualSeries_hasSum_exactL and original_integer_quartic_exact_infinite_L. Seven actual native sources plus the genuine unchanged pure HarmonicStability definition are compiled in a fresh task-local project. Real Stage1 graph, eight parser/ref oracles and native header parser supply all source spans. Three actual definitions move into a lightweight Definition importing the exact frozen Reflection and FiniteSum parents. All21 original Summation proofs and their actual parent proof closure are retained in every Solution; no external theorem/proof boundary is introduced.\n\n'+ '\n\n'.join(limitations)+'\n\nNo root/scope/API/credential writes occurred. The seven-file copy-plan is for the parent; independent review and publication remain separate.\n')
stable=[p for p in OUT.iterdir() if p.is_file() and p.name not in ['author-audit.json','SHA256SUMS.txt','source-manifest.json']]
stable+=list((OUT/'staged').rglob('*.lean'))+list((OUT/'dependencies').rglob('*.lean'))
stable+=list(PROJECT.glob('*.lean'))+[PROJECT/'lake-manifest.json',PROJECT/'lean-toolchain']
stable+=[PROJECT/'missions/zeta9/formalization'/f'{n}.lean' for n in receipt['source_sha256']]
stable+=list((PROJECT/'Definitions').glob('*.lean'))+list((PROJECT/'Solutions').glob('*.lean'))+list((PROJECT/'Theorems').glob('*.lean'))
stable=list(dict.fromkeys(stable))
manifest={'schema_version':1,'source_sha256':receipt['source_sha256'],'files':[{'task_relative':p.relative_to(TASK).as_posix(),'batch_relative':p.relative_to(OUT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(stable)],'existing_definition_dependencies':plan['existing_definitions'],'prior_native_independent_review_sha256':sha(mathfile),'fixed_FiniteSum_parent_author_freeze':fs_parent,'old_batches_modified':False}
dump(OUT/'source-manifest.json',manifest)
audit={'schema_version':1,'review_role':'author offline integration gate; separate independent review required','verdict':'PASS','source_sha256':receipt['source_sha256']['CoefficientMapSummation'],'sources_sha256':receipt['source_sha256'],
 'mathlib_rev':'0df444a360eaa60ab8c11dca51a86af692955474','lean_toolchain':'leanprover/lean4:v4.33.1','checks':checks,'targets':targets,
 'definition_comparisons':comparisons,'all_proof_records':helpers,'boundary_comparisons':boundary_comparisons,'actual_cross_module_helpers':prov['inline_helper_names'],
 'limitations':limitations,'fixed_FiniteSum_parent_author_freeze':fs_parent,'platform_published':False,'platform_accepted':False,'root_installed_by_author':False,'independent_transplantation_review_claimed':False,
 'root_scope_API_credential_writes':False,'stable_files':manifest['files']}
dump(OUT/'author-audit.json',audit)
freeze=stable+[OUT/'source-manifest.json',OUT/'author-audit.json']
write(OUT/'SHA256SUMS.txt',''.join(sha(p)+'  '+p.relative_to(OUT).as_posix()+'\n' for p in sorted(freeze)))
for line in (OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,rel=line.split('  ',1);assert sha(OUT/rel)==h
print(json.dumps({'author_verdict':'PASS','checks':len(checks),'actual_graph_records':prov['graph_records'],'definition_comparisons':301,'helpers_per_Sol':per,
 'frozen_files':len(freeze),'author_sha256':sha(OUT/'author-audit.json'),'copyplan_sha256':sha(OUT/'root-copy-plan.json'),'manifest_sha256':sha(OUT/'source-manifest.json'),'SHA256SUMS_sha256':sha(OUT/'SHA256SUMS.txt')},ensure_ascii=False))
