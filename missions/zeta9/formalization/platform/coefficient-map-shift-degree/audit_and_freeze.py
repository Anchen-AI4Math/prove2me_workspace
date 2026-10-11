"""Author transplantation gate, distinct from later independent review."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/'project'
NS='ZetaNine.CoefficientMapShiftDegree';SOURCE_SHA='96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953'
STD={'propext','Classical.choice','Quot.sound'};REV='0df444a360eaa60ab8c11dca51a86af692955474'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
rows=lambda p:[json.loads(l) for l in p.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
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
 checks.append({'name':name,'pass':bool(okay),'evidence':evidence})
 if not okay:
  n=len(list(OUT.glob('retained-author-gate-failure-*.json')))+1
  dump(OUT/f'retained-author-gate-failure-{n:02d}.json',{'failed_check':name,'checks_observed':checks,'excluded_from_success_evidence':True})
  raise AssertionError(name)
receipt=load(OUT/'compile-receipt.json');plan=load(OUT/'target-plan.json');prov=load(OUT/'integration-provenance.json')
sourcefile=TASK/'formalization/CoefficientMapShiftDegree.lean';source=sourcefile.read_bytes()
check('one_actual_native_source_fixed_and_fresh_byte_copy',receipt['source_sha256']=={'CoefficientMapShiftDegree':SOURCE_SHA} and sha(sourcefile)==SOURCE_SHA==sha(PROJECT/'missions/zeta9/formalization/CoefficientMapShiftDegree.lean'))
mathfile=TASK/'verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-review.json';math=load(mathfile)
check('prior_independent_mathematics_PASS_16_checks_54_bindings',sha(mathfile)=='d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df' and math['verdict']=='PASS' and len(math['checks'])==16 and all(c['pass'] for c in math['checks']) and len(math['stable_files'])==54 and all(sha(ROOT/r['root_relative'])==r['sha256'] for r in math['stable_files']),{'new_independent_platform_review_claimed':False})
author=TASK/'verification/formalization-coefficient-map-shift-degree-2026-10-04';author_bindings=[]
for line in (author/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
 h,rel=line.split('  ',1);author_bindings.append({'root_relative':rel,'sha256':h});assert sha(ROOT/rel)==h
check('native_author_27_manifest_members_and_28_SHA_entries_fixed',sha(author/'compile-receipt.json')=='93595416db563dd9cd8ffb5030455eed1edfe678b392ec64b1bd4930fdb7f853' and sha(author/'source-manifest.json')=='8918a99aed1d1ab8d75079feaac4996f70f0e96cf66cec2dff713a0454210044' and sha(author/'SHA256SUMS.txt')=='88f22efde6ad2e4552c878e55ca09f5247f9ab4ffa567c7d5edc91036808f4c5' and len(author_bindings)==28,{'SHA_entries':28,'retained_native_failures_used_as_success_evidence':False})
check('all_twenty_three_main_executions_actually_zero',receipt.get('complete') is True and len(receipt['rows'])==23 and all(r['exit_code']==0 and sha(OUT/r['log'])==r['log_sha256'] and (OUT/(r['label']+'-exit.txt')).read_text().strip()=='0' for r in receipt['rows']),{'observed_runs':len(receipt['rows'])})
check('native_and_staged_proof_objects_not_borrowed',receipt.get('native_and_staged_objects_borrowed') is False and len(plan['existing_definitions'])==0 and prov['inline_helper_names']==[] and prov['new_external_theorem_boundaries']==[])
mathlib=next(p for p in load(PROJECT/'lake-manifest.json')['packages'] if p['name']=='mathlib')
gitrev=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
(OUT/'mathlib-revision.log').write_bytes(gitrev.stdout+gitrev.stderr)
check('actual_pinned_Lean_and_Mathlib','version 4.33.1' in (OUT/'toolchain.log').read_text(encoding='utf-8-sig') and (PROJECT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1' and mathlib['rev']==REV and gitrev.returncode==0 and gitrev.stdout.decode().strip()==REV)
native={r['label']:r for r in rows(OUT/'types_original.log')};defs=[r for r in native.values() if r['value'] is not None]
contexts=['types_definition']+[f'types_{i}_{k}' for i in range(3) for k in ['solution','reference']]
reports={c:{r['label']:r for r in rows(OUT/(c+'.log'))} for c in contexts};comparisons=[]
for d in defs:
 for c,rs in reports.items():
  r=rs[d['label']];comparisons.append({'declaration':d['declaration'],'context':c,'type_equal':r['type']==d['type'],'value_equal':r['value']==d['value'],'axioms':r['axioms']})
check('three_actual_Definitions_type_and_value_exact_in_seven_contexts',len(defs)==3 and len(comparisons)==21 and all(c['type_equal'] and c['value_equal'] and set(c['axioms'])<=STD for c in comparisons),{'definitions':['shiftA','shiftB','shiftDifference'],'comparisons':21})
targets=[]
for i,t in enumerate(plan['targets']):
 n=t['theorem_name'];o=native[n];s=reports[f'types_{i}_solution'][n];r=reports[f'types_{i}_reference'][n]
 targets.append({'theorem':n,'actual_original_type':o['type'],'original_solution_reference_type_equal':o['type']==s['type']==r['type'],'original_axioms':o['axioms'],'solution_axioms':s['axioms'],'reference_axioms':r['axioms']})
check('three_original_Solution_reference_types_exact_without_extra_hypotheses',len(targets)==3 and all(t['original_solution_reference_type_equal'] for t in targets),targets)
check('three_complete_Solution_targets_standard_three_axioms',all(set(t['solution_axioms'])==STD==set(t['original_axioms']) for t in targets),sorted(STD))
helpers=[rows(OUT/f'helpers_{i}.log') for i in range(3)]
check('all_twelve_actual_source_proofs_plus_wrapper_closed_in_each_Solution',all(len(rs)==13 and all(set(r['axioms'])<=STD for r in rs) for rs in helpers),{'records':39,'parent_proof_boundaries':[]})
check('no_external_Theorems_Solutions_or_mission_proof_import',all(not any(l.startswith(('import Theorems.','import Solutions.','import missions.')) for l in (OUT/'staged'/t['local_solution']).read_text(encoding='utf-8').splitlines()) for t in plan['targets']))
check('reference_stubs_only_are_not_complete_proof_evidence',all('sorryAx' in t['reference_axioms'] for t in targets))
graph=rows(OUT/'decl_graph.jsonl');facts=rows(OUT/'CoefficientMapShiftDegree-sketch_info.jsonl');refs=[f for f in facts if f['kind']=='ref']
check('actual_Stage1_graph_and_Stage2_parser_no_project_axioms',len(graph)==prov['graph_records'] and not any(g['kind']=='axiom' for g in graph) and all(g['module']=='missions.zeta9.formalization.CoefficientMapShiftDegree' for g in graph) and prov['source_declarations']==15 and prov['source_defs']==3 and prov['source_proofs']==12 and sum(f['kind']=='decl' for f in facts)==15,{'graph_records':len(graph),'facts':prov['source_fact_counts']})
check('real_header_parser_exact_native_imports',prov['header']['start']['offset']==0 and source[:prov['header']['end']['offset']].decode().strip().splitlines()==['import Mathlib.Algebra.Polynomial.Taylor','import Mathlib.Algebra.Polynomial.Reverse','import Mathlib.Tactic'])
check('no_parent_proof_bridge_or_assumption',prov['inline_helper_facts']==[] and prov['bridge_open_context_facts']==[] and (OUT/'actual-proof-bridge.lean.inc').read_bytes()==b'')
definition='import Mathlib.Algebra.Polynomial.Taylor\nimport Mathlib.Algebra.Polynomial.Reverse\n\nset_option autoImplicit false\nnoncomputable section\nnamespace '+NS+'\n\n'
definition+='\n'.join(source[f['span']['start']['offset']:f['span']['end']['offset']].decode() for f in prov['definition_open_context_facts'])+'\n\n'
definition+='\n\n'.join(source[f['declStart']['offset']:f['declEnd']['offset']].decode() for f in prov['definition_facts'])+'\n\nend '+NS+'\n'
check('lightweight_Definition_is_three_exact_actual_parser_spans',len(prov['definition_facts'])==3 and definition.encode()==(OUT/'staged'/plan['local_definition']).read_bytes())
cuts=[(f['declStart']['offset'],f['declEnd']['offset'],b'') for f in prov['definition_facts']]+[(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in prov['deleted_diagnostic_facts']]+[(0,prov['header']['end']['offset'],b'')]
splices=[]
for t in plan['targets']:
 full=t['theorem_name'];name=full.split('.')[-1];changes=[]
 for r in refs:
  if r['const']!=full:continue
  a,b=r['start']['offset'],r['end']['offset']
  if any(x<=a and b<=y for x,y,_ in cuts):continue
  old=source[a:b].decode();assert old in [name,full]
  changes.append((a,b,('checked_'+name if old==name else NS+'.checked_'+name).encode()))
 prefix='import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\nimport Mathlib.Algebra.Polynomial.Taylor\nimport Mathlib.Algebra.Polynomial.Reverse\nimport Mathlib.Tactic\n\n'
 result=prefix+'\n'+edit(source,cuts+changes).decode()+'\n\nopen ZetaNine '+NS+'\n\ntheorem solution'+prov['targets'][full]['original_signature']+':= by\n  exact '+NS+'.checked_'+name+' '+t['wrapper_arguments']+'\n\n#print axioms solution\n'
 splices.append(result.encode()==(OUT/'staged'/t['local_solution']).read_bytes())
check('all_twelve_actual_proof_bodies_and_three_parser_splices_exact',all(splices) and len(prov['deleted_diagnostic_facts'])==5,{'proofs_per_Solution':12,'extra_hypotheses':[]})
req=load(OUT/'problems-request.json');dreq=load(OUT/'definitions-request.json')[0]
check('documented_API_fields_and_exact_Definition_request',set(req)=={'env','private','problems'} and all(set(p)<={'theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source','tags'} and p['formal_statement'].endswith(':= by sorry') and len(p['theorem_title'])<=200 for p in req['problems']) and set(dreq)<={'definition_name','definition_title','definition','natural_language_statement','source','tags','env','private'} and dreq['definition'].encode()==definition.encode())
check('original_domains_faithful_in_human_statements','only $H\\ne0$' in req['problems'][0]['natural_language_statement'] and '$n\\ge1$' in req['problems'][1]['natural_language_statement'] and '7n-3' in req['problems'][1]['natural_language_statement'] and 'le8' in req['problems'][2]['natural_language_statement'] and 'No nonzero-input premise' in req['problems'][2]['natural_language_statement'])
boundary=load(OUT/'stage-boundary-report.json');boundary_comparisons=[]
normalize=lambda s:s.replace('.checked_actual_shift_difference_small_degree_implies_zero','.actual_shift_difference_small_degree_implies_zero')
old_reports=[load(author/'type-report.json')['records_actual'],load(TASK/'verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-boundary-types.json')]
for run,oldrs in zip(boundary['runs'],old_reports):
 oldby={r['declaration']:r for r in oldrs};assert len(run['records'])==len(oldrs)
 check(run['label']+'_actual_zero_and_standard_axioms',run['exit_code']==0 and sha(OUT/(run['label']+'.log'))==run['log_sha256'] and (OUT/(run['label']+'-exit.txt')).read_text().strip()=='0' and run['all_standard_axioms'],{'records':len(run['records'])})
 for r in run['records']:
  d=normalize(r['declaration']);o=oldby[d]
  boundary_comparisons.append({'declaration':d,'type_equal':normalize(r['type'])==o['type'],'value_equal':r['definitionValue']==o['definitionValue'],'axioms':r['axioms']})
check('all_22_author_and_17_independent_records_exact_against_staged_operator',boundary['all_zero'] and len(boundary_comparisons)==39 and all(r['type_equal'] and r['value_equal'] for r in boundary_comparisons),{'n1X5':'coeff15=0, outside degree domain, eval1=-1152','other_boundaries':'zero/natural degree zero, nonmonic/negative constants, n0, exact degree and actual leading coefficient in the valid domain'})
check('mathematical_scope_excludes_R_kernel_inverse_and_irrationality',math['R_operator_relationship_proved_or_assumed'] is False and math['aggregate_kernel_or_inverse_proved_in_source'] is False and math['zeta_or_irrationality_conclusions'] is False and math['new_external_proof_assumptions']==[])
prior=TASK/'formalization/platform/coefficient-map-summation';prior_count=0
for line in (prior/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,rel=line.split('  ',1);assert sha(prior/rel)==h;prior_count+=1
check('previous_Summation_author_199_frozen_members_unchanged',prior_count==199,{'previous_batch_writes':False})
copyfiles=[]
for rel in [plan['local_definition']]+[t[k] for t in plan['targets'] for k in ['local_solution','local_reference']]:
 p=OUT/'staged'/rel;dest=ROOT/rel
 copyfiles.append({'staged_task_relative':p.relative_to(TASK).as_posix(),'root_relative_destination':rel,'bytes':p.stat().st_size,'sha256':sha(p),'destination_exists_at_author_freeze':dest.exists()})
 if dest.exists():assert sha(dest)==sha(p)
dump(OUT/'root-copy-plan.json',{'source_sha256':SOURCE_SHA,'sources_sha256':receipt['source_sha256'],'required_existing_Definitions':[],
 'author_scope':'new task-local batch only; parent installs','overwrite_allowed':False,'files':copyfiles,'scope_build_entrypoints_for_parent':[t['local_solution'].removesuffix('.lean').replace('/','.') for t in plan['targets']]})
dump(OUT/'decl-plan.json',{'actual_native_declarations':15,'actual_graph_records':len(graph),'selected_public_endpoints':[t['theorem_name'] for t in plan['targets']],'pure_Definitions':3,'original_proofs_per_Solution':12,'new_external_theorem_boundaries':[]})
limitations=['The coefficient formula applies to every natural n and nonzero rational H. The degree obstruction keeps n>=1, degH<=7n-3; the low-degree endpoint also keeps deg(actual operator)<=8.',
 'All three actual polynomial definitions and all twelve original proofs are retained exactly. No parity, monicity, rational telescoper relationship, determinant/rank, kernel or inverse premise is added.',
 'The actual n=1,H=X^5 resonance has coefficient15=0 but eval1=-1152 and lies outside the degree bound. Zero, degree-zero, n=0 and nonmonic cases retain the original exact author and independent statements.',
 'This batch is the polynomial coefficient and degree obstruction only. The genuine rational-function relationship and original F inverse were proved separately; denominator heights, small nonzero integer forms and zeta irrationality are not claims here.',
 'Reference stubs intentionally carry sorryAx. Complete Solutions and all source proof records use only standard3 axioms. Author PASS is distinct from independent transplantation, scoped root build and external acceptance.']
write(OUT/'README.md','# Actual ShiftDegree offline author batch\n\nThree actual polynomial endpoints, three exact genuine Definitions and all twelve original proofs are staged using the real declaration graph, parser/ref oracle and header parser. One native source is freshly compiled; no coefficient-parent Definitions or mission proof objects are borrowed.\n\n'+'\n\n'.join(limitations)+'\n\nThe seven-file root-copy-plan is for the parent. No root/scope/API/credential writes occurred.\n')
stable=[p for p in OUT.iterdir() if p.is_file() and p.name not in ['author-audit.json','source-manifest.json','SHA256SUMS.txt']]
stable+=list((OUT/'staged').rglob('*.lean'))+list(PROJECT.glob('*.lean'))+[PROJECT/'lake-manifest.json',PROJECT/'lean-toolchain',PROJECT/'missions/zeta9/formalization/CoefficientMapShiftDegree.lean']
stable+=list((PROJECT/'Definitions').glob('*.lean'))+list((PROJECT/'Solutions').glob('*.lean'))+list((PROJECT/'Theorems').glob('*.lean'))
stable=list(dict.fromkeys(stable))
manifest={'schema_version':1,'source_sha256':SOURCE_SHA,'files':[{'task_relative':p.relative_to(TASK).as_posix(),'batch_relative':p.relative_to(OUT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(stable)],'prior_native_independent_review_sha256':sha(mathfile),'native_author_frozen_bindings':author_bindings,'old_batches_modified':False}
dump(OUT/'source-manifest.json',manifest)
dump(OUT/'author-audit.json',{'schema_version':1,'review_role':'author offline integration gate; separate independent transplantation review required','verdict':'PASS','source_sha256':SOURCE_SHA,'sources_sha256':receipt['source_sha256'],'lean_toolchain':'leanprover/lean4:v4.33.1','mathlib_rev':REV,'checks':checks,'targets':targets,'definition_comparisons':comparisons,'all_proof_records':helpers,'boundary_comparisons':boundary_comparisons,'native_author_frozen_bindings':author_bindings,'limitations':limitations,'platform_published':False,'platform_accepted':False,'root_installed_by_author':False,'root_scope_API_credential_writes':False,'independent_transplantation_review_claimed':False,'stable_files':manifest['files']})
freeze=stable+[OUT/'source-manifest.json',OUT/'author-audit.json']
write(OUT/'SHA256SUMS.txt',''.join(sha(p)+'  '+p.relative_to(OUT).as_posix()+'\n' for p in sorted(freeze)))
for line in (OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,rel=line.split('  ',1);assert sha(OUT/rel)==h
print(json.dumps({'author_verdict':'PASS','checks':len(checks),'definition_comparisons':21,'proof_records':39,'boundary_records':39,'frozen_files':len(freeze),'author_sha256':sha(OUT/'author-audit.json'),'copyplan_sha256':sha(OUT/'root-copy-plan.json'),'manifest_sha256':sha(OUT/'source-manifest.json'),'SHA256SUMS_sha256':sha(OUT/'SHA256SUMS.txt')},ensure_ascii=False))
