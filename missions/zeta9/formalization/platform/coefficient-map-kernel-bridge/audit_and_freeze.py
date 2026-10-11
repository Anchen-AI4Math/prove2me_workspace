"""Author gate for the actual KernelBridge; independent transplantation review follows."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/'p';BUILD=TASK/'.rt/k1/b'
NS='ZetaNine.CoefficientMapKernelBridge';ANS='ZetaNine.CoefficientMapAggregate'
SOURCE_SHA='1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb';REV='0df444a360eaa60ab8c11dca51a86af692955474'
STD={'propext','Classical.choice','Quot.sound'};MAPS={ANS+'.'+n for n in ['aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
rows=lambda p:[json.loads(l) for l in p.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
def lake_control_rows(p,module):
 records=[]
 for line in p.read_text(encoding='utf-8-sig').splitlines():
  if line.startswith('{'):records.append(json.loads(line))
  elif line.startswith('info: '+module+'.lean:') and ': {' in line:
   records.append(json.loads(line[line.index('{'):]))
 return records
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
check('eleven_actual_native_sources_fixed_and_fresh_copied',len(receipt['source_sha256'])==11 and receipt['source_sha256']['CoefficientMapKernelBridge']==SOURCE_SHA and all(sha(TASK/'formalization'/f'{n}.lean')==h==sha(PROJECT/'missions/zeta9/formalization'/f'{n}.lean') for n,h in receipt['source_sha256'].items()),receipt['source_sha256'])
mathfile=TASK/'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json';math=load(mathfile)
check('previous_native_math_review_22_checks_296_bindings_fixed',sha(mathfile)=='7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1' and math['verdict']=='PASS' and len(math['checks'])==22 and all(c['pass'] for c in math['checks']) and len(math['stable_files'])==296 and all(sha(ROOT/r['root_relative'])==r['sha256'] for r in math['stable_files']),{'previous_math_reviewer_is_current_platform_author':True,'independent_transplantation_PASS_claimed':False})
author=TASK/'verification/formalization-coefficient-map-kernel-2026-10-04';author_bindings=[]
for line in (author/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
 h,rel=line.split('  ',1);assert sha(TASK/rel)==h;author_bindings.append({'task_relative':rel,'sha256':h})
check('native_author_46_frozen_members_and_receipt_fixed',sha(author/'compile-receipt.json')=='07ed208d0eef9d16632320ee1710c4c62919cc948f5fe770eba5dcc315656aa7' and sha(author/'SHA256SUMS.txt')=='5e6481b76038db693c73f3bc13f582019ff5ce06c3f5361dadf88d218f69a498' and len(author_bindings)==46,{'native_source_proofs':23,'native_records':37})
check('all_forty_seven_main_author_executions_actually_zero',receipt.get('complete') is True and len(receipt['rows'])==47 and all(r['exit_code']==0 and sha(OUT/r['log'])==r['log_sha256'] and (OUT/(r['label']+'-exit.txt')).read_text().strip()=='0' for r in receipt['rows']),{'main_execution_rows':len(receipt['rows'])})
check('no_native_or_staged_mission_proof_objects_borrowed',receipt.get('native_and_staged_objects_borrowed') is False and prov['new_external_theorem_boundaries']==[])
retained_attempts=[p for d in sorted(OUT.glob('retained-attempt-*')) if d.is_dir() for p in sorted(d.rglob('*')) if p.is_file()]
diagnostic=load(OUT/'retained-attempt-01-offline-diagnostic-probes/receipt.json')
check('failed_offline_diagnostic_probes_retained_and_excluded_from_Lean_evidence',diagnostic['Lean_executions']==0 and diagnostic['excluded_from_success_evidence'] and all(r['exit_code']==1 for r in diagnostic['attempts']),{'retained_files':len(retained_attempts),'actual_failed_Lean_executions':0})
pathguard=load(OUT/'output-path-preflight.json');selectedpath=load(OUT/'lean-path-selected.json')['LEAN_PATH']
selecteddirs=[Path(s).resolve() for s in selectedpath.split(';') if s]
check('short_fresh_cache_and_actual_selected_Lean_PATH_without_root_proof_shadow',pathguard['all_absolute_output_paths_with_64_chars_below_260'] and pathguard['cache_absent_or_empty_before_first_Lean'] and pathguard['planned_total_execution_count']==57 and receipt['fresh_build_task_relative']==BUILD.relative_to(TASK).as_posix() and BUILD.resolve()/'lib/lean' in selecteddirs and not any(p==(ROOT/'.lake/build/lib/lean').resolve() or p==(OUT/'project/.lake/build/lib/lean').resolve() for p in selecteddirs),{'actual_selected_LEAN_PATH':selectedpath,'output_suffix_budget':64,'longest_guarded_output':pathguard['longest_guarded_output_path']})
check('fresh_main_compiler_cache_objects_hash_bound',receipt['fresh_main_cache_bindings'] and all(sha(TASK/r['task_relative'])==r['sha256'] for r in receipt['fresh_main_cache_bindings']),{'hash_bound_main_artifacts':len(receipt['fresh_main_cache_bindings'])})
timing=load(OUT/'definition-compile-time.json')
check('actual_Definition_compile_timing_and_constructor_closure_reason_bound',timing['actual_build_exit_code']==0 and timing['additional_Lean_runs']==0 and timing['source_sha256']==sha(PROJECT/'Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean') and timing['object_sha256']==sha(TASK/timing['object_task_relative']) and 0<timing['seconds_start_to_object_written']<=timing['seconds_start_to_Lake_exit_log_capture'] and timing['exact_Wait_Process_exit_timestamp_available'] is False,timing)
mathlib=next(p for p in load(PROJECT/'lake-manifest.json')['packages'] if p['name']=='mathlib')
g=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True);(OUT/'mathlib-revision.log').write_bytes(g.stdout+g.stderr)
check('actual_fixed_Lean_Mathlib_environment','version 4.33.1' in (OUT/'toolchain.log').read_text(encoding='utf-8-sig') and (PROJECT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1' and mathlib['rev']==REV and g.returncode==0 and g.stdout.decode().strip()==REV)
native={r['label']:r for r in rows(OUT/'types_original.log')};defs=[r for r in native.values() if r['value'] is not None]
contexts=['types_definition']+[f'types_{i}_{k}' for i in range(3) for k in ['solution','reference']]
reports={c:{r['label']:r for r in rows(OUT/(c+'.log'))} for c in contexts}
eqprov=load(OUT/'aggregate-data-equivalence-provenance.json');eqreport=load(OUT/'aggregate-data-equivalence-report.json');eqreceipt=load(OUT/'aggregate-data-equivalence-receipt.json')
check('actual_Aggregate_fixed_Def_and_parent_author_freeze_bound',eqprov['actual_parent_definition_sha256']=='ef491f5136c5a98d976ff9faf73df3b65393bb2caf50772dccafd213c8302079' and all(sha(TASK/r['task_relative'])==r['sha256'] for r in eqprov['parent_frozen_bindings']) and sha(TASK/eqprov['alias_native_source'])==eqprov['alias_source_sha256']==sha(OUT/'dependencies/NativeValueComparisonDefinition.lean')==sha(PROJECT/'NativeValueComparisonDefinition.lean') and sha(TASK/eqprov['native_full_value_details_source'])==eqprov['native_full_value_details_source_sha256']=='8593fe0fb35a0eacc4195a0693eab2c9118916e51e548e51bf7d47b8bcb585c6',{'parent_frozen_bindings':len(eqprov['parent_frozen_bindings']),'Definition_proof_fields_are_closed':True})
check('four_true_native_staged_alias_and_full_value_executions_actually_zero',eqreceipt['complete'] and eqreceipt['borrowed_objects'] is False and len(eqreceipt['runs'])==4 and all(r['exit_code']==0 and sha(OUT/(r['label']+'.log'))==r['log_sha256'] and (OUT/(r['label']+'-exit.txt')).read_text().strip()=='0' for r in eqreceipt['runs']) and all(sha(TASK/e['object_task_relative'])==e['object_sha256'] for e in eqreport['environments']))
native_alias=(PROJECT/'NativeValueComparisonDefinition.lean').read_bytes();staged_alias=(PROJECT/'StagedValueComparisonDefinition.lean').read_bytes()
native_details=(PROJECT/'aggregate-native-value-details.lean').read_bytes();staged_details=(PROJECT/'aggregate-staged-value-details.lean').read_bytes()
apair=eqprov['alias_single_import_substitution'];dpair=eqprov['details_single_import_substitution']
check('shared_actual_alias_and_full_value_programs_differ_only_by_single_import',native_alias.count(apair['original'].encode())==1 and native_alias.replace(apair['original'].encode(),apair['staged'].encode())==staged_alias and native_details.count(dpair['original'].encode())==1 and native_details.replace(dpair['original'].encode(),dpair['staged'].encode())==staged_details and sha(TASK/eqprov['native_full_value_details_source'])==sha(PROJECT/'aggregate-native-value-details.lean') and all(sha(PROJECT/r['file'])==r['sha256']==sha(TASK/r['dependency_snapshot']) for r in eqprov['fresh_program_bindings']),{'native_import':'actual Native Aggregate','staged_import':'genuine Def Aggregate','other_code_changes':0})
alias_comparisons=[];eqproofs=[]
check('separate_native_and_staged_full_kernel_environments',len(eqreport['environments'])==2 and [e['context'] for e in eqreport['environments']]==['native','staged'])
for e in eqreport['environments']:
 rs=e['records'];context=e['context'];expected=[ANS+'.'+n for n in eqprov['alias_and_original_definition_names']]
 check(context+'_six_full_definition_type_value_kernel_comparisons',len(rs)==15 and [r['declaration'] for r in rs[:6]]==expected and all(r['kind']=='kernel_definition_value' and r['alias_declaration']==eqprov['alias_namespace']+'.'+n and r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['pp_proofs_enabled'] and r['original_expression_repr'] and r['comparison_expression_repr'] and set(r['axioms'])<=STD for n,r in zip(eqprov['alias_and_original_definition_names'],rs[:6])),{'true_isDefEq_calls':6,'proof_terms_and_full_Expr_repr_retained':True,'pretty_value_identity_claimed':False})
 alias_comparisons.extend(dict(r,context=context) for r in rs[:6]);eqproofs.extend(dict(r,context=context) for r in rs[6:])
 check(context+'_nine_closed_rfl_and_actual_data_equalities',e['actual_closed_rfl_and_data_equalities']==9 and [r['declaration'] for r in rs[6:]]==eqprov['closed_kernel_data_equality_proofs'] and all(r['kind']=='rfl_or_data_equality' and set(r['axioms'])<=STD for r in rs[6:]),{'whole_function_rfl':6,'actual_map_data_rfl':3})
check('actual_data_equivalence_closed_without_extra_hypotheses',eqreport['closed_rfl_and_data_equalities']==18 and eqreport['native_direct_full_value_comparisons']==6 and eqreport['staged_direct_full_value_comparisons']==6 and eqreport['all_standard_axioms'] and eqprov['extra_hypotheses']==[],{'actual_Lean_kernel_definitional_equality':'true native data = shared alias program = staged actual data in separate environments','F_kernel_triviality_claimed':False,'seven_context_checks_are_canonical_propagation':True})
kp=load(OUT/'kernel-data-equivalence-provenance.json');kr=load(OUT/'kernel-data-equivalence-receipt.json');kv=load(OUT/'kernel-data-equivalence-report.json')
KDEFS=[NS+'.'+n for n in kp['actual_definition_names']]
MAPS.update([NS+'.actualAggregateEquiv',NS+'.inverseMultiplier'])
check('four_actual_Kernel_native_staged_full_value_runs_zero',kr['complete'] and kr['borrowed_objects'] is False and len(kr['runs'])==4 and all(r['exit_code']==0 and sha(OUT/(r['label']+'.log'))==r['log_sha256'] and (OUT/(r['label']+'-exit.txt')).read_text().strip()=='0' for r in kr['runs']) and all(sha(TASK/e['object_task_relative'])==e['object_sha256'] for e in kv['environments']))
kn=(PROJECT/'NativeKernelValueComparisonDefinition.lean').read_bytes();ks=(PROJECT/'StagedKernelValueComparisonDefinition.lean').read_bytes();kd=(PROJECT/'kernel-native-value-details.lean').read_bytes();kds=(PROJECT/'kernel-staged-value-details.lean').read_bytes()
check('Kernel_alias_and_full_value_programs_only_one_import_diff',kn.count(b'import missions.zeta9.formalization.CoefficientMapKernelBridge')==1 and kn.replace(b'import missions.zeta9.formalization.CoefficientMapKernelBridge',b'import Definitions.Def_ZetaNine_CoefficientMapKernelBridge',1)==ks and kd.replace(b'import NativeKernelValueComparisonDefinition',b'import StagedKernelValueComparisonDefinition',1)==kds and all(sha(PROJECT/r['file'])==r['sha256']==sha(TASK/r['task_relative']) for r in kp['programs']) and kp['extra_hypotheses']==[])
kernel_value_records=[];kernel_rfl_records=[]
for e in kv['environments']:
 rs=e['records'];context=e['context']
 check(context+'_seven_Kernel_whole_type_value_isDefEq_with_full_Expr',len(rs)==14 and [r['declaration'] for r in rs[:7]]==KDEFS and all(r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['pp_proofs_enabled'] and r['original_expression_repr'] and r['comparison_expression_repr'] and set(r['axioms'])<=STD for r in rs[:7]),{'true_kernel_calls':7,'constructor_bijection_proof_field_included':True,'default_PP_raw_Expr_identity_claimed':False})
 check(context+'_seven_closed_Kernel_whole_value_rfl_equalities',len(rs[7:])==7 and all(r['kind']=='rfl_or_data_equality' and set(r['axioms'])<=STD for r in rs[7:]))
 kernel_value_records.extend(dict(r,context=context) for r in rs[:7]);kernel_rfl_records.extend(dict(r,context=context) for r in rs[7:])
canonical=reports['types_definition'];comparisons=[]
for d in defs:
 for c,rs in reports.items():
  r=rs[d['label']];pretty=r['value']==d['value'];same=r['value']==canonical[d['label']]['value'];sem=pretty or (d['label'] in MAPS and same)
  comparisons.append({'declaration':d['declaration'],'context':c,'type_equal':r['type']==d['type'],'pretty_value_equal':pretty,'canonical_staged_pretty_value_equal':same,'value_equal':sem,'equivalence_basis':'true native/staged full kernel equality through shared alias and proof irrelevance' if d['label'] in MAPS else 'exact original pretty value and source span','axioms':r['axioms']})
check('65_actual_Definitions_455_exact_types_and_verified_values',len(defs)==65 and len(comparisons)==455 and all(r['type_equal'] and r['value_equal'] and set(r['axioms'])<=STD and (r['pretty_value_equal'] or r['declaration'] in MAPS) for r in comparisons),{'pretty_value_comparisons_for_60_nonexception_Definitions':420,'five_proof_bearing_Definitions':'Aggregate6 and Kernel7 actual full type/value kernel calls in each native/staged environment, with canonical staged pretty values propagated across seven contexts','raw_Expr_equality_from_pretty_prints_claimed':False,'context_propagation_is_direct_native_kernel_call_claimed':False})
targets=[]
for i,t in enumerate(plan['targets']):
 n=t['theorem_name'];o=native[n];s=reports[f'types_{i}_solution'][n];r=reports[f'types_{i}_reference'][n]
 targets.append({'theorem':n,'actual_original_type':o['type'],'original_solution_reference_type_equal':o['type']==s['type']==r['type'],'original_axioms':o['axioms'],'solution_axioms':s['axioms'],'reference_axioms':r['axioms']})
check('three_actual_original_Solution_reference_types_exact',len(targets)==3 and all(t['original_solution_reference_type_equal'] for t in targets),targets)
check('all_complete_endpoint_proofs_standard_three_axioms',all(set(t['solution_axioms'])==STD==set(t['original_axioms']) for t in targets),sorted(STD))
per=24+len(prov['inline_helper_names']);helpers=[rows(OUT/f'helpers_{i}.log') for i in range(3)]
check('all_23_original_source_proofs_true_parent_closure_wrapper_closed',all(len(rs)==per and all(set(r['axioms'])<=STD for r in rs) for rs in helpers),{'records_per_Solution':per,'total':3*per,'original_source_proofs':23,'actual_inline_parent_helpers':prov['inline_helper_names']})
check('no_external_Theorem_Solution_or_mission_proof_import',all(not any(l.startswith(('import Theorems.','import Solutions.','import missions.')) for l in (OUT/'staged'/t['local_solution']).read_text(encoding='utf-8').splitlines()) for t in plan['targets']))
check('only_reference_statement_stubs_have_sorryAx',all('sorryAx' in t['reference_axioms'] for t in targets))
check('eleven_exact_genuine_parent_Definitions_frozen',len(plan['existing_definitions'])==11 and all(sha(TASK/d['task_relative'])==d['sha256']==sha(PROJECT/d['root_relative']) for d in plan['existing_definitions']),plan['existing_definitions'])
check('actual_pure_Harmonic_definition_copied_byte_for_byte',any(d['root_relative']=='Definitions/Def_ZetaNine_HarmonicStability.lean' and d['sha256']=='5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92' and sha(ROOT/d['root_relative'])==d['sha256'] for d in plan['existing_definitions']))
old_reports=[load(author/'type-report.json'),load(TASK/'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-boundary-types.json')]
for cb,old in zip(prov['native_closed_control_bindings'],old_reports):
 rs=lake_control_rows(OUT/('native-control-'+cb['module']+'.log'),cb['module']);by={r['declaration']:r for r in old}
 check('fresh_native_'+cb['module']+'_records_exact',sha(TASK/cb['task_relative'])==cb['sha256']==sha(PROJECT/(cb['module']+'.lean')) and len(rs)==len(old) and all(r['type']==by[r['declaration']]['type'] and r['definitionValue']==by[r['declaration']]['definitionValue'] and set(r['axioms'])<=STD for r in rs),{'records':len(rs)})
graph=rows(OUT/'decl_graph.jsonl');source=(TASK/'formalization/CoefficientMapKernelBridge.lean').read_bytes();facts=rows(OUT/'CoefficientMapKernelBridge-sketch_info.jsonl');refs=[f for f in facts if f['kind']=='ref']
control_modules={c['module'] for c in prov['native_closed_control_bindings']}
actual_control_roots=[g['name'] for g in graph if g['module'] in control_modules and g['startLine']>0]
check('real_Stage1_graph_Stage2_source_declarations_and_control_roots',len(graph)==prov['graph_records'] and not any(g['kind']=='axiom' for g in graph) and prov['source_declarations']==30 and prov['source_defs']==7 and prov['source_proofs']==23 and sum(f['kind']=='decl' for f in facts)==30 and set(prov['native_closed_control_roots'])==set(actual_control_roots),{'graph_records':len(graph),'control_roots_seed_the_true_parent_closure':prov['native_closed_control_roots'],'real_source_control_roots':len(actual_control_roots),'37_and_56_are_full_typed_record_counts_not_new_source_theorem_counts':True})
check('real_header_parser_keeps_true_Tel_Shift_Infinite_imports',prov['header']['start']['offset']==0 and source[:prov['header']['end']['offset']].decode().strip().splitlines()==['import missions.zeta9.formalization.CoefficientMapTelescoper','import missions.zeta9.formalization.CoefficientMapShiftDegree','import Mathlib.Order.Interval.Set.Infinite'])
sources={n:(TASK/'formalization'/f'{n}.lean').read_bytes() for n in receipt['source_sha256']};bridge=''
for module in ['CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity','CoefficientMapPartialFractions','CoefficientMapReflection','CoefficientMapFiniteSum','CoefficientMapSummation','CoefficientMapAggregate','CoefficientMapTelescoper','CoefficientMapShiftDegree']:
 hs=[f for f in prov['inline_helper_facts'] if f['module']==module]
 if not hs:continue
 bridge+='open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.'+module+'\n\n'
 opens=[f['fact'] for f in prov['bridge_open_context_facts'] if f['module']==module]
 for f in opens:bridge+=sources[module][f['span']['start']['offset']:f['span']['end']['offset']].decode()+'\n'
 if opens:bridge+='\n'
 for h in hs:
  f=h['fact'];bridge+=sources[module][f['declStart']['offset']:f['declEnd']['offset']].decode()+'\n\n'
 bridge+='end ZetaNine.'+module+'\n\n'
check('all_true_parent_proof_spans_and_open_contexts_exact',bridge.encode()==(OUT/'actual-proof-bridge.lean.inc').read_bytes() and hashlib.sha256(bridge.encode()).hexdigest()==prov['bridge_sha256'])
field=load(OUT/'embedded-bijection-provenance.json')
check('Equiv_bijection_closed_from_actual_graph_without_cycle',sha(OUT/'decl_graph.jsonl')==field['true_fresh_native_graph_sha256'] and field['closure_has_no_Equiv_inverse_or_prescribed_output_cycle'] and field['extra_hypotheses']==[] and field['no_kernel_bijection_inverse_output_or_HasSum_hypotheses_added'] and field['only_global_declarations_are_seven_original_Definitions'] and field['original_data_functions_unchanged'])
byname={g['name']:g for g in graph};seed=NS+'.original_five_dimensional_map_bijective';reached=set();queue=[seed]
while queue:
 name=queue.pop()
 if name in reached:continue
 reached.add(name);queue.extend(byname[name]['typeDeps']+byname[name]['valueDeps'])
expectedproofs={n for n in reached if byname[n]['kind']=='theorem' and byname[n]['startLine']>0}
check('embedded_true_bijection_proof_closure_exact_not_guessed',expectedproofs=={r['original_declaration'] for r in field['proof_closure_declarations']} and not any(NS+'.'+n in reached for n in ['actualAggregateEquiv','inverseMultiplier','prescribedL']))
available=set();localnames={r['original_declaration']:r['local_binding'] for r in field['proof_closure_declarations']};localterms=[]
for r in field['proof_closure_declarations']:
 f=r['parser_declaration_fact'];data=sources[r['module']];a=f['declStart']['offset'];b=f['declEnd']['offset'];start=r['parser_binding_fact']['end']['offset'];changes=[]
 assert hashlib.sha256(data[a:b]).hexdigest()==r['source_span_sha256'] and r['new_hypotheses']==[]
 for ref in r['parser_resolved_refs']:
  x,y=ref['start']['offset'],ref['end']['offset']
  if x<start:continue
  const=ref['const']
  if const in localnames:assert const in available;replacement=localnames[const]
  else:replacement=const
  changes.append((x-start,y-start,replacement.encode()))
 localterms.append('have '+r['local_binding']+edit(data[start:b],changes).decode());available.add(r['original_declaration'])
proof='((by\n'+''.join('    '+'\n    '.join(t.splitlines())+'\n' for t in localterms)+'    exact '+localnames[seed]+'\n  ) : '+field['exact_original_bijection_type']+')'
check('all_actual_embedded_proof_spans_and_parser_ref_renames_exact',proof+'\n'==(OUT/'closed-actual-aggregate-equiv-proof.lean.inc').read_text(encoding='utf-8-sig') and field['exact_original_bijection_type']==next(r['type'] for r in old_reports[0] if r['declaration']==seed),{'actual_closed_source_proofs':len(localterms),'new_hypotheses':[]})
definition=(OUT/'staged'/plan['local_definition']).read_text(encoding='utf-8-sig')
check('seven_genuine_Definition_spans_with_one_closed_field_change',len(prov['definition_facts'])==7 and sha(OUT/'staged'/plan['local_definition'])==field['definition_sha256']==sha(PROJECT/plan['local_definition']) and len(field['definition_transforms'])==7 and sum(r['constructor_proof_field_changed'] for r in field['definition_transforms'])==1 and kp['original_genuine_Definition_sha256']==field['definition_sha256'])
for o in field['true_source_open_contexts']:
 f=o['parser_fact'];assert o['text']==sources[o['module']][f['span']['start']['offset']:f['span']['end']['offset']].decode()
mathlib_imports=list(dict.fromkeys(line for name in receipt['source_sha256'] for line in sources[name].decode().splitlines() if line.startswith('import Mathlib.')))
assert mathlib_imports==field['actual_native_Mathlib_imports'] and 'import Mathlib.Tactic' in mathlib_imports
prefix='import Definitions.Def_ZetaNine_CoefficientMapTelescoper\nimport Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n'+'\n'.join(mathlib_imports)+'\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\nopen ZetaNine '+' '.join('ZetaNine.'+n for n in receipt['source_sha256'] if n!='CoefficientMapKernelBridge')+'\n'+'\n'.join(dict.fromkeys(o['text'] for o in field['true_source_open_contexts']))+'\n\nnamespace '+NS+'\n\n'
pieces=[]
for item in field['definition_transforms']:
 f=item['parser_fact'];a,b=f['declStart']['offset'],f['declEnd']['offset'];chunk=source[a:b]
 if item['constructor_proof_field_changed']:
  call=field['original_bijection_call_ref'];assert call['const']==seed
  chunk=edit(chunk,[(call['start']['offset']-a,call['end']['offset']-a,proof.encode())])
 pieces.append(chunk.decode())
rebuilt_definition=prefix+'\n\n'.join(pieces)+'\n\nend '+NS+'\n'
check('all_seven_original_data_spans_exact_except_actual_closed_bijection_field',rebuilt_definition==definition,{'new_global_proof_declarations':0,'new_hypotheses':[],'actual_native_Mathlib_imports_preserved':mathlib_imports})
ng=load(OUT/'kernel-native-global-declarations.json');sg=load(OUT/'kernel-staged-global-declarations.json')
check('actual_environment_genuine_Def_only_seven_top_level_data_declarations',len([r for r in ng if r['startLine']>0])==30 and len([r for r in sg if r['startLine']>0])==7 and {r['name'] for r in sg if r['startLine']>0}==set(KDEFS) and all(r['kind']=='def' for r in sg if r['startLine']>0) and not any(r['kind']=='axiom' for r in ng+sg),{'source_native_declarations':ng,'source_staged_declarations':sg})

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
 prefix='import Definitions.Def_ZetaNine_CoefficientMapKernelBridge\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n'+bridge
 openline='open ZetaNine '+NS+' ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.HarmonicStability\n'
 result=prefix+'\n'+edit(source,cuts+changes).decode()+'\n\n'+openline+'\ntheorem solution'+prov['targets'][full]['original_signature']+':= by\n  exact '+NS+'.checked_'+name+' '+t['wrapper_arguments']+'\n\n#print axioms solution\n'
 splices.append(result.encode()==(OUT/'staged'/t['local_solution']).read_bytes())
check('all_23_original_proof_bodies_and_three_parser_splices_exact',all(splices) and len(prov['deleted_diagnostic_facts'])==17,{'extra_hypotheses':[]})
req=load(OUT/'problems-request.json');dreq=load(OUT/'definitions-request.json')[0]
check('documented_API_request_fields_and_exact_Definition_body',set(req)=={'env','private','problems'} and all(set(p)<={'theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source','tags'} and p['formal_statement'].endswith(':= by sorry') and len(p['theorem_title'])<=200 for p in req['problems']) and set(dreq)<={'definition_name','definition_title','definition','natural_language_statement','source','tags','env','private'} and dreq['definition'].encode()==definition.encode())
check('actual_Even_n_ge2_rational_quartic_HasSum_scope_faithful',all('even' in p['natural_language_statement'] and 'n>=2' in p['natural_language_statement'] for p in req['problems']) and 'rational polynomial' in req['problems'][0]['natural_language_statement'] and 'HasSum' in req['problems'][2]['natural_language_statement'] and 'Summable' in req['problems'][2]['natural_language_statement'] and all(p['extra_hypotheses']==[] for p in prov['targets'].values()))
boundary=load(OUT/'stage-boundary-report.json');boundary_comparisons=[]
normalize=lambda s:s.replace('.checked_inverseMultiplier_actual_HasSum_and_absolute','.inverseMultiplier_actual_HasSum_and_absolute')
for run,old in zip(boundary['runs'],old_reports):
 by={r['declaration']:r for r in old}
 check(run['label']+'_actual_zero_standard_axioms',run['exit_code']==0 and len(run['records'])==len(old) and sha(OUT/(run['label']+'.log'))==run['log_sha256'] and (OUT/(run['label']+'-exit.txt')).read_text().strip()=='0' and run['all_standard_axioms'],{'records':len(run['records'])})
 for r in run['records']:
  d=normalize(r['declaration']);o=by[d]
  boundary_comparisons.append({'declaration':d,'type_equal':normalize(r['type'])==o['type'],'value_equal':r['definitionValue']==o['definitionValue'],'axioms':r['axioms']})
check('all_37_original_author_and_56_independent_records_exact_staged',boundary['all_zero'] and len(boundary_comparisons)==93 and all(r['type_equal'] and r['value_equal'] for r in boundary_comparisons),{'original_boundaries':'all56 independently fixed actual Kernel, inverse and HasSum controls replayed; n0 and n1 exclusions remain intact'})
check('integer_height_J_irrationality_not_in_batch_claims',not math.get('irrationality_closed',False) and not math.get('J_closed',False),{'actual_quartic_kernel_zero_bijection_and_rational_inverse_HasSum_are_claims':True,'integer_inverse_height_or_small_linear_forms_are_not_claims':True})
oldcounts={}
for name in ['coefficient-map','coefficient-map-jet','coefficient-map-injectivity','coefficient-map-partial-fractions','coefficient-map-reflection','coefficient-map-finite-sum','coefficient-map-summation','coefficient-map-aggregate','coefficient-map-telescoper','coefficient-map-shift-degree']:
 batch=TASK/'formalization/platform'/name;n=0
 for line in (batch/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
  h,rel=line.split('  ',1);assert sha(batch/rel)==h;n+=1
 oldcounts[name]=n
check('all_ten_old_platform_author_batches_frozen_and_unmodified',len(oldcounts)==10 and oldcounts['coefficient-map-summation']==199 and oldcounts['coefficient-map-shift-degree']==128 and oldcounts['coefficient-map-telescoper']==259,oldcounts)
copyfiles=[]
for rel in [plan['local_definition']]+[t[k] for t in plan['targets'] for k in ['local_solution','local_reference']]:
 p=OUT/'staged'/rel;dest=ROOT/rel;copyfiles.append({'staged_task_relative':p.relative_to(TASK).as_posix(),'root_relative_destination':rel,'bytes':p.stat().st_size,'sha256':sha(p),'destination_exists_at_author_freeze':dest.exists()})
 if dest.exists():assert sha(dest)==sha(p)
dump(OUT/'root-copy-plan.json',{'source_sha256':SOURCE_SHA,'sources_sha256':receipt['source_sha256'],'required_existing_Definitions':plan['existing_definitions'],'author_scope':'new task-local staged batch only; parent installs','overwrite_allowed':False,'files':copyfiles,'scope_build_entrypoints_for_parent':[t['local_solution'].removesuffix('.lean').replace('/','.') for t in plan['targets']]})
dump(OUT/'decl-plan.json',{'actual_source_declarations':30,'actual_native_sources':11,'pure_Harmonic_definition':True,'new_actual_Definitions':7,'complete_actual_proofs_per_Solution':23,'actual_graph_records':len(graph),'actual_inline_parent_helpers':prov['inline_helper_names'],'closed_control_source_roots':prov['native_closed_control_roots'],'selected_public_endpoints':[t['theorem_name'] for t in plan['targets']],'new_external_theorem_boundaries':[]})
limitations=['The actual original map is defined on rational quartics, and the endpoints retain Even n and 2<=n. True R shifts, actual telescoper quotient, infinitely many positive regular points and the polynomial identity yield quartic kernel zero; finite dimensionality yields actual five-dimensional bijection.',
 'Seven original Definitions are preserved. actualAggregateEquiv closes its actual constructor bijective proof from dependency-ordered genuine source proof spans, with no kernel/bijection/inverse/output/HasSum premise and no reference cycle through actualAggregateEquiv, inverseMultiplier or prescribedL.',
 'Seven true KernelBridge definitions and six actual Aggregate definitions each receive separate native/staged full isDefEq type/value calls through a shared alias program, pp.proofs=true and full Expr repr. Closed rfl equalities verify the whole data functions. Canonical staged pretty values propagate across seven contexts; these are not additional direct native kernel calls.',
 'The actual inverseMultiplier is a unique rational quartic with its actual output and genuine prescribed HasSum plus norm Summable. Integer inverse coefficients, denominator/height estimates, arbitrarily small nonzero integer linear forms, J and irrationality are not proved by this batch.',
 'All37 original author and56 independent typed records are freshly replayed natively and against the complete staged Solution. Every actual original proof and the true parent proof closure is retained. Reference statements intentionally carry sorryAx; Solutions and closed source proofs use only standard3.',
 'This author performed the earlier native mathematical review. That fixed review is not independent platform transplantation approval. Root installation, scoped build and platform publication/acceptance are separate parent stages.']
write(OUT/'README.md','# Actual KernelBridge offline author batch\n\nThree exact original endpoints, seven genuine new Definitions, all23 original proofs and the true parent proof closure are staged using actual graph/parser/header executions. Eleven actual native sources plus unchanged Harmonic Definition and eleven genuine parent Definitions are freshly compiled.\n\n'+'\n\n'.join(limitations)+'\n\nOnly this new task-local batch/cache was written; no Root/scope/API/credential write occurred.\n')

stable=[p for p in OUT.iterdir() if p.is_file() and p.name not in ['author-audit.json','source-manifest.json','SHA256SUMS.txt']]
stable+=list((OUT/'staged').rglob('*.lean'))+list((OUT/'dependencies').rglob('*.lean'))+list(PROJECT.glob('*.lean'))+[PROJECT/'lake-manifest.json',PROJECT/'lean-toolchain']
stable+=[PROJECT/'missions/zeta9/formalization'/f'{n}.lean' for n in receipt['source_sha256']]
stable+=list((PROJECT/'Definitions').glob('*.lean'))+list((PROJECT/'Solutions').glob('*.lean'))+list((PROJECT/'Theorems').glob('*.lean'));stable=list(dict.fromkeys(stable))
stable+=retained_attempts;stable=list(dict.fromkeys(stable))
fresh_cache=[{'task_relative':p.relative_to(TASK).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(BUILD.rglob('*')) if p.is_file()]
manifest={'schema_version':1,'source_sha256':SOURCE_SHA,'sources_sha256':receipt['source_sha256'],'files':[{'task_relative':p.relative_to(TASK).as_posix(),'batch_relative':p.relative_to(OUT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(stable)],'retained_attempt_files_excluded_from_success_evidence':[p.relative_to(OUT).as_posix() for p in retained_attempts],'fresh_compiler_cache_bindings':fresh_cache,'actual_parent_Definitions':plan['existing_definitions'],'prior_native_math_review_sha256':sha(mathfile),'Aggregate_proof_bearing_data_equivalence':eqprov,'Kernel_proof_bearing_data_equivalence':kp,'embedded_bijection_provenance':field,'native_author_bindings':author_bindings,'old_batches_modified':False}
dump(OUT/'source-manifest.json',manifest)
dump(OUT/'author-audit.json',{'schema_version':1,'review_role':'new platform author; earlier native math reviewer; separate independent transplantation review required','verdict':'PASS','source_sha256':SOURCE_SHA,'sources_sha256':receipt['source_sha256'],'lean_toolchain':'leanprover/lean4:v4.33.1','mathlib_rev':REV,'checks':checks,'targets':targets,'definition_comparisons':comparisons,'native_alias_comparisons':alias_comparisons,'closed_actual_data_equalities':eqproofs,'kernel_full_value_comparisons':kernel_value_records,'kernel_closed_whole_value_equalities':kernel_rfl_records,'all_proof_records':helpers,'boundary_comparisons':boundary_comparisons,'actual_cross_module_helpers':prov['inline_helper_names'],'limitations':limitations,'platform_published':False,'platform_accepted':False,'root_installed_by_author':False,'root_scope_API_credential_writes':False,'independent_transplantation_review_claimed':False,'stable_files':manifest['files']})
freeze=stable+[OUT/'source-manifest.json',OUT/'author-audit.json'];write(OUT/'SHA256SUMS.txt',''.join(sha(p)+'  '+p.relative_to(OUT).as_posix()+'\n' for p in sorted(freeze)))
for line in (OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,rel=line.split('  ',1);assert sha(OUT/rel)==h
print(json.dumps({'author_verdict':'PASS','checks':len(checks),'definition_comparisons':455,'60_nonexception_pretty_definition_values_exact':True,'actual_Aggregate_and_Kernel_proof_fields_full_kernel_equal':True,'native_full_value_kernel_records':6,'staged_full_value_kernel_records':6,'closed_rfl_data_records':18,'source_proof_records':3*per,'boundary_records':93,'frozen_files':len(freeze),'author_sha256':sha(OUT/'author-audit.json'),'copyplan_sha256':sha(OUT/'root-copy-plan.json'),'manifest_sha256':sha(OUT/'source-manifest.json'),'SHA256SUMS_sha256':sha(OUT/'SHA256SUMS.txt')},ensure_ascii=False))
