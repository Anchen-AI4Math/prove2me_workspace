"""Freeze actual native author evidence; honest same-author parent-object reuse."""
from run_author import *
import re,ast
gate();state=load(OUT/'preparation-state.json');receipt=load(OUT/'actual-execution-receipt.json')
checks=[]
def check(name,condition,evidence=None):
 checks.append({'name':name,'pass':bool(condition),'evidence':evidence})
 if not condition:
  idx=1+len(list(OUT.glob('retained-freeze-failure-*.json')))
  dump(OUT/('retained-freeze-failure-'+str(idx).zfill(2)+'.json'),{'status':'FAIL','Lean_invocations':0,'checks':checks,'excluded':True})
  raise AssertionError(name)
def step(mode,name):
 r=[x for x in receipt['rows'] if x['mode']==mode and x['name']==name and x['actual_exit']==0]
 assert len(r)==1;return r[0]
def readlog(mode,name):return (ROOT/step(mode,name)['log']['root_relative']).read_text(encoding='utf-8-sig')
def records(mode,name):return [json.loads(x) for x in readlog(mode,name).splitlines() if x.startswith('{')]
for r in receipt['rows']:
 for k in ['actual_input','log','exit_file']:
  p=ROOT/r[k]['root_relative'];assert sha(p)==r[k]['sha256'] and p.stat().st_size==r[k]['bytes']
 assert (ROOT/r['exit_file']['root_relative']).read_text().strip()==str(r['actual_exit'])
 if r['actual_exit']==0:
  p=ROOT/r['source']['root_relative'];assert sha(p)==r['source']['sha256']
  if r['object']:
   p=ROOT/r['object']['root_relative'];q=ROOT/r['retained_object']['root_relative'];assert sha(p)==sha(q)==r['object']['sha256']
check('all_actual_receipts_inputs_full_logs_exits_success_source_objects_current',True)
check('frozen_PS_author59_unchanged_actual_parent_compilation_receipts',len(load(AUTHOR/'author-audit.json')['stable_files'])==59,{'sha256':AUTHOR_SHA,'actual_parent_source_builds':13,'actual_final_PS_source_builds':1})
check('fourteen_same_author_parent_modules_exact_sources_and_objects_reused',len(state['parent_modules'])==14 and len(state['parent_source_and_objects'])==42 and len(state['new_project_copies'])==42,{'parent_project':str(PARENT),'fresh_parent_build_claimed':False,'independent_objects_borrowed':False})
data=TASK/'formalization/CoefficientMapFormalTransportData.lean';bounds=TASK/'formalization/CoefficientMapFormalTransportBounds.lean'
check('design_frozen_Data_exact_unchanged_and_actual_compiled_zero',sha(data)==state['frozen_data_sha256']=='ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27' and step('compile',data.stem)['actual_exit']==0,bind(data))
check('final_Bounds_actual_compiled_zero',step('compile',bounds.stem)['actual_exit']==0 and sha(bounds)==step('compile',bounds.stem)['source']['sha256'],bind(bounds))
design=load(ROOT/state['design_freeze']['root_relative'])
for r in design['files']:
 p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
check('original_mathematical_design_freeze_all_five_files_unchanged',len(design['files'])==5,{'finite_168_checks_historical_not_new_universal_proof':True})
src=records('audit','source-full-audit.lean');values=records('audit','whole-values.lean');endpoints=records('audit','endpoint-audit.lean')
standard={'propext','Classical.choice','Quot.sound'}
check('source33_complete_actual_types_12_full_definition_values_21proofs',len(src)==33 and sum(x['kind']=='def' for x in src)==12 and sum(x['kind']=='theorem' for x in src)==21 and sum(x['full_definition_value_expression_repr'] is not None for x in src)==12 and all(x['full_type_expression_repr'] for x in src))
check('source33_actual_axioms_only_standard_three',all(set(x['axioms'])<=standard for x in src),sorted(standard))
check('all12_Data_complete_function_values_closed_by_rfl',len(values)==12 and all(set(x['axioms'])<=standard and x['full_type_expression_repr'] for x in values))
check('nine_explicit_full_type_boundary_and_index_guard_proofs',len(endpoints)==9 and all(set(x['axioms'])<=standard and x['full_type_expression_repr'] for x in endpoints))
names={x['declaration'].split('.')[-1] for x in endpoints}
check('actual_choice_degree_spec_equation_positive_domain_typed',{'chosen_pair_full_type'}<=names)
check('Gamma_row_recovers_actual_P_typed',{'Gamma_recovery_full_type'}<=names)
check('actual_polynomial_zero_t_two_n_ge_one_typed',{'actual_zero_at_two_full_type'}<=names)
check('shifted_degree_2n_plus18_and_real_denominator_strictproper_typed',{'actual_shifted_degree_full_type','actual_strict_proper_full_type'}<=names)
check('n_one_zero_and_strictproper_actual_typed_boundary',{'original_n_one_zero_and_proper'}<=names)
check('n_zero_choice_convention_and_guarded_zero_indices_typed',{'n_zero_choice_is_data_convention','previous_index_zero_guard','old_index_zero_guard'}<=names)
rawdata=data.read_text(encoding='utf-8-sig');rawbounds=bounds.read_text(encoding='utf-8-sig')
check('actual_Data12defs_one_inherited_spec_Bounds20theorems_no_new_axioms_admissions',len(re.findall(r'^def ',rawdata,re.M))==12 and len(re.findall(r'^theorem ',rawdata,re.M))==1 and len(re.findall(r'^theorem ',rawbounds,re.M))==20 and len(re.findall(r'^def ',rawbounds,re.M))==0 and not any(re.search(r'^(?:axiom|unsafe)\b|\b(?:sorry|admit)\b',s,re.M) for s in [rawdata,rawbounds]))
failure=[r for r in receipt['rows'] if r['actual_exit']!=0]
assert len(failure)==1 and failure[0]['label']=='e02' and failure[0]['actual_exit']==1
old=(ROOT/failure[0]['actual_input']['root_relative']).read_text(encoding='utf-8-sig')
corrected=old.replace('_ = n := by simp\n','_ = n := by\n        simp only [natDegree_X_sub_C]\n        simp\n',1).replace('_ = n := by simp\n','_ = n := by\n        simp only [natDegree_X_add_C]\n        simp\n',1)
error=(ROOT/failure[0]['log']['root_relative']).read_text(encoding='utf-8-sig')
check('first_Bounds_compile1_complete_retained_only_two_simp_proof_repairs',corrected==rawbounds and error.count('error: unsolved goals')==2,{'failed_step':'e02','all_failed_run_excluded':True,'Data_unchanged':True,'types_and_mathematical_hypotheses_unchanged':True})
resolved=records('resolver','resolver.lean');modules=state['parent_modules']+['missions.zeta9.formalization.CoefficientMapFormalTransportData','missions.zeta9.formalization.CoefficientMapFormalTransportBounds'];assert len(resolved)==17
paths=[Path(x).resolve() for x in resolved[0]['LEAN_PATH'].split(';') if x]
cache=(PROJECT/'b/lib/lean').resolve()
package_caches={(ROOT/'.lake/packages'/r['name']/'.lake/build/lib/lean').resolve() for r in load(PROJECT/'lake-manifest.json')['packages']}
runtime_library=Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean').resolve()
check('actual_exact_allowed_search_path_no_Root_author_or_independent_fallback',cache in paths and set(paths)<=package_caches|{cache,runtime_library},{'actual_path':resolved[0]['LEAN_PATH']})
objects=[]
for m,r in zip(modules,resolved[1:]):
 p=cache/(m.replace('.','/')+'.olean');assert r['module']==m and Path(r['resolved_olean']).resolve()==p.resolve()
 if m in state['parent_modules']:
  origin=PARENT/'b/lib/lean'/(m.replace('.','/')+'.olean');assert sha(p)==sha(origin);kind='same-author previous actual parent object copy'
 else:
  original=step('compile',m.split('.')[-1]);assert sha(p)==original['object']['sha256'];kind='new module compiled in this run'
 objects.append({'module':m,'origin':kind,**bind(p)})
check('actualfindOLean_all16_exact_author_project_objects_parent_origin_distinguished',True,objects)
check('actual_Lean4_33_1_pinned_runtime_and_manifest_bytes','version 4.33.1' in readlog('runtime','actual pinned runtime') and (PROJECT/'lean-toolchain').read_bytes()==(ROOT/'lean-toolchain').read_bytes() and (PROJECT/'lake-manifest.json').read_bytes()==(ROOT/'lake-manifest.json').read_bytes())
revision=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
write(OUT/'actual-mathlib-revision.log',revision.stdout+revision.stderr);write(OUT/'actual-mathlib-revision-exit.txt',str(revision.returncode)+'\n')
lib=next(x for x in load(PROJECT/'lake-manifest.json')['packages'] if x['name']=='mathlib')
check('actual_Mathlib_revision_matches_fixed_manifest',revision.returncode==0 and revision.stdout.decode().strip()==lib['rev']=='0df444a360eaa60ab8c11dca51a86af692955474')
success=[r for r in receipt['rows'] if r['actual_exit']==0]
check('seven_actual_successes_six_Lean_plus_runtime_one_failure_excluded',len(success)==7 and len(failure)==1 and len(receipt['rows'])==8)
for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
check('task_only_new_author_files_no_parent_Root_API_credentials_scope_writes',True)
counts={'parent_modules_reused':14,'fresh_parent_builds_claimed':0,'new_module_successful_compiles':2,'new_module_failed_compiles_retained_excluded':1,'successful_Lean_compiles_and_audits':6,'runtime_version_invocations':1,'all_actual_successful_invocations':7,'source_records':33,'Data_definitions':12,'Data_inherited_witness_proofs':1,'Bounds_theorems':20,'whole_function_Data_rfl_proofs':12,'explicit_endpoints_and_guards':9,'Std3_records':54,'actual_module_resolutions':16}
dump(OUT/'actual-counts.json',counts)
author=load(AUTHOR/'author-audit.json')
fixed=[AUTHOR/'author-audit.json']+[ROOT/r['root_relative'] for r in author['stable_files']]
fixed += [ROOT/r['root_relative'] for r in state['parent_source_and_objects']+state['new_project_copies']+state['pinned_runtime']+[state['design_freeze']]]
fixed += [TASK/r['task_relative'] for r in design['files']]+[bounds]
fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='author-audit.json']
for directory,dirs,files in os.walk(PROJECT):
 dirs[:]=[x for x in dirs if x not in ['.lake','__pycache__']]
 fixed += [Path(directory)/name for name in files]
fixed += [p for p in (PROJECT/'.lake').iterdir() if p.is_file()]
fixed=sorted({p.resolve() for p in fixed},key=lambda x:x.as_posix());bindings=[]
for p in fixed:
 assert p.is_relative_to(ROOT.resolve());r=bind(p)
 if p.is_relative_to(TASK):r['task_relative']=p.relative_to(TASK).as_posix()
 bindings.append(r)
report={'schema_version':1,'verdict':'PASS','stage':'NATIVE AUTHOR ONLY','scope':'ACTUAL_CHOSEN_PAIR_GAMMA_RESTORATION_TRUE_NUMERATOR_ZERO_AND_STRICT_PROPER_BOUND_ONLY',
 'Data_sha256':sha(data),'Data_bytes':data.stat().st_size,'Bounds_sha256':sha(bounds),'Bounds_bytes':bounds.stat().st_size,
 'frozen_parent_author_sha256':AUTHOR_SHA,'checks':checks,'counts':counts,'stable_files':bindings,'actual_source_records':src,'actual_whole_function_value_records':values,'actual_explicit_endpoint_records':endpoints,
 'parent_cache_reused':True,'fresh_parent_build_claimed':False,'independent_objects_borrowed':False,'parent_or_Root_API_credentials_scope_modified':False,
 'all_actual_success_receipts':success,'retained_failed_attempts':failure,
 'independent_review':'PENDING','platform_acceptance_claimed':False,'general_proper_numerator_PF_proved':False,'five_output_parameter_transport_proved':False,'HasSum_parameter_transport_proved':False,'irrationality_proved':False,
 'findings':[{'topic':'choice','detail':'The original frozen Data bytes choose the actual unique Connection pair for n>=1. Its original n=0 zero convention is exactly audited and is not substituted into positive-n specifications.'},
 {'topic':'Gamma','detail':'The actual coefficient row Gamma recovers the actual quartic P, with new monomial rows and old P coefficient columns. No five-output matrix transport identity is proved here.'},
 {'topic':'numerator','detail':'The true polynomial cancellation numerator vanishes at t=2 for every n>=1 and every q, including n=1, directly from the i=0 product factor. Its shifted version vanishes at x=1. The degree bound holds including q=0, while strict properness retains n>=1. The true degree of the denominator polePolynomial(n+1)^9 is used in the final strict inequality.'},
 {'topic':'cache','detail':'Fourteen previously compiled same-author PS parent objects are copied with exact source/object bindings into ft1; two new modules are compiled here. No parent object is rewritten, no independent or Root proof object is borrowed, and no fresh parent build is claimed. Actual findOLean resolves all sixteen modules inside ft1.'},
 {'topic':'history','detail':'The first Bounds source compile failed only because broad simp expanded C before the degree-one identities matched. Its full source, log and actual exit1 remain retained and excluded. Exactly the two simp proof lines were repaired; Data, theorem types and mathematical conditions were unchanged. Historical UNCOMPILED text in the frozen Data/design remains unchanged; actual current compile/audit evidence governs this author verdict.'}]}
dump(OUT/'author-audit.json',report)
for r in bindings:
 p=ROOT/r['root_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
gate()
print('FormalTransport Data/Bounds native author PASS',len(checks),'checks',len(bindings),'bindings',flush=True)
print('Data',sha(data),data.stat().st_size,'Bounds',sha(bounds),bounds.stat().st_size,flush=True)
print('Report SHA256',sha(OUT/'author-audit.json'),'bytes',(OUT/'author-audit.json').stat().st_size,flush=True)
