from run import *
import re, datetime

prep=verify()
plan=load(OUT/'audit-plan.json')
receipt=load(OUT/'compile-receipt.json')
checks=[]
standard={'propext','Classical.choice','Quot.sound'}
def check(name, passed, evidence=None):
    checks.append({'name':name,'pass':bool(passed),'evidence':evidence})
    assert passed,name
def execution(logical):
    rs=[r for r in receipt['rows'] if r['logical']==logical]
    assert len(rs)==1 and rs[0]['actual_exit']==0
    return rs[0]
def records(logical):
    r=execution(logical)
    return [json.loads(s) for s in (OUT/r['log']).read_text(encoding='utf8').splitlines() if s.startswith('{')]
def cleaned(s): return re.sub(r'\s+','',re.sub(r'--[^\n]*','',re.sub(r'/-[\s\S]*?-/','',s)))

pf=TASK/'formalization/CoefficientMapNumeratorPartialFractions.lean'
data=TASK/'formalization/CoefficientMapFormalTransportData.lean'
failed=[r for r in receipt['rows'] if r['actual_exit']!=0]
successful=[r for r in receipt['rows'] if r['actual_exit']==0]
check('exactly one original own boundary Lean failure retained excluded',len(failed)==1 and failed[0]['label']=='r08')
check('all required final compiler and audit executions succeeded',len(successful)==9 and len(receipt['rows'])==10)
for r in receipt['rows']:
    assert sha(OUT/r['snapshot'])==r['snapshot_sha256']==r['source_sha256']
    for k,h in [('log','log_sha256'),('exit_file','exit_sha256'),('wrapper','wrapper_sha256')]:
        assert sha(OUT/r[k])==r[h]
    assert int((OUT/r['exit_file']).read_text())==r['actual_exit']
    if r['output_sha256']:
        object_snapshot=OUT/(r['label']+'.olean')
        assert sha(object_snapshot)==r['output_sha256']
check('all actual source snapshots logs exits wrappers and successful object snapshots hash bound',True)
check('original Data frozen bytes compiled personally no ft1 object reuse',
      sha(data)==sha(OUT/'d0.lean')=='ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27'
      and execution('actual own CoefficientMapFormalTransportData')['source_sha256']==sha(data))
check('PF original snapshot preserved and final source proof scripts unchanged except documentation',
      sha(OUT/'p0.lean')=='929b1b89943e96c0cfe823d66698ad0465ec3081cb7cd3b603bbe8340c062787'
      and cleaned(pf.read_text(encoding='utf8'))==cleaned((OUT/'p0.lean').read_text(encoding='utf8')))
final=[r for r in receipt['rows'] if r['logical']=='actual own CoefficientMapNumeratorPartialFractions'][-1]
check('final PF source own mirror and actual object bound',
      final['actual_exit']==0 and final['source_sha256']==sha(pf)==sha(PROJECT/'missions/zeta9/formalization/CoefficientMapNumeratorPartialFractions.lean')
      and final['output_sha256']==sha(TASK/final['output_task_relative']))
reg=load(OUT/'historical-object-regeneration.json')
check('initial PF object replaced before archive and explicitly reproduced exact without overwriting final cache',
      reg['first_object_explicitly_reproduced_from_identical_original_project_source_bytes']
      and reg['reproduced_object_sha256_exact_matches_initial_actual_output_hash']==reg['initial_output_sha256']
      and sha(OUT/'r02.olean')==reg['initial_output_sha256'],reg)
check('14 PS author parent objects exactly bound copied authorized reused and never called fresh',
      len(prep['reused_parent_objects'])==14 and not prep['PS_parent_builds_claimed_fresh'])
check('prior PS native author frozen source log and object bindings intact',
      len(prep['author_stable_files'])==59,{'PS_author_audit_sha256':prep['PS_author_audit_sha256']})
typ=records('actual own types')
defs=[r for r in typ if r['kind']=='definition_full_expression']
proofs=[r for r in typ if r['kind']=='proof_full_type']
check('16 actual Definition full types and full values and24 source proof complete types emitted',
      [r['declaration'] for r in defs]==plan['actual_definition_names'] and len(defs)==16
      and [r['declaration'] for r in proofs]==plan['actual_proof_names'] and len(proofs)==24)
check('all source Definitions and complete proof types standard three only',
      all(set(r['axioms'])<=standard for r in typ))
val=records('actual own values')
kernel=[r for r in val if r['kind']=='native_alias_whole_value_kernel']
rfl=[r for r in val if r['kind']=='proof_full_type']
check('16 actual entire Definition kernel comparisons and16 closed whole function rfl certificates',
      len(kernel)==len(rfl)==16 and all(r['type_kernel_equal'] and r['full_value_kernel_equal'] for r in kernel)
      and [r['declaration'] for r in kernel]==plan['actual_definition_names']
      and [r['declaration'] for r in rfl]==[r['closed_rfl'] for r in plan['full_value_aliases']])
check('all full value certificates standard three only and full proof values preserved',
      all(set(r['axioms'])<=standard for r in val)
      and all(r['original_full_value_expression_repr'] and r['alias_full_value_expression_repr'] for r in kernel))
bound=records('actual own repaired boundaries and three exact endpoint kernel types')
bp=[r for r in bound if r['kind']=='proof_full_type']
et=[r for r in bound if r['kind']=='explicit_endpoint_type_kernel']
check('15 new generic and genuine boundary statements closed standard three only',
      len(bp)==15 and [r['declaration'] for r in bp]==plan['own_endpoint_and_boundary_names']
      and all(set(r['axioms'])<=standard for r in bp))
check('three explicit generic endpoint whole types match kernel without extra PF hypotheses',
      len(et)==3 and all(r['whole_type_kernel_equal'] for r in et),et)
required=['checked_zero_actual_jet','checked_zero_numerator_reconstruction','checked_m0_Aone_reconstruction',
          'checked_m0_critical_X8_reconstruction','checked_m0_X9_is_excluded','checked_m0_simple_pole_of_X8',
          'checked_m0_simple_pole_regular_PF','checked_two_pole_constant_reconstruction',
          'checked_n1_q1_actual_shifted_remainder','checked_n1_q1_actual_remainder_reconstruction']
check('m arbitrary zero m0 critical1/t degree threshold two poles n1 true Q boundaries retained',
      all(n in [r['declaration'] for r in bp] for n in required))
repair=load(OUT/'boundary-repair-plan.json')
failed_rows=[json.loads(s) for s in (OUT/'r08.log').read_text(encoding='utf8').splitlines() if s.startswith('{')]
check('failed source log exit and propagated sorryAx records retained entirely excluded',
      sha(OUT/'boundaries.lean')==repair['failed_source_preserved']
      and any('sorryAx' in r.get('axioms',[]) for r in failed_rows)
      and repair['failed_records_including_sorryAx_all_excluded'])
check('failure display Python GBK diagnostic recorded separately from actual Lean1',
      repair['failure_log_display_Python_exit']==1 and repair['Lean_exit']==1)
resolution=records('actual own resolver')
env=resolution[0]
paths=[Path(p).resolve() for p in env['LEAN_PATH'].split(';') if p]
check('actual Lean4.33.1 and explicit only own cache plus fixed package environment',
      env['Lean_version']=='4.33.1' and paths[0]==CACHE.resolve()
      and all(p.is_relative_to((ROOT/'.lake/packages').resolve()) for p in paths[1:]))
check('17 actual object resolutions own copies with14 declared reused and3 fresh new modules',
      len(resolution)==18 and [r['module'] for r in resolution[1:]]==plan['actual_module_resolver_names']
      and all(Path(r['object']).resolve()==(CACHE/(r['module'].replace('.','/')+'.olean')).resolve() for r in resolution[1:]))
manifest=load(PROJECT/'lake-manifest.json')
rev=next(r['rev'] for r in manifest['packages'] if r['name']=='mathlib')
git=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
write(OUT/'mathlib-revision.log',git.stdout+git.stderr)
check('actual fixed Mathlib git revision and toolchain bytes',
      git.returncode==0 and git.stdout.decode().strip()==rev==prep['Mathlib_revision']
      and (PROJECT/'lean-toolchain').read_text().strip()==prep['Lean_toolchain'])
text=re.sub(r'--[^\n]*','',re.sub(r'/-[\s\S]*?-/','',pf.read_text(encoding='utf8')))
check('final PF has no admission axiom statement mirror or unsafe kernel bypass',
      not re.search(r'\b(?:sorry|admit)\b|^\s*(?:axiom|constant|opaque)\b|skipKernelTC|unsafe\s+(?:def|theorem)',text,re.M))
check('no Root proofcache independent proof objects API scope credentials or ft1 objects used',
      not prep['Root_proofcache_or_independent_objects_borrowed'] and not prep['Data_ft1_author_object_borrowed'])
diagnostic=load(OUT/'freeze-preflight-diagnostic.json')
check('initial pure documentation comparator diagnostic retained and actual Lean-comment comparison passed',
      diagnostic['actual_Python_exit']==1 and diagnostic['Lean_invocations']==0
      and not diagnostic['source_or_Lean_log_exit_objects_changed'])
diagnostic['corrected_actual_Python_exit']=0
dump(OUT/'freeze-preflight-diagnostic.json',diagnostic)
summary={'actual_successful_Lean_calls':len(successful),'actual_failed_Lean_calls':len(failed),
         'reused_PS_author_parent_objects_not_fresh':14,'fresh_own_Data_PF_alias_modules':3,
         'complete_Data_PF_definition_records':16,'complete_Data_PF_source_proof_records':24,
         'whole_definition_value_kernel_calls':16,'closed_whole_function_rfl_proofs':16,
         'own_generic_and_boundary_proofs':15,'exact_generic_endpoint_whole_type_kernel_calls':3,
         'actual_own_module_resolutions':17,'PF_five_output_transport_proved':False}
dump(OUT/'actual-summary.json',summary)
fixed=[ROOT/r['root_relative'] for r in prep['author_stable_files']]+[PS/'author-audit.json',PS/'preparation-state.json']
fixed+=[TASK/r['origin_task_relative'] for r in prep['reused_parent_objects']]
fixed+=[p for p in PROJECT.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
fixed+=[p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['author-audit.json','SHA256SUMS.txt','source-manifest.json']]
fixed+=[pf,data,TASK/'research/coefficient-map-numerator-pf-offline-preparation-2026-10-04.json',
        TASK/'research/coefficient-map-numerator-pf-offline-preparation-2026-10-04.md',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']
bindings=[]
for p in sorted(set(p.resolve() for p in fixed),key=lambda p:p.as_posix()):
    assert p.is_relative_to(ROOT.resolve())
    r={'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
    if p.is_relative_to(TASK.resolve()):r['task_relative']=p.relative_to(TASK).as_posix()
    bindings.append(r)
report={'verdict':'PASS','stage':'native author only; independent native/platform review pending',
        'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':sha(pf),
        'Data_source_sha256':sha(data),'checks':checks,'counts':summary,'stable_files':bindings,
        'main_source_proof_scripts_changed_from_original':False,
        'parent_objects_explicitly_reused_not_fresh':True,'independent_review':'PENDING',
        'platform_acceptance_claimed':False,'five_formal_output_transport_proved':False,
        'retained_failures':[failed[0]],'diagnostics':repair,'historical_object_regeneration':reg,
        'evidence_boundary':'Arbitrary m and actual polynomial A, strict degree and regular-point conditions unchanged. No abstract PF array, PF-existence hypothesis, zeta independence, F transport, integer height or irrationality assertion.'}
dump(OUT/'source-manifest.json',{'source_sha256':sha(pf),'Data_source_sha256':sha(data),'files':bindings})
dump(OUT/'author-audit.json',report)
sumfiles=[p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='SHA256SUMS.txt']
write(OUT/'SHA256SUMS.txt',''.join(sha(p)+'  '+p.relative_to(OUT).as_posix()+'\n' for p in sorted(sumfiles)))
for r in bindings:
    p=ROOT/r['root_relative']
    assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
print('NumeratorPF native author PASS',len(checks),'checks',len(bindings),'stable bindings.',flush=True)
print('Final source SHA',sha(pf),'author-audit SHA',sha(OUT/'author-audit.json'),flush=True)
