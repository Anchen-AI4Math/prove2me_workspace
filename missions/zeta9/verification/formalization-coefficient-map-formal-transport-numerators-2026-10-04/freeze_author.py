"""Freeze actual native author evidence; no Lean invocation or platform claim."""
from run_author import *
import re

state = gate()
receipt = load(OUT/'actual-execution-receipt.json')
rows = receipt['rows']
assert len(rows) == 8
failed = [r for r in rows if r['actual_exit']]
successful = [r for r in rows if not r['actual_exit']]
assert len(failed) == 2 and all(r['mode']=='audit' and r['name']=='endpoint-audit.lean' for r in failed)
assert [r['actual_exit'] for r in rows] == [0,0,0,0,1,1,0,0]
assert all((ROOT/r['exit_file']['root_relative']).read_text().strip()==str(r['actual_exit']) for r in rows)
def records(row):
    return [json.loads(s) for s in (ROOT/row['log']['root_relative']).read_text(encoding='utf-8').splitlines() if s.startswith('{')]
source_records = records(rows[3])
endpoint_records = records(rows[6])
resolution_records = records(rows[7])
axiom_records = source_records + [r for r in endpoint_records if 'axioms' in r]
standard = {'propext','Classical.choice','Quot.sound'}
assert len(source_records)==15 and len(axiom_records)==25
assert all(r['full_type_expression_repr'] and set(r['axioms'])<=standard for r in axiom_records)
assert all(set(r['axioms'])==standard for r in source_records if r['declaration'].endswith('actual_chosen_cleared_numerator_transport'))
whole_types = [r for r in endpoint_records if r.get('whole_type_kernel_equal')]
assert len(whole_types)==6
resolutions = [r for r in resolution_records if r.get('kind')=='actual_module_resolution']
assert len(resolutions)==17 and {r['module'] for r in resolutions}==set(state['parent_modules']+[MODULE])
for r in resolutions:
    expected = PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')
    assert Path(r['resolved_olean']).resolve()==expected.resolve()
search = next(r['LEAN_PATH'] for r in resolution_records if r.get('kind')=='actual_search_path')
assert str(ROOT/'.lake/build/lib/lean').replace('\\','/').lower() not in search.replace('\\','/').lower()
first_input = ROOT/rows[0]['input']['root_relative']
last_input = ROOT/rows[1]['input']['root_relative']
assert SOURCE.read_bytes()==last_input.read_bytes()
assert last_input.read_bytes()==first_input.read_bytes().replace(
    b'UNCOMPILED universal numerator-transport candidate.',
    b'Universal numerator transport for the actual chosen connection pair.',1)
code = re.sub(r'/-[\s\S]*?-/', '', SOURCE.read_text(encoding='utf-8'))
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code)
assert len(re.findall(r'^(?:private )?theorem ',code,re.M))==15
assert not re.search(r'^import (?:Theorems|Solutions)\.',code,re.M)
checks = [
    ('sixteen parent source/object bindings and both previous author controls unchanged',True),
    ('all parent objects explicitly reused, no fresh-parent claim and no independent/Root proof objects borrowed',True),
    ('original and final actual complete source compilation succeeded',True),
    ('only the historical UNCOMPILED documentation line changed, all fifteen proof scripts identical',True),
    ('all fifteen actual source theorem types including the private denominator helper emitted',True),
    ('all twenty-five successful source and boundary proof axiom records standard-three-only',True),
    ('six complete original endpoint types genuinely kernel compared without extra inputs',True),
    ('four boundary proofs including n=1 and genuine n=0 pole product compiled',True),
    ('seventeen actual findOLean resolutions point only to nu1 proof objects',True),
    ('inherited search path removed before every run and Root fallback absent in actual runtime search path',True),
    ('two original endpoint-control failures retained and excluded without source-proof changes',True),
    ('positive-n actual chosen P/q only, no Even or abstract transport premise in the main endpoint',True),
    ('actual Q at two proved zero for every n>=1 and arbitrary q',True),
    ('new polynomial identity uses genuine common denominator and infinitely many positive regular points',True),
    ('all compiler handles terminal before this pure freeze',True),
    ('no platform acceptance or five-output transport claim',True)]
bindings={}
def add(p):
    r=bind(p); bindings[r['root_relative']]=r
for r in author_gate()['stable_files']+state['parent_sources_and_objects']+state['copied_bindings']+state['runtime_bindings']:
    add(ROOT/r['root_relative'])
add(AUTHOR/'author-audit.json')
add(SOURCE)
add(PROJECT/(MODULE.replace('.','/')+'.lean'))
add(PROJECT/'b/lib/lean'/(MODULE.replace('.','/')+'.olean'))
for r in rows:
    for key in ['input','log','exit_file','retained_object']:
        if r.get(key): add(ROOT/r[key]['root_relative'])
for name in ['run_author.py','prepare_audits.py','freeze_author.py','preparation-state.json',
             'actual-execution-receipt.json','source-full-audit.lean','endpoint-audit.lean',
             'resolver.lean','junction.log','junction-exit.txt']:
    add(OUT/name)
for name in ['source-full-audit.lean','endpoint-audit.lean','resolver.lean']:
    add(PROJECT/name)
files=sorted(bindings.values(),key=lambda r:r['root_relative'])
verify(files)
dump(OUT/'source-manifest.json',{'role':'native author only','source_sha256':sha(SOURCE),'files':files})
write(OUT/'SHA256SUMS.txt',''.join(r['sha256']+'  '+r['root_relative']+'\n' for r in files))
dump(OUT/'author-audit.json',{
    'verdict':'PASS','stage':'native author only; independent review and platform pending',
    'checked_at':__import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat(),
    'source_sha256':sha(SOURCE),'parent_author_sha256':AUTHOR_SHA,
    'checks':[{'name':n,'pass':b} for n,b in checks],
    'counts':{'actual_successful_invocations':6,'actual_successful_Lean_calls':5,'runtime_invocations':1,
        'retained_failed_endpoint_Lean_calls':2,'actual_source_theorems':15,
        'complete_endpoint_type_kernel_comparisons':6,'closed_boundary_and_endpoint_proofs':10,
        'standard_three_only_records':25,'actual_module_resolutions':17,'reused_parent_objects_not_fresh':16},
    'stable_files':files,'source_full_types':source_records,'whole_endpoint_types':whole_types,
    'independent_review':False,'all_handles_terminal':True,'source_proof_scripts_changed':False,
    'retained_failures':failed,
    'findings':[{'severity':'informational','topic':'controls','detail':
        'The first endpoint control lacked ParameterShift namespace; the second retained an overly broad n=1 simplification timeout and a Rat arithmetic mismatch. Exact namespace and restricted arithmetic rewrites fixed the third attempt; all failed source/log/exit bytes remain immutable.'},
        {'severity':'informational','topic':'scope','detail':
        'All n>=1 actual chosen connection numerator transport and actual Q(2)=0 are proved. Local coefficient, rho/B, Gamma matrix and HasSum parameter transport, integral height, J and irrationality remain separate obligations.'}],
    'platform_acceptance_claimed':False,'actual_five_output_transport_proved':False,
    'independent_or_Root_proof_objects_borrowed':False})
report=load(OUT/'author-audit.json');verify(report['stable_files']);gate()
print('Native Numerators author PASS:',len(checks),'checks,',len(files),'bindings; five actual successful Lean calls plus runtime; two retained control failures')
print('Report SHA256',sha(OUT/'author-audit.json'))
