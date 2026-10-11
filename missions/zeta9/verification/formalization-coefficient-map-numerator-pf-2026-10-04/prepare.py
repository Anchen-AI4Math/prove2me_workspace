from run import *

assert not PROJECT.exists(), 'Fresh author project must be absent at enrollment'
audit=load(PS/'author-audit.json')
assert audit['verdict']=='PASS' and sha(PS/'author-audit.json')=='4a8dbe4ff74047e223054a4b14ca034ca73c900513ed205dcdd8ff91bd670642'
for row in audit['stable_files']:
    p=ROOT/row['root_relative']
    assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
PROJECT.mkdir(parents=True)
for name in ['lakefile.lean','lean-toolchain','lake-manifest.json']:
    write(PROJECT/name,(PARENT/name).read_bytes())
prep_sources=load(PS/'preparation-state.json')['sources']
parents=[];sources=[]
for row in prep_sources:
    rel=Path(row['project_relative'])
    original=ROOT/row['root_relative'];mirror=PARENT/rel
    assert original.read_bytes()==mirror.read_bytes()
    write(PROJECT/rel,original.read_bytes())
    sources.append({'root_relative':row['root_relative'],'project_relative':rel.as_posix(),
                    'sha256':sha(original),'bytes':original.stat().st_size})
    origin=PARENT/'b/lib/lean'/rel.with_suffix('.olean')
    dest=CACHE/rel.with_suffix('.olean')
    assert origin.exists()
    write(dest,origin.read_bytes())
    parents.append({'origin_task_relative':origin.relative_to(TASK).as_posix(),
                    'own_copy_task_relative':dest.relative_to(TASK).as_posix(),
                    'module':rel.with_suffix('').as_posix().replace('/','.'),
                    'sha256':sha(origin),'bytes':origin.stat().st_size,
                    'provenance':'Root-authorized reuse of PS author parent object; not independently/fresh compiled here'})
assert len(parents)==14
psobj=next(row for row in parents if row['module'].endswith('.CoefficientMapParameterShift'))
assert psobj['sha256']=='ed03ea9686d51af4b8419b6b9528e9812ba5d19a5eaa5e247a4da434909efb26'
for name,expected in [('CoefficientMapFormalTransportData','ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27'),
                      ('CoefficientMapNumeratorPartialFractions','929b1b89943e96c0cfe823d66698ad0465ec3081cb7cd3b603bbe8340c062787')]:
    src=TASK/'formalization'/(name+'.lean')
    assert sha(src)==expected
    write(OUT/('d0.lean' if name.endswith('Data') else 'p0.lean'),src.read_bytes())
    write(PROJECT/'missions/zeta9/formalization'/(name+'.lean'),src.read_bytes())
prep={'status':'ACTUAL_PARENT_REUSE_BOUND_OWN_DATA_PF_NOT_YET_COMPILED','Root_lane2_granted':True,
      'Lean_invocations_in_preparation':0,'project_initially_absent':True,
      'PS_author_audit_sha256':sha(PS/'author-audit.json'),'author_stable_files':audit['stable_files'],
      'reused_parent_objects':parents,'parent_source_copies':sources,
      'Mathlib_revision':'0df444a360eaa60ab8c11dca51a86af692955474','Lean_toolchain':'leanprover/lean4:v4.33.1',
      'Root_proofcache_or_independent_objects_borrowed':False,
      'Data_ft1_author_object_borrowed':False,'PS_parent_builds_claimed_fresh':False}
dump(OUT/'preparation.json',prep)
verify()
print('Prepared absent np1 project,14 exact reused PS parent objects, own Data/PF original snapshots.',flush=True)
