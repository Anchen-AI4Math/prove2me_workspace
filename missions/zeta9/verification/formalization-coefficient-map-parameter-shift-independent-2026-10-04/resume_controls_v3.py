"""Second explicit own-control retry: valid typed forall/arrow syntax, same frozen native cache."""
from run import *
verify();receipt=load(OUT/'actual-execution-receipt.json')
assert receipt['source_phase_complete'] and len(receipt['rows'])==19
assert all(r['actual_exit']==0 for r in receipt['rows'][:17])
assert [(r['label'],r['actual_exit']) for r in receipt['rows'][17:]]==[('e18',1),('e19',1)]
for r in receipt['rows']:
 for key in ['log','exit_file']:assert sha(OUT/r[key])==r[key+'_sha256']
 if r['source_root_relative']:assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 if r['object_task_relative']:assert sha(TASK/r['object_task_relative'])==r['object_sha256']
original=(OUT/'independent-boundary.lean').read_text(encoding='utf-8')
assert original.count('∀ k ≤ 2,')==1 and original.count('∀ k ≤ 3,')==1 and original.count('∀ k ≤ 4,')==2
new=original
for n in [2,3,4]:new=new.replace('∀ k ≤ '+str(n)+',','∀ k : Nat, k ≤ '+str(n)+' →')
write(OUT/'independent-boundary-v3.lean',new);write(PROJECT/'independent-boundary-v3.lean',new)
dump(OUT/'boundary-retry-v3-annotation.json',{'status':'EXPLICIT_RETRY_AFTER_TWO_ACTUAL_FAILED_RUNS',
 'failed_steps':['e18','e19'],'first_failure':'Four literal-bound indices inferred Rat',
 'second_failure':'Lean bounded-forall grammar rejects grouped typed binder immediately before <=',
 'old_controls_sha256':sha(OUT/'independent-boundary.lean'),'new_controls_sha256':sha(OUT/'independent-boundary-v3.lean'),
 'changes':'Exactly four literal-bound forall binders written forall k : Nat, k <= bound -> ...; all numerical values and remaining theorem/proof text identical.',
 'failed_runs_wholly_excluded':True,'author_source_unchanged':True,'cache_not_reset_or_borrowed':True})
run('actual own independent-boundary-v3.lean',['lake','env','lean',str(PROJECT/'independent-boundary-v3.lean')],PROJECT/'independent-boundary-v3.lean')
for n in ['author-type-audit.lean','kernel-types.lean']:
 run('actual own '+n,['lake','env','lean',str(PROJECT/n)],PROJECT/n)
run('actual own fourteen module resolver',['lake','env','lean','--run',str(PROJECT/'resolver.lean')],PROJECT/'resolver.lean')
r=load(OUT/'actual-execution-receipt.json');r['controls_phase_complete']=True;r['status']='ALL_REQUESTED_EXECUTIONS_FINISHED';r['retained_failed_steps_excluded']=['e18','e19'];dump(OUT/'actual-execution-receipt.json',r)
