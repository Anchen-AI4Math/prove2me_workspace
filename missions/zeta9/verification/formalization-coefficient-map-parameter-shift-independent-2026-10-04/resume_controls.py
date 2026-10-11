"""Explicit same-cache retry of independent boundary after actual Nat/Rat binder failure."""
from run import *
verify();receipt=load(OUT/'actual-execution-receipt.json')
assert receipt['source_phase_complete'] and len(receipt['rows'])==18
assert all(r['actual_exit']==0 for r in receipt['rows'][:17])
failed=receipt['rows'][-1];assert failed['label']=='e18' and failed['actual_exit']==1 and failed['logical_step']=='actual own independent-boundary.lean'
assert sha(OUT/failed['log'])==failed['log_sha256'] and sha(PROJECT/'independent-boundary.lean')==failed['source_sha256']
original=(OUT/'independent-boundary.lean').read_text(encoding='utf-8')
assert original.count('∀ k ≤ 2,')==1 and original.count('∀ k ≤ 3,')==1 and original.count('∀ k ≤ 4,')==2
new=original
for n in [2,3,4]:new=new.replace('∀ k ≤ '+str(n)+',','∀ (k : Nat) ≤ '+str(n)+',')
write(OUT/'independent-boundary-v2.lean',new);write(PROJECT/'independent-boundary-v2.lean',new)
dump(OUT/'boundary-retry-annotation.json',{'status':'EXPLICIT_RETRY_AFTER_ACTUAL_FAILED_RUN','failed_actual_step':failed,
 'old_controls_sha256':sha(OUT/'independent-boundary.lean'),'new_controls_sha256':sha(OUT/'independent-boundary-v2.lean'),
 'changes':'Exactly four literal-bound forall binders explicitly annotated Nat; all numerical values and remaining theorem/proof text identical.',
 'original_actual_printed_records':27,'original_actual_invalid_sorryAx_records':4,'failed_run_wholly_excluded_from_success':True,
 'source_or_author_proofs_modified':False,'cache_not_reset_or_borrowed':True})
run('actual own independent-boundary-v2.lean',['lake','env','lean',str(PROJECT/'independent-boundary-v2.lean')],PROJECT/'independent-boundary-v2.lean')
for n in ['author-type-audit.lean','kernel-types.lean']:
 run('actual own '+n,['lake','env','lean',str(PROJECT/n)],PROJECT/n)
run('actual own fourteen module resolver',['lake','env','lean','--run',str(PROJECT/'resolver.lean')],PROJECT/'resolver.lean')
r=load(OUT/'actual-execution-receipt.json');r['controls_phase_complete']=True;r['status']='ALL_REQUESTED_EXECUTIONS_FINISHED';r['retained_failed_steps_excluded']=['e18'];dump(OUT/'actual-execution-receipt.json',r)
