"""Retain trailing-parenthesis parser failure and complete actual kernel/resolver controls."""
from run import *
verify();receipt=load(OUT/'actual-execution-receipt.json');assert len(receipt['rows'])==23
assert [(r['label'],r['actual_exit']) for r in receipt['rows'] if r['actual_exit']!=0]==[('e18',1),('e19',1),('e20',1),('e23',1)]
for r in receipt['rows']:
 for key in ['log','exit_file']:assert sha(OUT/r[key])==r[key+'_sha256']
 if r['source_root_relative']:assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 if r['object_task_relative']:assert sha(TASK/r['object_task_relative'])==r['object_sha256']
original=(OUT/'kernel-types.lean').read_text(encoding='utf-8');assert original.count(']).compress)\n')==1
new=original.replace(']).compress)\n',']).compress\n')
write(OUT/'kernel-types-v2.lean',new);write(PROJECT/'kernel-types-v2.lean',new)
dump(OUT/'kernel-retry-annotation.json',{'status':'EXPLICIT_RETRY_AFTER_TRAILING_PARENTHESIS_ACTUAL_FAILURE','failed_step':'e23','actual_exit':1,
 'changes':'Remove one trailing unmatched parenthesis only; whole expected program and fifteen original type kernel comparisons unchanged',
 'failed_actual_output_records':32,'failed_run_wholly_excluded':True,'author_source_unchanged':True,'native_cache_objects_not_reset_or_borrowed':True})
run('actual own kernel-types-v2.lean',['lake','env','lean',str(PROJECT/'kernel-types-v2.lean')],PROJECT/'kernel-types-v2.lean')
run('actual own fourteen module resolver',['lake','env','lean','--run',str(PROJECT/'resolver.lean')],PROJECT/'resolver.lean')
r=load(OUT/'actual-execution-receipt.json');r['controls_phase_complete']=True;r['status']='ALL_REQUESTED_EXECUTIONS_FINISHED';r['retained_failed_steps_excluded']=['e18','e19','e20','e23'];dump(OUT/'actual-execution-receipt.json',r)
