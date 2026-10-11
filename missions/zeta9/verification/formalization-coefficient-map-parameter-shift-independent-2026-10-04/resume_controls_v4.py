"""Explicit retry after n2 endpoint numeral normalization, retaining all earlier own failures."""
from run import *
verify();receipt=load(OUT/'actual-execution-receipt.json');assert receipt['source_phase_complete'] and len(receipt['rows'])==20
assert all(r['actual_exit']==0 for r in receipt['rows'][:17])
assert [(r['label'],r['actual_exit']) for r in receipt['rows'][17:]]==[('e18',1),('e19',1),('e20',1)]
for r in receipt['rows']:
 for key in ['log','exit_file']:assert sha(OUT/r[key])==r[key+'_sha256']
 if r['source_root_relative']:assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 if r['object_task_relative']:assert sha(TASK/r['object_task_relative'])==r['object_sha256']
original=(OUT/'independent-boundary-v3.lean').read_text(encoding='utf-8')
old='simpa using five_actual_connection_transports_exist_unique 2 (by decide) (4 : Fin 5)'
assert original.count(old)==1
new=original.replace(old,'simpa [show (2 : Rat) + 1 = 3 by norm_num] using five_actual_connection_transports_exist_unique 2 (by decide) (4 : Fin 5)')
write(OUT/'independent-boundary-v4.lean',new);write(PROJECT/'independent-boundary-v4.lean',new)
dump(OUT/'boundary-retry-v4-annotation.json',{'status':'EXPLICIT_RETRY_AFTER_THREE_ACTUAL_FAILED_RUNS','failed_steps':['e18','e19','e20'],
 'third_failure':'Last n2 specialization simpa did not normalize rational 2+1 to3;26/27 printed closed records, entire run excluded',
 'changes_since_v3':'Only last specialization proof adds explicit norm_num equality Rat 2+1=3; all statement types and27 numerical controls unchanged',
 'source_or_author_proofs_modified':False,'cache_not_reset_or_borrowed':True,'controls_sha256':sha(OUT/'independent-boundary-v4.lean')})
dump(OUT/'retained-utf8-reporting-failure-01.json',{'role':'pure Python read-only failed-log reporting','actual_exit':1,'error':'UnicodeEncodeError: gbk could not encode exists glyph','Lean_invocations':0,'failed_log_or_source_bytes_modified':False,'excluded_from_success_counts':True,'repaired_by':'sys.stdout.reconfigure encoding utf-8; subsequent read-only reporting actual0'})
run('actual own independent-boundary-v4.lean',['lake','env','lean',str(PROJECT/'independent-boundary-v4.lean')],PROJECT/'independent-boundary-v4.lean')
for n in ['author-type-audit.lean','kernel-types.lean']:
 run('actual own '+n,['lake','env','lean',str(PROJECT/n)],PROJECT/n)
run('actual own fourteen module resolver',['lake','env','lean','--run',str(PROJECT/'resolver.lean')],PROJECT/'resolver.lean')
r=load(OUT/'actual-execution-receipt.json');r['controls_phase_complete']=True;r['status']='ALL_REQUESTED_EXECUTIONS_FINISHED';r['retained_failed_steps_excluded']=['e18','e19','e20'];dump(OUT/'actual-execution-receipt.json',r)
