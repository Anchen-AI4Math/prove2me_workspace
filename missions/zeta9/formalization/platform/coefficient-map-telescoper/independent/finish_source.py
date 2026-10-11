from run_step import *
verify()
old=load(OUT/'retained-source-attempt-01-dependency-order/fresh-source-compile-receipt.json')
assert len(old['rows'])==17 and [x['exit_code'] for x in old['rows']]==[0]*16+[1]
for r in old['rows']:
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 for key in ['log','exit_file','wrapper']:
  assert sha(OUT/r[key])==r[key+'_sha256']
 if r['output_sha256']:assert sha(TASK/r['output_task_relative'])==r['output_sha256']
order=['HarmonicStability','CoefficientMapReflection','CoefficientMapFiniteSum','CoefficientMapSummation','CoefficientMapAggregate']
for short in order:
 rel='Definitions/Def_ZetaNine_'+short+'.lean';run('topological pure Def '+short,PROJECT/rel,P,P/(rel.removesuffix('.lean')+'.olean'))
run('fresh native Aggregate alias',PROJECT/'NativeValueComparisonDefinition.lean',N,N/'NativeValueComparisonDefinition.olean')
run('fresh native Aggregate kernel full values six plus nine rfl',OUT/'agg-native-values.lean',N)
run('fresh staged Aggregate alias',PROJECT/'StagedValueComparisonDefinition.lean',P,P/'StagedValueComparisonDefinition.olean')
run('fresh staged Aggregate kernel full values six plus nine rfl',OUT/'agg-staged-values.lean',P)
extra=load(OUT/'review-compile-receipt.json')['rows'];assert len(extra)==9 and all(r['exit_code']==0 for r in extra)
dump(OUT/'fresh-source-compile-receipt.json',dict(old,complete=True,retained_failed_steps=['s17'],successful_old_steps_hash_guarded_reused=True,
 supplemental_receipt='review-compile-receipt.json',supplemental_step_labels=[r['label'] for r in extra],successful_Lean_invocations=25,failed_dependency_scheduler_invocations=1))
print('Fresh source and pure dependencies complete:25 actual successes +1 retained import-order failure; no borrowed objects',flush=True)
