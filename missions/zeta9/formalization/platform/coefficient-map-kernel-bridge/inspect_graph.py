from pathlib import Path
import json
p=Path(__file__).resolve().parent
gs=[json.loads(l) for l in (p/'decl_graph.jsonl').read_text().splitlines() if l.startswith('{')]
by={g['name']:g for g in gs};seen=set();q=['ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective']
while q:
 n=q.pop()
 if n in seen:continue
 seen.add(n);q.extend(by[n]['typeDeps']+by[n]['valueDeps'])
print(json.dumps({'actual_graph_records':len(gs),'actual_defs':sum(g['kind']=='def' and g['startLine']>0 for g in gs),'true_bijection_proof_closure':sum(by[n]['kind']=='theorem' and by[n]['startLine']>0 for n in seen),'cycle_through_Equiv_inverse_prescribed':any('ZetaNine.CoefficientMapKernelBridge.'+n in seen for n in ['actualAggregateEquiv','inverseMultiplier','prescribedL']),'control_source_roots':{m:sum(g['module']==m and g['startLine']>0 for g in gs) for m in ['NativeKernelAuthorControl','NativeKernelIndependentControl']}}))
compile((p/'audit_and_freeze.py').read_text(), 'author-gate','exec')
