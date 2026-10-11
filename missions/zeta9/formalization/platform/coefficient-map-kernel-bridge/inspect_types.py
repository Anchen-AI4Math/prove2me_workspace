from pathlib import Path
import json
p=Path(__file__).resolve().parent
rows=lambda f:[json.loads(l) for l in f.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
native={r['label']:r for r in rows(p/'types_original.log')};staged={r['label']:r for r in rows(p/'types_definition.log')}
assert len(staged)==65
exception={'ZetaNine.CoefficientMapAggregate.'+n for n in ['aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']};exception|={'ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv','ZetaNine.CoefficientMapKernelBridge.inverseMultiplier'}
print(json.dumps({'already_executed_original_types':len(native),'actual_genuine_Def_types':len(staged),'all65_types_equal':all(r['type']==native[n]['type'] for n,r in staged.items()),'pretty_value_differences':[n for n,r in staged.items() if r['value']!=native[n]['value']],'full_value_protocol_required_for_proof_bearing_Definitions':sorted(exception)}))