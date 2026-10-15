"""Select a complete cached import closure for scope/cross-file regression.

This is an isolated compiler regression, not the main upload classification
and never a substitute for the remaining universal machine bridge.
"""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
base=json.loads((VER/'machine-upload-plan.json').read_text(encoding='utf-8'))
contexts={c['module']:c for c in json.loads((VER/'machine-scope-contexts.json').read_text(encoding='utf-8'))}
rows=[json.loads(s) for s in (VER/'machine-decl-graph.jsonl').read_text(encoding='utf-8').splitlines()]
by_name={r['name']:r for r in rows}
roots=['ThreeSum.Histograms.selected_pairMass_bound','ThreeSum.Bands.tripleOwner_injective',
       'ThreeSum.HashFamily.oneHot_four_independent','ThreeSum.HashFamily.trimmed_second_moment',
       'ThreeSum.Coloring.reduction_correct']
modules=set();pending=[by_name[n]['module'] for n in roots]
while pending:
    module=pending.pop()
    if module in modules:continue
    modules.add(module)
    for item in contexts[module]['imports']:
        pending.extend(i['name'] for i in item['identifiers'] if i['name'] in contexts)
for module in modules:
    receipt=VER/'sketch-oracles'/(module.replace('.','_')+'.receipt.json')
    assert receipt.exists() and json.loads(receipt.read_text(encoding='utf-8'))['exit_code']==0,module
result={**base,'roots':roots,'participating_modules':sorted(modules),
        'instance_roots':[r['name'] for r in rows if r['module'] in modules and r['isInstance']],
        'live_rows':[r for r in rows if r['module'] in modules],
        'regression_only':True,'regression_purpose':'Section variables, implicit universes, instances and real cross-file helper dependencies',
        'note':'Complete cached import closure for a local compiler regression; publication forbidden.'}
(VER/'scope-regression-upload-plan.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Prepared isolated scope regression:',len(roots),'roots in',len(modules),'fully extracted modules.')
