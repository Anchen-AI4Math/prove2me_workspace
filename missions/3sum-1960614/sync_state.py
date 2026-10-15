"""Read this proposal, then its published targets and actual graphs. No platform writes."""
import json
from pathlib import Path
from platform import api, save

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
state=json.loads((HERE/'proposal-state.json').read_text(encoding='utf-8'))
proposal=api('GET','/mission-proposals/'+state['proposal_id'])
save('proposal-current.json',proposal)
print('Proposal:',proposal['id'],proposal['status'],flush=True)
targets=[]
for item in proposal['items']:
    name=item.get('theorem_name') or item.get('name') or ''
    tid=item.get('theorem_id') or item.get('published_theorem_id')
    if not tid or not name.startswith('ThreeSum1960614.'):
        continue
    theorem=api('GET','/theorems/'+tid)
    key=name.replace('.','_')
    save(key+'-current.json',theorem)
    save(key+'-graph.json',api('GET','/theorems/'+tid+'/graph'))
    save(key+'-decompositions.json',api('GET','/theorems/'+tid+'/decompositions'))
    if item.get('formal_statement'):
        (ROOT/'Theorems'/('Thm_'+key+'.lean')).write_text(
            item.get('preamble','')+'\n\n'+item['formal_statement']+'\n',encoding='utf-8')
    targets.append({'name':name,'theorem_id':tid,'status':theorem.get('status')})
    print(name,theorem.get('status'),tid,flush=True)
save('published-targets.json',targets)
if not targets:
    print('New targets are not yet published; planned edges are not remote graph evidence.',flush=True)
