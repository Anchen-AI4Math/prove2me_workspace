"""Scoped Prove2Me reads and proposal writes; never confirms or launches a proposal."""
import importlib.util
import json
from pathlib import Path
import sys
import http.client
import time
import urllib.error
from urllib.parse import quote

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('p2m', ROOT / 'scripts/p2m_api.py')
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)

def api(method, path, data=None):
    for attempt in range(3):
        try:
            status, raw = p2m._request(method, path, token=p2m.get_token(), data=data)
        except (urllib.error.URLError,http.client.RemoteDisconnected,TimeoutError,ConnectionError):
            if method!='GET' or attempt==2:raise
            time.sleep(3*(attempt+1));continue
        if method=='GET' and status in (429,500,502,503,504) and attempt<2:
            time.sleep(3*(attempt+1));continue
        break
    if not 200 <= status < 300:
        raise RuntimeError(f'{method} {path}: HTTP {status}: {raw[:1200]}')
    return json.loads(raw) if raw else None

def save(name, data):
    out = HERE / 'verification'
    out.mkdir(exist_ok=True)
    (out / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def discover():
    campaign = api('GET', '/campaigns/3sum-exponent')
    save('campaign-current.json', campaign)
    proposals = api('GET', '/mission-proposals?limit=100&offset=0')
    save('proposals-before.json', proposals)
    print('campaign', campaign['id'], campaign['status'], campaign['env'])
    for query in ['ThreeSum1960614', 'ThreeSum.Parameters', 'LocalCover', '1.960614']:
        data = api('GET', '/theorems?q=' + quote(query) + '&limit=50')
        save('library-' + query.replace('.', '_') + '.json', data)
        print('search', query, str(data)[:1100])

def write_proposal():
    audit=json.loads((HERE/'verification/source-audit.json').read_text(encoding='utf-8'))
    assert audit['exit_code']==0 and not audit['hash_mismatches']
    build=(HERE/'verification/draft-build.txt').read_text(encoding='utf-8')
    assert 'Build completed successfully' in build, 'Draft Lean compilation must pass first'
    payloads=json.loads((HERE/'payloads.json').read_text(encoding='utf-8'))
    for item in payloads:
        key=item.get('theorem_name',item.get('definition_name')).split('.')[-1]
        item['readback']=(HERE/'blind'/f'{key}.readback.md').read_text(encoding='utf-8')
        item['readback_model']='GPT-6'
    campaign=api('GET','/campaigns/3sum-exponent')
    assert campaign['status']=='active'
    state=HERE/'proposal-state.json'
    name='Deterministic Integer 3SUM 1.960614: Quartic Switch and Complete Program Extension'
    if state.exists():
        proposal_id=json.loads(state.read_text(encoding='utf-8'))['proposal_id']
        proposal=api('GET','/mission-proposals/'+proposal_id)
    else:
        existing=api('GET','/mission-proposals?limit=100&offset=0')['proposals']
        matches=[p for p in existing if p['name']==name]
        if matches:
            assert len(matches)==1
            proposal=api('GET','/mission-proposals/'+matches[0]['id'])
        else:
            proposal=api('POST','/mission-proposals',{'campaign_id':campaign['id'],'name':name})
        proposal_id=proposal['id']
        state.write_text(json.dumps({'proposal_id':proposal_id,'campaign_id':campaign['id']},indent=2)+'\n',encoding='utf-8')
    assert proposal['status']=='Draft', 'Never edit a launched proposal'
    assert proposal.get('campaign_id')==campaign['id'] or proposal.get('campaign',{}).get('id')==campaign['id']
    save('proposal-before-write.json',proposal)
    goal_id=proposal['main_item_id']
    reference_ids=[x['id'] for x in proposal['items'] if x['kind']=='reference']
    ordered=[]
    for item in payloads:
        milestone={k:item[k] for k in ('milestone_title','milestone_description') if k in item}
        body={k:v for k,v in item.items() if k not in milestone}
        if item.get('theorem_name')=='ThreeSum1960614.threeSum_1960614':
            result=api('PATCH',f'/mission-proposals/{proposal_id}/items/{goal_id}',
                       {k:v for k,v in body.items() if k!='kind'})
        else:
            result=api('POST',f'/mission-proposals/{proposal_id}/items',body)
        item_id=result['id']
        ordered.append(item_id)
        if milestone:
            api('POST',f'/mission-proposals/{proposal_id}/milestones',{'item_id':item_id,**milestone})
        print('saved',item.get('theorem_name',item.get('definition_name')),flush=True)
    api('PATCH','/mission-proposals/'+proposal_id,{'name':name,
        'description':(HERE/'description.md').read_text(encoding='utf-8'),
        'main_item_id':goal_id,'item_order':reference_ids+ordered})
    after=api('GET','/mission-proposals/'+proposal_id)
    milestones=api('GET',f'/mission-proposals/{proposal_id}/milestones')
    save('proposal-after.json',after)
    save('milestones-after.json',milestones)
    assert after['status']=='Draft' and after['main_item_id']==goal_id
    assert after['item_order']==reference_ids+ordered
    for item_id,expected in zip(ordered,payloads):
        actual=next(x for x in after['items'] if x['id']==item_id)
        for key in ['formal_statement','preamble','definition','readback','natural_language_statement']:
            if key in expected:
                assert actual[key]==expected[key], (item_id,key)
        assert not actual.get('confirmed',False)
    print('READY https://prove2.me/my-missions/'+proposal_id,flush=True)

if __name__ == '__main__':
    write_proposal() if '--write-proposal' in sys.argv else discover()
