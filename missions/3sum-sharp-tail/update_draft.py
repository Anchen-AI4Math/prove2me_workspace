"""Edit only the specified private staging draft; never confirm or launch."""
import json
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = 'https://prove2.me/api/v1'
PID = '7552d42d-7c8c-4f16-aead-ec41ac6cc8d5'
PREFIX = '/mission-proposals/' + PID
cred = json.loads((ROOT/'credentials.json').read_text(encoding='utf-8-sig'))

def api(method, path, body=None):
    data = None if body is None else json.dumps(body,ensure_ascii=False).encode('utf-8')
    req = urllib.request.Request(BASE+path, data=data, method=method,
        headers={'Authorization':'Bearer '+cred['access_token'],'Content-Type':'application/json'})
    with urllib.request.urlopen(req, timeout=90) as res:
        raw=res.read()
        return json.loads(raw) if raw else None

def save(name,data):
    (HERE/'verification'/name).write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')

if __name__ == '__main__':
    current = api('GET',PREFIX)
    assert current['status']=='Draft'
    before = json.loads((HERE/'verification/proposal-before.json').read_text(encoding='utf-8-sig'))
    assert current['main_item_id']==before['main_item_id']
    readbacks=json.loads((HERE/'readbacks.json').read_text(encoding='utf-8'))
    items=json.loads((HERE/'items.json').read_text(encoding='utf-8'))
    ids=[before['items'][0]['id']]
    uploaded=[]
    for item in items:
        item=dict(item)
        key=item.get('definition_name',item.get('theorem_name'))
        item['readback']=readbacks[key]
        item['readback_model']='gpt-6'
        mt=item.pop('milestone_title',None)
        md=item.pop('milestone_description',None)
        if key=='ThreeSumSharpTail.threeSum_1999017':
            result=api('PATCH',PREFIX+'/items/'+before['main_item_id'],{k:v for k,v in item.items() if k!='kind'})
        else:
            result=api('POST',PREFIX+'/items',item)
        save('last-item-response.json',result)
        iid=result['id']
        ids.append(iid)
        uploaded.append({'id':iid,'key':key})
        save('uploaded-items.json',uploaded)
        if mt:
            api('POST',PREFIX+'/milestones',{'item_id':iid,'milestone_title':mt,'milestone_description':md})
        print('Saved '+key,flush=True)
    body={'name':'Deterministic Integer 3SUM in O(n^1.999017): Sharp Binomial-Tail Analysis',
          'description':(HERE/'description.md').read_text(encoding='utf-8'),
          'campaign_id':'52073c33-5f7d-479b-b2db-238c6e280c9a',
          'main_item_id':before['main_item_id'],'item_order':ids}
    api('PATCH',PREFIX,body)
    after=api('GET',PREFIX)
    milestones=api('GET',PREFIX+'/milestones')
    save('proposal-after.json',after)
    save('milestones-after.json',milestones)
    assert after['status']=='Draft'
    assert after['campaign_id']==body['campaign_id']
    assert after['description']==body['description']
    assert after['item_order']==ids
    assert len(after['items'])==8
    assert '{{value}}' not in json.dumps(after['items'])
    for spec in items:
        key=spec.get('definition_name',spec.get('theorem_name'))
        match=next(x for x in after['items'] if x['id']==next(u['id'] for u in uploaded if u['key']==key))
        for field in ('formal_statement','preamble','natural_language_statement','source'):
            if field in spec: assert match[field]==spec[field], (key,field)
        assert match['readback']==readbacks[key]
    print('Read-back verification passed: Draft, campaign 3sum-exponent, 8 items; goal 1.999017.')
