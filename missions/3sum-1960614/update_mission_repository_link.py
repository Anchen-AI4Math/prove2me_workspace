"""Add the user-requested source link to the live mission description only."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import sys
from platform import api

VER=Path(__file__).resolve().parent/'verification'
MISSION='01a7fb00-e5c3-4a42-a3c2-2cbf04330ffc'
source=json.loads((VER/'bigospeedrun-submission.json').read_text(encoding='utf-8'))
repo=source['repo_url'];commit=source['commit']
assert repo=='https://github.com/Anchen0823/three-sum-1960614'
assert commit=='8c25c0325de5be4286413f39ca0c9278aad33f52'
def read_mission():
    offset=0
    while True:
        page=api('GET',f'/missions?limit=100&offset={offset}')
        matches=[m for m in page['missions'] if m['id']==MISSION]
        assert len(matches)<=1
        if matches:return matches[0]
        offset+=len(page['missions'])
        if not page['missions'] or offset>=page['total']:raise RuntimeError('Live mission not found')

before=read_mission()
(VER/'mission-before-repository-link.json').write_text(json.dumps(before,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
description=before.get('description') or ''
addition=(f'Source code and complete Lean formalization: [GitHub repository]({repo}). '
          f'Fixed source revision: [`{commit[:12]}`]({repo}/tree/{commit}).')
if repo in description and commit in description:
    desired=description
else:
    desired=description.rstrip()+'\n\n'+addition
intent={'requested_at_utc':datetime.now(timezone.utc).isoformat(),'mission_id':MISSION,
        'repo_url':repo,'commit':commit,'description_before_sha256':hashlib.sha256(description.encode()).hexdigest(),
        'payload':{'description':desired},'changes_other_fields':False}
(VER/'mission-repository-link-intent.json').write_text(json.dumps(intent,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'mission_id':MISSION,'name':before.get('name'),'added_text':addition,
                  'mutation_needed':desired!=description},ensure_ascii=True),flush=True)
if '--apply' not in sys.argv:
    print('Preview saved; no mutation performed.',flush=True)
    raise SystemExit(0)
if desired!=description:
    response=api('PATCH','/missions/'+MISSION,{'description':desired})
    (VER/'mission-repository-link-response.json').write_text(json.dumps(response,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
after=read_mission()
assert after['description']==desired,'Live description did not match the requested edit'
for key in ('name','mission_type','campaign_id','campaign'):
    assert before.get(key)==after.get(key),(key,'Unrequested metadata change')
assert before['main_theorem']['theorem_id']==after['main_theorem']['theorem_id']
assert repo in after['description'] and commit in after['description']
(VER/'mission-after-repository-link.json').write_text(json.dumps(after,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
receipt={k:v for k,v in intent.items() if k!='payload'}
receipt.update(verified_at_utc=datetime.now(timezone.utc).isoformat(),
               live_description_matches=True,description_after_sha256=hashlib.sha256(desired.encode()).hexdigest())
(VER/'mission-repository-link-validation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('Verified source repository and fixed revision in live mission description.',flush=True)
