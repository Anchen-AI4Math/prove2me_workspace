"""Read-only provenance checks before retrying an approval-rejected proof upload."""
import hashlib
import json
from pathlib import Path
import re
from platform import api, save

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
path=ROOT/'Solutions/Sol_ThreeSum1960614_uniform_entropy_bound.lean'
code=path.read_text(encoding='utf-8')
imports=re.findall(r'^import (\S+)',code,re.M)
assert imports==['Theorems.Thm_ThreeSum1960614_quartic_geometry',
                 'Theorems.Thm_ThreeSum1960614_tangent_log_bounds']
for forbidden in ['credentials','password','access_token','api_key','https://','http://',
                  'C:', 'D:', 'IO.', 'readFile', 'unsafe', 'axiom ', 'sorry','native_decide']:
    assert forbidden not in code,forbidden
assert 'Build completed successfully' in (HERE/'verification/uniform-build.txt').read_text(encoding='utf-8')
ids={'target':'bdba84e8-71fd-4c5d-88ce-382200fb1450',
     'quartic_geometry':'5eadf13c-7877-4753-a08c-3cf8eba024a4',
     'tangent_log_bounds':'eb511634-dac7-447e-9fa7-9177b75c8cba',
     'definition':'4f989e3e-71e0-4d7d-ad99-06cb29a25354'}
records={}
for key,tid in ids.items():
    data=api('GET','/theorems/'+tid)
    save('uniform-scope-'+key+'.json',data)
    records[key]={k:data.get(k) for k in ['theorem_id','theorem_name','status','visibility','is_private','private']}
    if key in ['quartic_geometry','tangent_log_bounds']:
        assert data['status']=='Proved'
target=json.loads((HERE/'verification/uniform-scope-target.json').read_text(encoding='utf-8'))
expected=target['formal_statement'].split(':= by',1)[0].replace(target['theorem_name'],'solution',1)
actual='theorem solution'+code.split('theorem solution',1)[1].split(':= by',1)[0]
assert re.sub(r'\s+','',expected)==re.sub(r'\s+','',actual)
proposal=api('GET','/mission-proposals/561f5d71-28d6-4027-81f0-3fa01d5d7409')
assert proposal['status'] in ['In review','Reviewed'] and proposal['visibility']=='public'
record={'source':path.relative_to(ROOT).as_posix(),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'source_kind':'Only a Lean real-variable mathematical proof with two platform imports; no file IO, credentials, private paths, or data files',
        'exact_published_target_match':True,'proposal_status':proposal['status'],
        'proposal_visibility':proposal['visibility'],'campaign_id':proposal['campaign_id'],
        'declarations':records,
        'human_authorization':'User requested this mission, its formalization and graph updates, and explicitly confirmed submitting the public proposal. This is the next proof of that exact published milestone.'}
save('uniform-public-scope-check.json',record)
print(json.dumps(record,ensure_ascii=False,indent=2))
