"""Compare stable owner-list records with their individual status endpoints."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from platform import api
from machine_queue_reads import owner_status_reads

VER = Path(__file__).resolve().parent / 'verification'
state = json.loads((VER / 'machine-platform-publish.json').read_text(encoding='utf-8'))
proof = max((i for i in state['items'].values() if i.get('proof_status')=='ACCEPTED'),
            key=lambda i:i['verify_intent']['requested_at_utc'])
published = max((i for n,i in state['items'].items() if n.startswith('ThreeSum1960614_Machine_Bundle') and i.get('theorem_id')),
                key=lambda i:i['publish_intent']['requested_at_utc'])
job = {k:v for k,v in published.items() if k!='theorem_id'}
cached = owner_status_reads({'proof':proof,'job':job},include_accepted=True)
for path, record in cached.items():
    single = api('GET',path)
    for key in ('id','status','theorem_id','error_message'):
        assert single.get(key)==record.get(key),(path,key)
    if path.startswith('/publish-jobs/'):
        assert single['definitions']==record['definitions']
receipt = {'checked_at_utc':datetime.now(timezone.utc).isoformat(),
           'proof_submission_id':proof['submission_id'],'publish_job_id':job['job_id'],
           'ids_statuses_targets_errors_equal':True,'definition_source_bytes_equal':True,
           'matched_endpoint_count':len(cached)}
(VER/'queue-owner-list-validation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(receipt))
