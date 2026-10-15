"""Read current proof verdicts and actual dependency graphs for this mission."""
import json
from pathlib import Path
from platform import api, save

HERE=Path(__file__).resolve().parent
records={}
for key,filename in [('local_cover_bounds','local-cover-submit.txt'),('threeSum_1960614','main-reduction-submit.txt'),
                     ('quartic_switch_bounds','quartic-submit.txt'),('uniform_entropy_bound','uniform-submit.txt'),
                     ('integer_schedule','integer-submit.txt'),
                     ('quartic_parameter_certificate','parameter-certificate-submit.txt')]:
    if not (HERE/'verification'/filename).exists():
        continue
    data=json.loads((HERE/'verification'/filename).read_text(encoding='utf-8').split('\n',1)[1])
    records[key]={'submission_id':data['submission_id']}
for key,record in json.loads((HERE/'verification/support-nodes.json').read_text(encoding='utf-8')).items():
    if record.get('submission_id'):
        records[key]={'submission_id':record['submission_id']}
for key,record in records.items():
    verdict=api('GET','/verify?submission_id='+record['submission_id'])
    save(key+'-verdict.json',verdict)
    record.update(theorem_id=verdict['theorem_id'],status=verdict['status'])
    save('ThreeSum1960614_'+key+'-current.json',api('GET','/theorems/'+record['theorem_id']))
    save('ThreeSum1960614_'+key+'-graph.json',api('GET','/theorems/'+record['theorem_id']+'/graph'))
    save('ThreeSum1960614_'+key+'-decompositions.json',api('GET','/theorems/'+record['theorem_id']+'/decompositions'))
    print(key,verdict['status'],record['submission_id'],flush=True)
save('proof-status.json',records)
