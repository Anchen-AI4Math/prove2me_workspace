"""Read the unchanged mission targets and original main reduction; no mutations."""
from datetime import datetime,timezone
import json
from pathlib import Path
from platform import api

VER=Path(__file__).resolve().parent/'verification'
MAIN='a53b364e-57a0-4d2c-adc6-983a74218a4b'
BRIDGE='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
PROPOSAL='561f5d71-28d6-4027-81f0-3fa01d5d7409'
summary={'read_at_utc':datetime.now(timezone.utc).isoformat()}
for name,path in [('main','/theorems/'+MAIN),('bridge','/theorems/'+BRIDGE),
                  ('main-decompositions','/theorems/'+MAIN+'/decompositions'),
                  ('main-graph','/theorems/'+MAIN+'/graph'),
                  ('proposal','/mission-proposals/'+PROPOSAL)]:
    result=api('GET',path)
    (VER/('machine-current-'+name+'.json')).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    if name in ('main','bridge','proposal'):
        summary[name]={k:result[k] for k in ('id','theorem_name','name','status','campaign_id') if k in result}
(VER/'machine-remote-status.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary,ensure_ascii=True))
