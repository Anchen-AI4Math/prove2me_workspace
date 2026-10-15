"""Verify the existing exact-goal reduction before selecting upload roots."""
from datetime import datetime,timezone
import json
from pathlib import Path
from platform import api

VER=Path(__file__).resolve().parent/'verification'
MAIN='a53b364e-57a0-4d2c-adc6-983a74218a4b'
SUBMISSION='17448ceb-49aa-4f37-9e4e-107b286f0059'
CERTIFICATE='6f7c52c1-6e2d-4554-adb3-bf79b8ed51a9'
BRIDGE='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
current=api('GET','/theorems/'+MAIN)
verdict=api('GET','/verify?submission_id='+SUBMISSION)
graph=api('GET','/theorems/'+MAIN+'/graph')
assert current['theorem_name']=='ThreeSum1960614.threeSum_1960614'
assert verdict['theorem_id']==MAIN and verdict['status'] in ('SKETCH_ACCEPTED','ACCEPTED')
edges={(e['source'],e['target'],e['kind']) for e in graph['edges']}
sketch='sketch-'+SUBMISSION
for child in [CERTIFICATE,BRIDGE]:
    assert (child,sketch,'sketch') in edges
    assert (sketch,MAIN,'sketch') in edges
result={'checked_at_utc':datetime.now(timezone.utc).isoformat(),
        'main_theorem_id':MAIN,'main_name':current['theorem_name'],
        'main_status':current['status'],'reduction_submission_id':SUBMISSION,
        'reduction_status':verdict['status'],'parameter_certificate_id':CERTIFICATE,
        'complete_machine_bridge_id':BRIDGE,'actual_paths_verified':True,
        'remaining_source_upload_target':'ThreeSum1960614.costs_solve_3sum',
        'explanation':'The existing accepted exact-goal reduction uses the parameter certificate and universal machine bridge. Proving the bridge closes this same original main goal; the independent model root is already Proved.'}
(VER/'main-reduction-bridge-plan.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
(VER/'main-reduction-current-graph.json').write_text(json.dumps(graph,indent=2)+'\n',encoding='utf-8')
print('Verified exact main goal and both real reduction paths. Main status:',current['status'])
