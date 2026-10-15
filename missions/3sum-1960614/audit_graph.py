"""Audit current actual paths without claiming the complete mission is solved."""
from datetime import datetime, timezone
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
VERIFY=HERE/'verification'
def read(name):
    return json.loads((VERIFY/name).read_text(encoding='utf-8-sig'))

proofs=read('proof-status.json')
main=proofs['threeSum_1960614']
assert main['status'] in ('SKETCH_ACCEPTED','ACCEPTED')
graph=read('ThreeSum1960614_threeSum_1960614-graph.json')
required=[(graph,'6f7c52c1-6e2d-4554-adb3-bf79b8ed51a9',main['submission_id'],main['theorem_id']),
          (graph,'7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6',main['submission_id'],main['theorem_id'])]
dependencies={
    'quartic_switch_bounds':['quartic_geometry','log_coefficients'],
    'tangent_log_bounds':['log_coefficients'],
    'uniform_entropy_bound':['quartic_geometry','tangent_log_bounds'],
    'encoding_parameter_bounds':['high_precision_logs'],
    'initial_entropy_bound':['high_precision_logs'],
    'quartic_parameter_certificate':['encoding_parameter_bounds','initial_entropy_bound'],
    'executable_scale_limits':['executable_scale_rounding'],
    'integer_schedule':['cleared_switch_equivalence','quartic_switch_bounds','uniform_entropy_bound']}
for parent,children in dependencies.items():
    if parent not in proofs or proofs[parent]['status'] not in ('ACCEPTED','SKETCH_ACCEPTED'):
        continue
    parent_graph=read('ThreeSum1960614_'+parent+'-graph.json')
    required.extend((parent_graph,proofs[child]['theorem_id'],proofs[parent]['submission_id'],
                     proofs[parent]['theorem_id']) for child in children)
paths=[]
for graph,child,submission,parent in required:
    edges={(e['source'],e['target'],e['kind']) for e in graph['edges']}
    sketch='sketch-'+submission
    assert (child,sketch,'sketch') in edges,(child,sketch)
    assert (sketch,parent,'sketch') in edges,(sketch,parent)
    paths.append({'child':child,'submission_id':submission,'parent':parent})
for key in [k for k,v in proofs.items() if v['status']=='ACCEPTED']:
    theorem=read('ThreeSum1960614_'+key+'-current.json')
    assert theorem['status']=='Proved'
main_status=read('ThreeSum1960614_threeSum_1960614-current.json')['status']
result={'read_at_utc':datetime.now(timezone.utc).isoformat(),'verified_paths':paths,
        'proofs':proofs,'proved_theorem_count':sum(v['status']=='ACCEPTED' for v in proofs.values()),
        'main_goal_status':main_status,'main_goal_proved':main_status=='Proved','remote_graph_complete':False,
        'remaining_connection':'analytic/scheduling milestones through the complete expansion-232 executable runtime bridge',
        'independent_model_root':'ThreeSum1960614.fixed_model_lower_bound'}
(VERIFY/'graph-check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Verified',len(paths),'actual child -> submission -> parent paths. Main remains Open.')
