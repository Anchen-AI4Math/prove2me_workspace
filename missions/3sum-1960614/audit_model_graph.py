"""Read back real accepted model proofs and child/submission/root graph paths."""
from datetime import datetime,timezone
import json
from pathlib import Path
from platform import api
from machine_graph_paths import graph_endpoint

VER=Path(__file__).resolve().parent/'verification'
manifest=json.loads((VER/'model-platform-manifest.json').read_text(encoding='utf-8'))
state_path=VER/'model-platform-publish.json'
state=json.loads(state_path.read_text(encoding='utf-8'))
reuse=json.loads((VER/'model-upload-plan.json').read_text(encoding='utf-8'))['reusable_accepted_nodes']
assert state.get('all_proofs_accepted'), 'Publication has not finished'
paths=[]
theorems=[]
for record in manifest['theorems']:
    item=state['items'][record['name']]
    verdict=api('GET','/verify?submission_id='+item['submission_id'])
    assert verdict['status']=='ACCEPTED',(record['name'],verdict['status'])
    current=api('GET','/theorems/'+item['theorem_id'])
    assert current['status']=='Proved',(record['name'],current['status'])
    graph=api('GET',graph_endpoint(item['theorem_id']))
    (VER/(record['name'].replace('.','_')+'-model-graph.json')).write_text(json.dumps(graph,indent=2)+'\n',encoding='utf-8')
    edges={(e['source'],e['target'],e['kind']) for e in graph['edges']}
    sketch='sketch-'+item['submission_id']
    for child in record['children']:
        child_id=(reuse[child]['theorem_id'] if child in reuse else state['items'][child]['theorem_id'])
        assert (child_id,sketch,'sketch') in edges,(child,sketch)
        assert (sketch,item['theorem_id'],'sketch') in edges
        paths.append({'child_name':child,'child':child_id,
                      'submission_id':item['submission_id'],'parent':item['theorem_id']})
    theorems.append({'source_name':record['name'],'platform_name':current['theorem_name'],
                     'theorem_id':item['theorem_id'],'status':current['status'],
                     'submission_id':item['submission_id']})
main=api('GET','/theorems/a53b364e-57a0-4d2c-adc6-983a74218a4b')
result={'read_at_utc':datetime.now(timezone.utc).isoformat(),
        'model_branch_complete':True,'proved_theorems':theorems,'verified_paths':paths,
        'independent_root':'9319378a-d6f7-45f7-b66b-35f91d017f2e',
        'main_goal_status':main['status'],'full_machine_graph_complete':False}
(VER/'model-graph-check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
state['actual_edge_audit_complete']=True
state_path.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Verified',len(theorems),'Proved model nodes and',len(paths),'actual dependency paths.')
print('Full machine graph remains pending; main status:',main['status'])
