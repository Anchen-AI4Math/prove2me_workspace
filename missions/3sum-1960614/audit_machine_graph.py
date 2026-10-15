"""Audit live accepted proofs and real child -> submission -> parent paths.

The immutable original main reduction remains the final link. Never infer
edges from imports, metadata, milestone order, or a Proved status alone.
"""
from datetime import datetime,timezone
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
from platform import api
from machine_graph_paths import actual_child_path,graph_endpoint
from machine_queue_reads import owner_status_reads

VER=Path(__file__).resolve().parent/'verification'
MAIN='a53b364e-57a0-4d2c-adc6-983a74218a4b'
BRIDGE='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
CERTIFICATE='6f7c52c1-6e2d-4554-adb3-bf79b8ed51a9'
ORIGINAL_SUBMISSION='17448ceb-49aa-4f37-9e4e-107b286f0059'
read=lambda path:json.loads(path.read_text(encoding='utf-8'))
manifest_path=VER/'machine-platform-manifest.json'
manifest=read(manifest_path)
state_path=VER/'machine-platform-publish.json'
state=read(state_path)
assert state['all_proofs_accepted']
if state.get('validation_mode')=='server-first':
    authorization=read(VER/'machine-server-first-authorization.json')
    assert authorization['user_authorized_server_compilation']
    assert authorization['manifest_sha256']==state['manifest_sha256']
else:
    assert manifest['validation_complete']
assert hashlib.sha256(manifest_path.read_bytes()).hexdigest()==state['manifest_sha256']
reuse={r['name']:r for r in manifest['reused_theorems']}
required={r['name']:state['items'][r['name']]['theorem_id'] for r in manifest['theorems']}
required.update({name:r['theorem_id'] for name,r in reuse.items()})
assert required['ThreeSum1960614.costs_solve_3sum']==BRIDGE
edges=set()
nodes={}
snapshots=[]
decomposition_edges=[]

# Reuse raw server responses captured in this same publication run. A long
# sequential audit already spans a time interval; preserve that interval and
# exact bytes instead of downloading identical accepted graph data twice.
# Acceptance verdicts, original root/reduction and reused identities below
# are still read afresh on every audit execution.
if '--reuse-live-snapshots-after' in sys.argv:
    threshold=datetime.fromisoformat(sys.argv[sys.argv.index('--reuse-live-snapshots-after')+1]).timestamp()
    candidates=list((VER/'machine-frontier-readback').glob('*.json'))+list(VER.glob('*-machine-live-graph.json'))
    candidates=sorted((p for p in candidates if p.stat().st_mtime>=threshold),key=lambda p:p.stat().st_mtime)
    for path in candidates:
        raw=path.read_bytes()
        graph=json.loads(raw)
        if not isinstance(graph,dict) or not all(k in graph for k in ('root_id','nodes','edges')):
            continue
        edges.update((e['source'],e['target'],e['kind']) for e in graph['edges'])
        for node in graph['nodes']:
            if node.get('node_type')=='theorem':nodes[node['theorem_id']]=node
        snapshots.append({'root_id':graph['root_id'],'file':str(path.relative_to(VER)),
            'sha256':hashlib.sha256(raw).hexdigest(),'reused_same_run_response':True,
            'snapshot_saved_at_utc':datetime.fromtimestamp(path.stat().st_mtime,timezone.utc).isoformat()})
    print('Loaded',len(snapshots),'raw same-run live graph responses with exact hashes.',flush=True)

def get_graph(theorem_id,label,depth=2,direction='children'):
    graph=api('GET',graph_endpoint(theorem_id,depth,direction))
    assert graph['root_id']==theorem_id
    path=VER/(label+'-machine-live-graph.json')
    path.write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    snapshots.append({'root_id':theorem_id,'file':path.name,'depth':depth,'direction':direction,
                      'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                      'reused_same_run_response':False,
                      'snapshot_saved_at_utc':datetime.now(timezone.utc).isoformat()})
    edges.update((e['source'],e['target'],e['kind']) for e in graph['edges'])
    for node in graph['nodes']:
        if node.get('node_type')=='theorem':nodes[node['theorem_id']]=node
    return graph

def recover_decomposition_edge(name,child,child_id,item):
    """Read a persisted proof edge omitted by both bounded graph views.

    This is authoritative server decomposition data, never an inferred import
    or planned dependency. Keep its distinct provenance in the audit receipt.
    """
    response=api('GET','/theorems/'+item['theorem_id']+'/decompositions')
    path=VER/(name.replace('.','_')+'-edge-decompositions.json')
    path.write_text(json.dumps(response,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    decomposition=next(r for r in response['decompositions'] if r['submission_id']==item['submission_id'])
    assert decomposition.get('deprecated_at') is None
    match=next(r for r in decomposition['children'] if r.get('theorem_id')==child_id)
    assert match['theorem_name']==child and match['status']=='Proved'
    assert match.get('deprecated_at') is None
    sketch='sketch-'+item['submission_id']
    assert (sketch,item['theorem_id'],'sketch') in edges
    edge=(child_id,sketch,'sketch')
    assert edge not in edges
    edges.add(edge)
    decomposition_edges.append({'child_name':child,'parent_name':name,
        'child_id':child_id,'parent_id':item['theorem_id'],'submission_id':item['submission_id'],
        'source':'live nondeprecated decomposition child record',
        'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'bounded_graph_views_omit_edge':True})

get_graph(MAIN,'main-root')
paths=[]
proofs=[]
verdicts=owner_status_reads({r['name']:state['items'][r['name']] for r in manifest['theorems']},include_accepted=True)
for position,record in enumerate(manifest['theorems'],1):
    name=record['name'];item=state['items'][name]
    if state.get('validation_mode')=='server-first':
        assert item['verified_solution_sha256']==record['solution_sha256']
    verdict=verdicts['/verify?submission_id='+item['submission_id']]
    assert verdict['status']=='ACCEPTED',(name,verdict['status'])
    sketch='sketch-'+item['submission_id']
    expected=[(required[child],sketch,'sketch') for child in record['children']]
    if expected:expected.append((sketch,item['theorem_id'],'sketch'))
    if any(edge not in edges for edge in expected) or item['theorem_id'] not in nodes:
        get_graph(item['theorem_id'],name.replace('.','_'))
    current=nodes[item['theorem_id']]
    assert current['status']=='Proved',(name,current['status'])
    assert current['theorem_name']==name
    for child in record['children']:
        child_id=required[child]
        try:
            actual=actual_child_path(edges,child_id,item['submission_id'],item['theorem_id'])
        except AssertionError:
            # A child-focused response can omit theorem children after a long
            # prefix of definition imports, even with has_more_children=false.
            # The deployed parent view exposes the actual missing sketch edge.
            get_graph(child_id,child.replace('.','_')+'-parents',2,'parents')
            try:
                actual=actual_child_path(edges,child_id,item['submission_id'],item['theorem_id'])
            except AssertionError:
                get_graph(item['theorem_id'],name.replace('.','_')+'-expanded',4)
                try:
                    actual=actual_child_path(edges,child_id,item['submission_id'],item['theorem_id'])
                except AssertionError:
                    recover_decomposition_edge(name,child,child_id,item)
                    actual=actual_child_path(edges,child_id,item['submission_id'],item['theorem_id'])
        if child_id not in nodes:
            get_graph(child_id,child.replace('.','_'))
        assert nodes[child_id]['status']=='Proved',(child,nodes[child_id]['status'])
        paths.append({'child_name':child,'child':child_id,'parent_name':name,
                      'parent':item['theorem_id'],'submission_id':item['submission_id'],**actual})
    proofs.append({'name':name,'theorem_id':item['theorem_id'],
                   'submission_id':item['submission_id'],'status':'ACCEPTED'})
    if position%25==0:print('Audited',position,'/',len(manifest['theorems']),'live proofs',flush=True)

# Reused theorems may have different original proof decompositions. Check
# their actual status and identity, never native-source child expectations.
def fresh_reused_identity(pair):
    name,record=pair
    current=api('GET','/theorems/'+record['theorem_id'])
    assert current['status']=='Proved' and current['theorem_name']==name
    return {'name':name,'theorem_id':record['theorem_id'],'status':current['status']}
with ThreadPoolExecutor(max_workers=4) as pool:
    reused_identities=list(pool.map(fresh_reused_identity,reuse.items()))

original=api('GET','/verify?submission_id='+ORIGINAL_SUBMISSION)
assert original['status']=='ACCEPTED',('Original final reduction is not closed',original['status'])
decompositions=api('GET','/theorems/'+MAIN+'/decompositions')
(VER/'main-root-machine-live-decompositions.json').write_text(json.dumps(decompositions,indent=2)+'\n',encoding='utf-8')
decomposition=next(r for r in decompositions['decompositions'] if r['submission_id']==ORIGINAL_SUBMISSION)
assert decomposition.get('deprecated_at') is None
assert {r['theorem_id'] for r in decomposition['children']}=={CERTIFICATE,BRIDGE}
get_graph(MAIN,'main-root-final')
main=api('GET','/theorems/'+MAIN)
assert main['status']=='Proved' and main['theorem_name']=='ThreeSum1960614.threeSum_1960614'
original_sketch='sketch-'+ORIGINAL_SUBMISSION
for child in (CERTIFICATE,BRIDGE):
    assert (child,original_sketch,'sketch') in edges
assert (original_sketch,MAIN,'sketch') in edges

# Verify every published main-tree node connects to the existing main root
# through live sketch edges. Structural definition imports do not count.
parents={}
for source,target,kind in edges:
    if kind=='sketch':parents.setdefault(source,set()).add(target)
def reaches_main(start):
    pending=[start];seen=set()
    while pending:
        node=pending.pop()
        if node==MAIN:return True
        if node in seen:continue
        seen.add(node);pending.extend(parents.get(node,()))
    return False
assert all(reaches_main(theorem_id) for theorem_id in required.values()),(
    'Disconnected main-tree nodes',[name for name,theorem_id in required.items() if not reaches_main(theorem_id)])
receipt={'read_at_utc':datetime.now(timezone.utc).isoformat(),'manifest_sha256':state['manifest_sha256'],
         'main_goal_status':'Proved','full_machine_graph_complete':True,
         'new_proved_node_count':len(proofs),'reused_proved_node_count':len(reuse),
         'original_main_reduction':ORIGINAL_SUBMISSION,'original_main_children':[CERTIFICATE,BRIDGE],
         'accepted_proofs':proofs,'verified_paths':paths,'snapshots':snapshots,
         'fresh_reused_identities':reused_identities,
         'oldest_graph_response_saved_at_utc':min(p['snapshot_saved_at_utc'] for p in snapshots),
         'newest_graph_response_saved_at_utc':max(p['snapshot_saved_at_utc'] for p in snapshots),
         'decomposition_edge_readbacks':decomposition_edges,
         'bounded_graph_view_omission_count':len(decomposition_edges),
         'edge_evidence_policy':'actual graph endpoint edges, with explicitly recorded live decomposition children for bounded-view omissions; no import inference',
         'direct_paths':sum(p['path_kind']=='direct' for p in paths),
         'transitive_paths':sum(p['path_kind']=='transitive' for p in paths),
         'every_planned_node_connected_to_original_main':True}
(VER/'machine-graph-check.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
state['actual_edge_audit_complete']=True
state_path.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Verified',len(proofs),'new Proved nodes,',len(reuse),'reused nodes,',len(paths),
      'actual child paths and the unchanged final main reduction.',flush=True)
