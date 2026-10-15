"""Read back accepted machine branches without claiming the open root is closed.

This audit never writes uploader state. Its stable snapshot can run while the
single publisher advances, and checks actual graph paths rather than imports.
"""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from platform import api
from machine_graph_paths import actual_child_path, graph_endpoint
from machine_queue_reads import owner_status_reads

HERE = Path(__file__).resolve().parent
VER = HERE / 'verification'
OUT = VER / 'machine-frontier-readback'
OUT.mkdir(exist_ok=True)
read = lambda path: json.loads(path.read_text(encoding='utf-8'))
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
state = read(VER / 'machine-platform-publish.json')
MAIN = 'a53b364e-57a0-4d2c-adc6-983a74218a4b'
BRIDGE = '7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
ORIGINAL = '17448ceb-49aa-4f37-9e4e-107b286f0059'
accepted = [r for r in manifest['theorems']
            if state['items'].get(r['name'], {}).get('proof_status') == 'ACCEPTED']
ids = {r['name']: r['theorem_id'] for r in manifest['reused_theorems']}
ids.update({name: item['theorem_id'] for name, item in state['items'].items()
            if item.get('theorem_id')})


def fetch(task):
    label, path = task
    response = api('GET', path)
    (OUT / (label + '.json')).write_text(
        json.dumps(response, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    return label, response


tasks = [('main', '/theorems/' + MAIN),
         ('bridge', '/theorems/' + BRIDGE),
         ('main-graph', graph_endpoint(MAIN)),
         ('main-decompositions', '/theorems/' + MAIN + '/decompositions'),
         ('original-reduction', '/verify?submission_id=' + ORIGINAL)]
for index, record in enumerate(accepted):
    item = state['items'][record['name']]
    assert item['verified_solution_sha256'] == record['solution_sha256']
    tasks.append((f'graph-{index:04}', graph_endpoint(item['theorem_id'])))
verdicts = owner_status_reads({r['name']: state['items'][r['name']] for r in accepted}, include_accepted=True)
with ThreadPoolExecutor(max_workers=4) as pool:
    replies = dict(pool.map(fetch, tasks))
for index, record in enumerate(accepted):
    verdict = verdicts['/verify?submission_id=' + state['items'][record['name']]['submission_id']]
    replies[f'verdict-{index:04}'] = verdict
    (OUT / f'verdict-{index:04}.json').write_text(json.dumps(verdict, indent=2) + '\n', encoding='utf-8')

paths = []
proofs = []
all_edges = set()
all_nodes = {}
for reply in replies.values():
    if not isinstance(reply, dict) or 'edges' not in reply or 'nodes' not in reply:
        continue
    all_edges.update((e['source'], e['target'], e['kind']) for e in reply['edges'])
    all_nodes.update({node['theorem_id']: node for node in reply['nodes']
                      if node.get('node_type') == 'theorem'})
for index, record in enumerate(accepted):
    item = state['items'][record['name']]
    graph = replies[f'graph-{index:04}']
    verdict = replies[f'verdict-{index:04}']
    assert verdict['status'] == 'ACCEPTED', (record['name'], verdict['status'])
    assert graph['root_id'] == item['theorem_id']
    nodes = all_nodes
    assert nodes[item['theorem_id']]['status'] == 'Proved'
    assert nodes[item['theorem_id']]['theorem_name'] == record['name']
    edges = all_edges
    sketch = 'sketch-' + item['submission_id']
    for child in record['children']:
        child_id = ids[child]
        try:
            actual = actual_child_path(edges, child_id, item['submission_id'], item['theorem_id'])
        except AssertionError:
            _, expanded = fetch((f'parents-{child_id}', graph_endpoint(child_id, 2, 'parents')))
            edges.update((e['source'], e['target'], e['kind']) for e in expanded['edges'])
            nodes.update({node['theorem_id']: node for node in expanded['nodes'] if node.get('node_type')=='theorem'})
            try:
                actual = actual_child_path(edges, child_id, item['submission_id'], item['theorem_id'])
            except AssertionError:
                _, expanded = fetch((f'graph-{index:04}-expanded', graph_endpoint(item['theorem_id'], 4)))
                edges.update((e['source'], e['target'], e['kind']) for e in expanded['edges'])
                nodes.update({node['theorem_id']: node for node in expanded['nodes'] if node.get('node_type')=='theorem'})
                actual = actual_child_path(edges, child_id, item['submission_id'], item['theorem_id'])
        assert nodes[child_id]['status'] == 'Proved', child
        paths.append({'child': child_id, 'child_name': child,
                      'parent': item['theorem_id'], 'parent_name': record['name'],
                      'submission_id': item['submission_id'], **actual})
    proofs.append({'name': record['name'], 'theorem_id': item['theorem_id'],
                   'submission_id': item['submission_id'], 'status': 'ACCEPTED'})

receipt = {'read_at_utc': datetime.now(timezone.utc).isoformat(),
           'manifest_sha256': hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
           'state_snapshot_at_utc': state.get('updated_at_utc'),
           'new_proved_nodes_audited': len(proofs), 'verified_child_paths': len(paths),
           'direct_paths': sum(p['path_kind']=='direct' for p in paths),
           'transitive_paths': sum(p['path_kind']=='transitive' for p in paths),
           'main_goal_status': replies['main']['status'],
           'bridge_status': replies['bridge']['status'],
           'original_reduction_status': replies['original-reduction']['status'],
           'full_machine_graph_complete': False,
           'accepted_proofs': proofs, 'verified_paths': paths,
           'remaining_new_proofs': len(manifest['theorems']) - len(proofs)}
(VER / 'machine-frontier-graph-check.json').write_text(
    json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in receipt.items()
                  if k not in ('accepted_proofs', 'verified_paths')}, ensure_ascii=True))
