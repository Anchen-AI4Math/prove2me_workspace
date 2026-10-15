"""Screen existing CI snapshots for reducible data agreement; never compile Lean.

This is candidate selection only. An accepted server proof of the unchanged
target, or of a parent using the candidate directly, remains the final check.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path

VER = Path(__file__).resolve().parent / 'verification'
read = lambda n: json.loads((VER / n).read_text(encoding='utf-8'))
index = read('extended-reuse-compact-index.json')
native, public = index['native'], index['public']
rows = {r['name']: r for r in map(json.loads, (VER / 'machine-decl-graph.jsonl').read_text(encoding='utf-8').splitlines())}
approved = set(read('machine-definition-reuse.json')['definitions'])
types = {r['name']: r for r in read('public-theorem-probe-types.json')}
catalog = {r['theorem_name']: r for r in read('machine-public-1962-catalog.json')['records'] if r['status'] == 'Proved'}
manifest = read('machine-platform-manifest.json')
state = read('machine-platform-publish.json')
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
memo = {}

def type_matches(name):
    left = native.get(name)
    right = public.get(name)
    if left is None:
        return False
    if right is not None:
        return left['type_sha256'] == right['type_sha256'] and left['universeCount'] == right['universeCount']
    right = types.get(name)
    return right is not None and left['universeCount'] == right['universeCount'] and left['type_sha256'] == hashlib.sha256(right['type'].encode()).hexdigest()

def agrees(name, active=frozenset()):
    if name in approved:
        return True, None
    if name in memo:
        return memo[name]
    if name in active:
        return False, 'recursive data cycle requiring server check: ' + name
    left = native.get(name)
    right = public.get(name)
    if left is None or not type_matches(name):
        return False, 'missing or different type: ' + name
    if not set(left['axioms']) <= STANDARD:
        return False, 'nonstandard axiom: ' + name
    if left['isProof']:
        deps = rows[name]['typeDeps']
    elif left['kind'] == 'definition' and right is not None:
        if left['value_sha256'] != right['value_sha256'] or left['shape'] != right['shape']:
            return False, 'different data definition: ' + name
        deps = rows[name]['typeDeps'] + rows[name]['valueDeps']
    else:
        return False, 'fresh primitive or unavailable data: ' + name
    for dep in deps:
        result = agrees(dep, active | {name})
        if not result[0]:
            memo[name] = result
            return result
    memo[name] = (True, None)
    return memo[name]

candidates, rejected = [], []
for record in manifest['theorems']:
    name = record['original_decl']
    item = state['items'].get(record['name'], {})
    if name not in catalog or item.get('proof_status') == 'ACCEPTED':
        continue
    if not type_matches(name):
        rejected.append({'name': name, 'reason': 'different or unavailable theorem type'})
        continue
    result = next((result for dep in rows[name]['typeDeps'] if not (result := agrees(dep))[0]), (True, None))
    if result[0]:
        candidates.append({'name': record['name'], 'original_decl': name,
                           'candidate_id': catalog[name]['theorem_id'],
                           'already_published': bool(item.get('theorem_id')),
                           'children': record['children'],
                           'server_type_check_required': True})
    else:
        rejected.append({'name': name, 'reason': result[1]})
report = {'method': 'Existing compiler CI/type snapshots and transitive data agreement; no new Lean elaboration',
          'candidate_count': len(candidates), 'candidates': candidates,
          'rejected_count': len(rejected), 'rejected': rejected,
          'not_a_server_acceptance_receipt': True}
(VER / 'machine-additional-reuse-screen.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Screened additional public reuse:', len(candidates), 'candidates;', len(rejected), 'excluded; no local proof compilation.')
print(json.dumps([{'name': r['original_decl'], 'children': len(r['children'])} for r in candidates[:25]]))
