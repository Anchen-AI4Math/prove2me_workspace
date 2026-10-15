"""Read the exact loop-rule graph and decomposition to diagnose missing views."""
from concurrent.futures import ThreadPoolExecutor
import json
import sys
from pathlib import Path
from platform import api

VER = Path(__file__).resolve().parent / 'verification'
tid = 'b437f18c-a389-40ea-b050-104ef93ebeb7'
sid = 'a2848852-6d3c-4c06-a816-d1b76f4d365a'
state = json.loads((VER / 'machine-platform-publish.json').read_text(encoding='utf-8'))
child = state['items']['ThreeSum1960614.Machine.Light.Ends.while']['theorem_id']
paths = [('loop-decompositions', '/theorems/' + tid + '/decompositions'),
         ('loop-graph', '/theorems/' + tid + '/graph'),
         ('while-graph', '/theorems/' + child + '/graph')]
if '--focused' in sys.argv:
    paths = [('loop-focused', '/theorems/' + tid + '/graph?depth=2&expand_node=' + tid + '&direction=children')]


def fetch(task):
    label, path = task
    result = api('GET', path)
    (VER / ('graph-view-' + label + '.json')).write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    if 'nodes' in result:
        print(label, 'nodes', len(result['nodes']), 'edges', len(result['edges']),
              'parent edges', [e for e in result['edges'] if e['target'] == tid], flush=True)
    else:
        print(label, json.dumps(result), flush=True)


with ThreadPoolExecutor(max_workers=3) as pool:
    list(pool.map(fetch, paths))
