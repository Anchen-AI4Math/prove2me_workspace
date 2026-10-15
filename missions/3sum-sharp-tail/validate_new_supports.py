"""Record actual proof checks before publishing open supporting declarations."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('publisher', HERE / 'publish_bridge_nodes.py')
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)
graphs = [json.loads((HERE / ('verification/' + name)).read_text(encoding='utf-8'))
    for name in ('foundation-retuned-graph.json', 'foundation-exact-triangle-graph.json')]
known = {n['theorem_name'].replace('.', '_'): n['theorem_id'] for graph in graphs
    for n in graph['nodes'] if n.get('theorem_name')}
supports = json.loads(publisher.STATE.read_text(encoding='utf-8'))
known.update({'ThreeSumSharpTail_' + name: record['theorem_id'] for name, record in supports.items()
    if record.get('theorem_id')})
record_path = HERE / 'verification/new-support-validation.json'
records = json.loads(record_path.read_text(encoding='utf-8')) if record_path.exists() else {}
for suffix in sys.argv[1:]:
    path = ROOT / f'Solutions/Sol_ThreeSumSharpTail_{suffix}.lean'
    source = path.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b', source.replace('#print axioms solution', ''))
    assert not re.search(r'^\s*(?:private\s+|public\s+)?(?:macro|macro_rules|syntax|elab|elab_rules|initialize)\b', source, re.M), \
        'Platform proof submissions must not register custom metaprogramming'
    result = subprocess.run([sys.executable, '-X', 'utf8', str(HERE / 'check_bridge.py'), str(path)],
        capture_output=True, text=True, encoding='utf-8')
    if result.returncode:
        diagnostics = [line for line in (result.stdout + result.stderr).splitlines()
            if ': error' in line or 'PANIC' in line or 'Traceback' in line]
        print('\n'.join(diagnostics[-20:]), flush=True)
        raise RuntimeError('Lean check failed; see verification/' + path.stem + '-check.txt')
    for line in result.stdout.splitlines():
        if 'depends on axioms:' in line:
            print(line, flush=True)
    children = []
    for module in re.findall(r'^import Theorems\.(\S+)', source, re.M):
        tid = known[module.removeprefix('Thm_')]
        current = publisher.api('GET', '/theorems/' + tid)
        assert current['status'] == 'Proved', current
        children.append({'name': current['theorem_name'], 'id': current['theorem_id'], 'status': current['status']})
    records[suffix] = {'solution': str(path), 'sha256': hashlib.sha256(source.encode()).hexdigest(),
        'lean_exit_code': result.returncode, 'current_proved_children': children,
        'publication_status': 'Open declaration only; completion requires server ACCEPTED of the complete Solution file'}
    print(suffix + ': actual proof compiled; proved children ' + str(len(children)), flush=True)
record_path.write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
