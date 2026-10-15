"""Fetch the exact platform modules needed by the new cost bridge.

This imports definitions and theorem references only, not claims of closure.
Files stay in this task's dependency mirror; existing workspace files are untouched.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MIRROR = HERE / 'verification/foundation-mirror'
spec = importlib.util.spec_from_file_location('p2m', ROOT / 'scripts/p2m_api.py')
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)


def api(path):
    status, raw = p2m._request('GET', path, token=p2m.get_token())
    if status != 200:
        raise RuntimeError(f'{path}: HTTP {status}: {raw[:500]}')
    return json.loads(raw)


def main():
    graph = json.loads((HERE / 'verification/foundation-exact-triangle-graph.json').read_text(encoding='utf-8'))
    known = {n['theorem_name'].replace('.', '_'): n['theorem_id']
             for n in graph['nodes'] if n.get('theorem_name')}
    queue = sys.argv[1:]
    if not queue:
        raise SystemExit('Pass exact platform module names, e.g. Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Theorem30')
    seen = set()
    while queue:
        module = queue.pop(0)
        if module in seen:
            continue
        seen.add(module)
        rel = Path(*module.split('.')).with_suffix('.lean')
        # Local shared files are authoritative and should not be overwritten.
        if (ROOT / rel).exists():
            continue
        target = MIRROR / rel
        snapshot = MIRROR / 'responses' / (module + '.json')
        if snapshot.exists():
            data = json.loads(snapshot.read_text(encoding='utf-8'))
        else:
            prefix = 'Def_' if module.startswith('Definitions.') else 'Thm_'
            name = module.split('.', 1)[1].removeprefix(prefix)
            tid = known.get(name)
            if tid is None:
                query = '_'.join(name.split('_')[-2:])
                status = '&status=Definition' if prefix == 'Def_' else ''
                results = api('/theorems?q=' + query + status + '&limit=50')
                matches = [n for n in results.get('theorems', []) if n['theorem_name'].replace('.', '_') == name]
                if len(matches) != 1:
                    raise RuntimeError('Cannot identify exact platform module: ' + module)
                tid = matches[0]['theorem_id']
            data = api('/theorems/' + tid)
            snapshot.parent.mkdir(parents=True, exist_ok=True)
            snapshot.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        text = data.get('definition') if data.get('status') == 'Definition' else None
        if not text:
            text = data.get('definitions')
        if not text:
            text = data.get('preamble', '') + '\n\n' + data.get('formal_statement', '')
        if not text.strip():
            raise RuntimeError('Empty module response: ' + module)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_text(encoding='utf-8') != text + '\n':
            target.write_text(text + '\n', encoding='utf-8')
        imports = re.findall(r'^\s*(?:public\s+)?import\s+((?:Definitions|Theorems)\.\S+)\s*$', text, re.M)
        queue.extend(imports)
        print(module + ': ' + data.get('status', '?') + f' ({len(text)} chars)', flush=True)


if __name__ == '__main__':
    main()
