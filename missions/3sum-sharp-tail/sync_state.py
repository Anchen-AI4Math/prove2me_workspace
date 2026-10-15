"""Snapshot only this user's 3SUM proposal and its published theorem graph."""
import importlib.util
import json
from pathlib import Path
import time
from urllib.error import URLError

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('p2m', ROOT / 'scripts/p2m_api.py')
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)


def api(path):
    for attempt in range(4):
        try:
            status, raw = p2m._request('GET', path, token=p2m.get_token())
        except (URLError, ConnectionError, TimeoutError):
            if attempt == 3:
                raise
            time.sleep(2 ** attempt)
            continue
        if status == 200:
            return json.loads(raw)
        if status >= 500 and attempt < 3:
            time.sleep(2 ** attempt)
            continue
        raise RuntimeError(f'GET {path}: HTTP {status}: {raw[:1000]}')


def save(name, data):
    (HERE / 'verification' / name).write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def write_reference(key, preamble, statement):
    path = ROOT / 'Theorems' / ('Thm_' + key + '.lean')
    text = preamble + '\n\n' + statement + '\n'
    if not path.exists() or path.read_text(encoding='utf-8') != text:
        path.write_text(text, encoding='utf-8')


if __name__ == '__main__':
    proposal = api('/mission-proposals/7552d42d-7c8c-4f16-aead-ec41ac6cc8d5')
    save('proposal-current.json', proposal)
    for item in proposal['items']:
        if item.get('status') == 'Definition':
            continue
        tid = item['theorem_id']
        theorem = api('/theorems/' + tid)
        key = item['theorem_name'].replace('.', '_')
        save(key + '-current.json', theorem)
        write_reference(key, item['preamble'], item['formal_statement'])
        save(key + '-graph.json', api('/theorems/' + tid + '/graph'))
        save(key + '-decompositions.json', api('/theorems/' + tid + '/decompositions'))
        print(key + ': ' + theorem.get('status', '?'), flush=True)
    for state_file in ['certificate-nodes.json', 'bridge-nodes.json']:
        nodes = HERE / 'verification' / state_file
        if not nodes.exists():
            continue
        for suffix, record in json.loads(nodes.read_text(encoding='utf-8')).items():
            tid = record.get('theorem_id')
            if not tid:
                continue
            theorem = api('/theorems/' + tid)
            key = 'ThreeSumSharpTail_' + suffix
            save(key + '-current.json', theorem)
            payload = record['payload']
            write_reference(key, payload['preamble'], payload['formal_statement'])
            save(key + '-graph.json', api('/theorems/' + tid + '/graph'))
            save(key + '-decompositions.json', api('/theorems/' + tid + '/decompositions'))
            print(key + ': ' + theorem.get('status', '?'), flush=True)
