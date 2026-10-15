"""Alpha-rename a program-prefix parameter mistaken for the prelude command."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
published = read(VER / 'machine-platform-publish.json')['items']
macro_path = VER / 'server-macro-apply-state.json'
macro_state = read(macro_path)
records = [(r, 'definition', r['path']) for r in manifest['definitions']]
records += [(r, k, r[k + '_path']) for r in manifest['theorems'] for k in ('theorem', 'solution')]
receipt = []
for r, kind, rel in records:
    path = ROOT / rel
    original = path.read_bytes()
    result = re.sub(rb'\bprelude\b', b'prefixProgram', original)
    if result == original:
        continue
    if kind == 'definition':
        name = r['module'].removeprefix('Definitions.Def_')
        assert not published.get(name, {}).get('theorem_id')
        r['sha256'] = sha(result)
    else:
        assert not published.get(r['name'], {}).get('theorem_id')
        if kind == 'theorem':
            r['preamble'] = re.sub(r'\bprelude\b', 'prefixProgram', r['preamble'])
            r['formal_statement'] = re.sub(r'\bprelude\b', 'prefixProgram', r['formal_statement'])
            assert result == (r['preamble'] + '\n' + r['formal_statement'] + '\n').encode()
        r[kind + '_sha256'] = sha(result)
    backup = VER / 'server-prefix-originals' / rel
    backup.parent.mkdir(parents=True, exist_ok=True)
    if backup.exists():
        assert backup.read_bytes() == original
    else:
        backup.write_bytes(original)
    path.write_bytes(result)
    macro_state['items'][rel]['result_sha256'] = sha(result)
    receipt.append({'path': rel, 'before_sha256': sha(original), 'after_sha256': sha(result)})
manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
macro_path.write_text(json.dumps(macro_state, indent=2) + '\n', encoding='utf-8')
(VER / 'server-prefix-parameter-rename.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print('Renamed program-prefix parameter and corresponding references in', len(receipt), 'files; no mathematical compilation.')
