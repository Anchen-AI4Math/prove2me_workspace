"""Expand the source project's import-only utility module into Mathlib imports."""
from datetime import datetime, timezone
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
source = HERE / 'machine/lean/Submission/ThreeSumApsp/Util/Basic.lean'
text = source.read_text(encoding='utf-8')
imports = re.findall(r'^public import (Mathlib\.[\w.]+)$', text, re.M)
# This module is only an import facade; no declaration is being copied/hidden.
stripped = re.sub(r'/\-[\s\S]*?\-/', '', text)
stripped = re.sub(r'^module\s*$', '', stripped, flags=re.M)
stripped = re.sub(r'^public import [\w.]+\s*$', '', stripped, flags=re.M)
assert imports and not stripped.strip()
state_path = VER / 'server-import-apply-state.json'
state = read(state_path) if state_path.exists() else {'items': {}}
macro_path = VER / 'server-macro-apply-state.json'
macro_state = read(macro_path)
records = [(r, 'definition', r['path']) for r in manifest['definitions']]
records += [(r, k, r[k + '_path']) for r in manifest['theorems'] for k in ('theorem', 'solution')]
old = b'import Submission.ThreeSumApsp.Util.Basic\n'
replacement = ('\n'.join('import ' + m for m in imports) + '\n').encode()
count = 0
for record, kind, rel in records:
    path = ROOT / rel
    data = path.read_bytes()
    if old not in data:
        continue
    assert sha(data) == (record['sha256'] if kind == 'definition' else record[kind + '_sha256'])
    backup = VER / 'server-import-originals' / rel
    backup.parent.mkdir(parents=True, exist_ok=True)
    if backup.exists():
        assert backup.read_bytes() == data
    else:
        backup.write_bytes(data)
    result = data.replace(old, replacement)
    if kind == 'definition':
        record['sha256'] = sha(result)
        record['dependencies'] = sorted((set(record['dependencies']) - {'Submission.ThreeSumApsp.Util.Basic'}) | set(imports))
    else:
        if kind == 'theorem':
            assert data == (record['preamble'] + '\n' + record['formal_statement'] + '\n').encode()
            record['preamble'] = record['preamble'].replace(old.decode(), replacement.decode())
            assert result == (record['preamble'] + '\n' + record['formal_statement'] + '\n').encode()
        record[kind + '_sha256'] = sha(result)
    path.write_bytes(result)
    state['items'][rel] = {'original_sha256': sha(data), 'result_sha256': sha(result)}
    macro_state['items'][rel]['result_sha256'] = sha(result)
    macro_state['items'][rel]['subsequent_import_facade_expansion'] = True
    count += 1
state.update(updated_at_utc=datetime.now(timezone.utc).isoformat(),
             facade_source_sha256=sha(source.read_bytes()), imports=imports)
state_path.write_text(json.dumps(state, indent=2) + '\n', encoding='utf-8')
macro_path.write_text(json.dumps(macro_state, indent=2) + '\n', encoding='utf-8')
manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print('Expanded import-only utility facade in', count, 'files; no local proof compilation.')
