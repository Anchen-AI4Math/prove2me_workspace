"""Install only the exact fetched imports of named bridge modules.

Existing shared files must match byte-for-byte. This never overwrites a
different workspace module and records the imported sources in this task's scope.
"""
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MIRROR = HERE / 'verification/foundation-mirror'
scope_path = HERE / 'scope.json'
scope = json.loads(scope_path.read_text(encoding='utf-8'))
queue = sys.argv[1:]
seen = set()
installed = []
while queue:
    module = queue.pop(0)
    if module in seen:
        continue
    seen.add(module)
    rel = Path(*module.split('.')).with_suffix('.lean')
    src = MIRROR / rel
    dst = ROOT / rel
    if dst.exists():
        if src.exists() and dst.read_text(encoding='utf-8') != src.read_text(encoding='utf-8'):
            raise RuntimeError('Existing shared module differs: ' + module)
        text = dst.read_text(encoding='utf-8')
    else:
        text = src.read_text(encoding='utf-8')
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(text, encoding='utf-8')
        installed.append(rel.as_posix())
    if rel.as_posix() not in scope['sources']:
        scope['sources'].append(rel.as_posix())
    queue.extend(re.findall(r'^\s*(?:public\s+)?import\s+((?:Definitions|Theorems)\.\S+)\s*$', text, re.M))
scope_path.write_text(json.dumps(scope, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
(HERE / 'verification/bridge-dependency-install.json').write_text(json.dumps({
    'requested': sys.argv[1:], 'import_closure': sorted(seen), 'new_files': installed},
    ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(f'{len(installed)} exact shared dependency modules installed; task scope updated.')
