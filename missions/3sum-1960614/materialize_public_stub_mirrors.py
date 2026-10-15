"""Mirror only imported public theorem interfaces, preserving existing files."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
records = json.loads((VER / 'public-stub-mirror-inputs.json').read_text(encoding='utf-8'))
records = {'Theorems.Thm_' + r['theorem_name'].replace('.', '_'): r for r in records}
headers = json.loads((VER / 'public-stub-mirror-headers.json').read_text(encoding='utf-8'))
headers = {'Theorems.Thm_' + r['name'].replace('.', '_'): r['imports'] for r in headers}
manifest = json.loads((VER / 'machine-platform-manifest.json').read_text(encoding='utf-8'))
pending = ['Theorems.Thm_' + r['name'].replace('.', '_') for r in manifest['reused_theorems']]
seen, mirrors, mismatches, unavailable = set(), [], [], []
while pending:
    module = pending.pop()
    if module in seen:
        continue
    seen.add(module)
    path = ROOT / Path(*module.split('.')).with_suffix('.lean')
    if module not in records:
        if not path.exists():
            unavailable.append(module)
        continue
    record = records[module]
    text = record['preamble'].replace('\r\n', '\n') + '\n' + record['formal_statement'].replace('\r\n', '\n') + '\n'
    if path.exists() and path.read_text(encoding='utf-8').rstrip('\n') != text.rstrip('\n'):
        mismatches.append(module)
    mirrors.append((module, path, text, record['theorem_id']))
    pending.extend(m for m in headers[module] if m.startswith('Theorems.'))
assert not mismatches, ('Existing shared theorem sources differ; inspect without overwriting', mismatches)
assert not unavailable, ('Required public interfaces absent from catalog and workspace', unavailable)
scope_path = HERE / 'scope.json'
scope = json.loads(scope_path.read_text(encoding='utf-8'))
written, fingerprints = [], []
for module, path, text, theorem_id in sorted(mirrors):
    if not path.exists():
        path.write_text(text, encoding='utf-8', newline='\n')
        relative = path.relative_to(ROOT).as_posix()
        if relative not in scope['sources']:
            scope['sources'].append(relative)
        written.append(relative)
    fingerprints.append({'module': module, 'theorem_id': theorem_id,
                         'path': path.relative_to(ROOT).as_posix(),
                         'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
scope_path.write_text(json.dumps(scope, indent=2) + '\n', encoding='utf-8')
receipt = {'interface_mirrors_only': True, 'written': written, 'fingerprints': fingerprints}
(VER / 'machine-public-stub-mirrors.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print('Materialized', len(written), 'missing public stubs;', len(fingerprints), 'exact interfaces in the required import closure.')
