"""Check complete metadata coverage without compiling any Lean proof."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
BATCHES = HERE / 'metadata/machine-batches'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
manifest = read(VER / 'machine-platform-manifest.json')
seen = {}
counts = {'definition': 0, 'theorem': 0}
for batch in read(BATCHES / 'index.json'):
    source = ROOT / batch['input']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == batch['sha256']
    originals = read(source)['items']
    entries = read(BATCHES / ('output-' + str(batch['batch']).zfill(3) + '.json'))
    assert [e['name'] for e in entries] == batch['names']
    assert len(entries) == len(originals)
    for original, entry in zip(originals, entries):
        name = entry['name']
        assert name == original['name'] and name not in seen
        kind = original['kind']
        title = entry[kind + '_title']
        assert isinstance(title, str) and 0 < len(title) <= 200
        assert len(entry['natural_language_statement']) >= 100
        assert isinstance(entry['tags'], list) and '3sum-1960614' in entry['tags']
        if kind == 'theorem':
            assert len(entry['explanation']) >= 100
        for value in entry.values():
            if isinstance(value, str):
                assert not any(ord(c) < 32 and c not in '\n\r\t' for c in value)
        counts[kind] += 1
        seen[name] = entry
expected = {r['module'].removeprefix('Definitions.Def_') for r in manifest['definitions']}
expected.update(r['name'] for r in manifest['theorems'])
retired = {r['retired_name'] for r in manifest.get('additional_direct_reuse', [])}
assert set(seen) == expected | retired
receipt = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
           'all_names_exactly_once': True, 'counts': counts,
           'active_counts': {'definition': len(manifest['definitions']), 'theorem': len(manifest['theorems'])},
           'retired_duplicate_metadata_count': len(retired),
           'batch_count': len(read(BATCHES / 'index.json')),
           'local_proof_compilation_performed': False}
(VER / 'machine-metadata-validation.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps(receipt))
