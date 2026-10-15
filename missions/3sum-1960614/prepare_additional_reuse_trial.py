"""Try a proved public theorem against an unchanged existing target, on server."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
name = 'ThreeSum.LightKaratsuba.joined_product'
public = next(r for r in read(VER / 'machine-additional-reuse-first-candidates-current.json') if r['theorem_name'] == name)
assert public['status'] == 'Proved' and public['mathlib_rev'] == manifest['environment']
record = next(r for r in manifest['theorems'] if r['original_decl'] == name)
assert record['children'] == []
state = read(VER / 'machine-platform-publish.json')
item = state['items'][record['name']]
assert item.get('theorem_id') and item.get('proof_status') != 'ACCEPTED'
path = ROOT / record['solution_path']
original = path.read_bytes()
assert sha(original) == record['solution_sha256']
backup = VER / 'additional-reuse-originals' / record['solution_path']
backup.parent.mkdir(parents=True, exist_ok=True)
assert not backup.exists()
backup.write_bytes(original)
extra = 'import Theorems.Thm_' + name.replace('.', '_') + '\n'
preamble = record['preamble']
first_import = preamble.index('import ')
preamble = preamble[:first_import] + extra + preamble[first_import:]
result = (preamble + '\n\ntheorem solution : type_of% (@_root_.' + name + ') :=\n  @_root_.' + name + '\n').encode()
path.write_bytes(result)
record['solution_sha256'] = sha(result)
record['children'] = [name]
assert name not in {r['name'] for r in manifest['reused_theorems']}
manifest['reused_theorems'].append({'name': name, 'original_decl': name,
                                  'theorem_id': public['theorem_id'],
                                  'reuse_mode': 'exact-target server verification pending'})
manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
receipt = {'target_name': record['name'], 'target_theorem_id': item['theorem_id'],
           'public_name': name, 'public_theorem_id': public['theorem_id'],
           'original_solution_sha256': sha(original), 'trial_solution_sha256': sha(result),
           'target_statement_unchanged': True, 'local_compilation_performed': False,
           'server_acceptance_pending': True}
(VER / 'machine-additional-reuse-trial.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
for batch in read(HERE / 'metadata/machine-batches/index.json'):
    if record['name'] not in batch['names']:
        continue
    meta_path = HERE / 'metadata/machine-batches' / ('output-' + str(batch['batch']).zfill(3) + '.json')
    metadata = read(meta_path)
    entry = next(e for e in metadata if e['name'] == record['name'])
    entry['explanation'] = ('Reuses the platform-proved Karatsuba joining identity, with the identical coefficient-storage predicate. '
                            'The platform checks that its complete proof type agrees with this existing target; no assumption or bound is added.')
    meta_path.write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Prepared public-theorem reuse trial for the unchanged joined-product target; no local compile.')
