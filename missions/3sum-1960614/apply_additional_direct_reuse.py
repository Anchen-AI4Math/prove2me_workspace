"""Replace unpublished duplicate leaves by existing proved platform theorems.

No Lean compilation: the source/CI screen selects candidates and actual parent
proof submissions check compatibility on the server against unchanged targets.
"""
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
before = manifest_path.read_bytes()
manifest = json.loads(before)
state = read(VER / 'machine-platform-publish.json')
current = read(VER / 'machine-additional-direct-reuse-current.json')
records = {r['name']: r for r in manifest['theorems']}
selected = {}
for entry in current:
    candidate, public = entry['candidate'], entry['public']
    record = records[candidate['name']]
    item = state['items'].get(record['name'], {})
    assert not record['children'] and not item.get('job_id') and not item.get('theorem_id')
    assert public['status'] == 'Proved' and public['mathlib_rev'] == manifest['environment']
    assert public['theorem_name'] == record['original_decl'] == candidate['original_decl']
    selected[record['name']] = entry
assert len(selected) == 9
mapping = {name: entry['public']['theorem_name'] for name, entry in selected.items()}
modules = {records[name]['theorem_module']: 'Theorems.Thm_' + replacement.replace('.', '_')
           for name, replacement in mapping.items()}

def rewrite(text):
    for old, new in sorted(modules.items(), key=lambda item: -len(item[0])):
        text = re.sub(re.escape(old) + r'(?![\w\'])', lambda _: new, text)
    for old, new in sorted(mapping.items(), key=lambda item: -len(item[0])):
        text = re.sub(re.escape(old) + r'(?![\w\'])', lambda _: new, text)
    return text

changes = []
for record in manifest['definitions']:
    data = (ROOT / record['path']).read_bytes()
    assert sha(data) == record['sha256']
    # Published interfaces and embedded definition proofs stay byte-identical.
    assert rewrite(data.decode()) == data.decode(), ('Unexpected definition dependency', record['path'])
kept = [r for r in manifest['theorems'] if r['name'] not in selected]
for record in kept:
    item = state['items'].get(record['name'], {})
    for kind in ('theorem', 'solution'):
        rel = record[kind + '_path']
        data = (ROOT / rel).read_bytes()
        assert sha(data) == record[kind + '_sha256']
        result = rewrite(data.decode()).encode()
        if data == result:
            continue
        if kind == 'theorem':
            assert not item.get('theorem_id'), ('Published target would change', record['name'])
            record['preamble'] = rewrite(record['preamble'])
            record['formal_statement'] = rewrite(record['formal_statement'])
            assert result == (record['preamble'] + '\n' + record['formal_statement'] + '\n').encode()
        else:
            assert not item.get('submission_id'), ('Submitted proof would change', record['name'])
        changes.append((rel, data, result))
        record[kind + '_sha256'] = sha(result)
    record['children'] = list(dict.fromkeys(mapping.get(child, child) for child in record['children']))

# All assertions above run before filesystem mutations.
backup_manifest = VER / 'machine-platform-manifest-before-direct-reuse.json'
assert not backup_manifest.exists()
backup_manifest.write_bytes(before)
for rel, data, result in changes:
    backup = VER / 'direct-reuse-originals' / rel
    backup.parent.mkdir(parents=True, exist_ok=True)
    backup.write_bytes(data)
    (ROOT / rel).write_bytes(result)
retired = []
for name, entry in selected.items():
    record = records[name]
    public = entry['public']
    assert public['theorem_name'] not in {r['name'] for r in manifest['reused_theorems']}
    manifest['reused_theorems'].append({'name': public['theorem_name'], 'original_decl': record['original_decl'],
                                      'theorem_id': public['theorem_id'],
                                      'reuse_mode': 'live Proved theorem; matching type and transitive reducible data snapshots; checked by parent submissions'})
    manifest['rename_map'][record['original_decl']] = public['theorem_name']
    paths = []
    for kind in ('theorem', 'solution'):
        source = (ROOT / record[kind + '_path']).resolve()
        destination = (VER / 'direct-reuse-retired' / (record[kind + '_path'] + '.txt')).resolve()
        assert source.is_relative_to(ROOT.resolve()) and destination.is_relative_to(VER.resolve())
        assert source.is_file() and not destination.exists()
        destination.parent.mkdir(parents=True, exist_ok=True)
        source.rename(destination)
        paths.append(destination.relative_to(ROOT).as_posix())
    retired.append({'retired_name': name, 'public_name': public['theorem_name'],
                    'theorem_id': public['theorem_id'], 'original_record': record,
                    'archived_source_files': paths})
manifest['theorems'] = kept
manifest['additional_direct_reuse'] = retired
manifest['validation_complete'] = False
manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
receipt = {'updated_at_utc': datetime.now(timezone.utc).isoformat(),
           'replaced_duplicate_leaf_count': len(retired), 'edited_files': len(changes),
           'new_theorem_count': len(kept), 'reused_theorem_count': len(manifest['reused_theorems']),
           'final_target_unchanged': True, 'published_sources_unchanged': True,
           'local_compilation_performed': False, 'parent_server_acceptance_required': True}
(VER / 'machine-additional-direct-reuse-application.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps(receipt))
