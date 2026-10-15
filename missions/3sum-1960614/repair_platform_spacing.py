"""Keep the natural-number ≤ token distinct from imported graph notation ≤s."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
assert (VER / 'machine-server-first.pause').exists()
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
digest = lambda b: hashlib.sha256(b).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
state = read(VER / 'machine-platform-publish.json')
conversion_path = VER / 'server-macro-apply-state.json'
conversion = read(conversion_path)
prepared = []
for record in manifest['definitions']:
    name = record['module'].removeprefix('Definitions.Def_')
    item = state['items'].get(name, {})
    if item.get('theorem_id') or item.get('job_id') and item.get('publish_status') not in ('FAILED','ERROR'):
        continue
    path = ROOT / record['path']
    original = path.read_bytes()
    revised = original.replace('≤stop'.encode(), '≤ stop'.encode()).replace('≤selected'.encode(),'≤ selected'.encode()).replace('≤mask'.encode(),'≤ mask'.encode()).replace('∣_root_'.encode(),'∣ _root_'.encode())
    if record['module'].endswith('Bundle034'):
        source = revised.decode('utf-8')
        source = source.replace(
            '''  | k+1 => time I w D k+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time h J k (D (k+1)).t (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length+200''',
            '''  | stageIndex+1 => time I w D stageIndex+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time h J stageIndex (D (stageIndex+1)).t (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w stageIndex).length+200''')
        source = source.replace(
            '  | k+1 => levelOffset h J boxCut k+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J k (boxCut k)',
            '  | stageIndex+1 => levelOffset h J boxCut stageIndex+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J stageIndex (boxCut stageIndex)')
        revised = source.encode('utf-8')
    if original == revised:
        continue
    name = record['module'].removeprefix('Definitions.Def_')
    item = state['items'].get(name, {})
    assert not item.get('theorem_id'), name
    assert not item.get('job_id') or item.get('publish_status') in ('FAILED', 'ERROR'), name
    assert digest(original) == record['sha256'], name
    entry = conversion['items'][record['path']]
    assert digest(original) == entry['result_sha256'], name
    backup = VER / 'server-proof-originals' / (path.stem + '-' + digest(original)[:12] + '.lean.txt')
    if backup.exists():
        assert backup.read_bytes() == original
    else:
        backup.write_bytes(original)
    change = {'name': name, 'path': record['path'], 'previous_sha256': digest(original),
              'current_sha256': digest(revised), 'reason': 'notation spacing or local natural-number pattern alpha-renaming',
              'changed_mathematical_declarations': False,
              'whitespace_insertions': original.count('≤stop'.encode()),
              'backup': str(backup.relative_to(ROOT))}
    prepared.append((record, path, revised, entry, change, 'sha256', None))
for record in manifest['theorems']:
    name = record['name']
    item = state['items'].get(name, {})
    if record.get('existing_theorem_id') or item.get('theorem_id') or item.get('job_id') and item.get('publish_status') not in ('FAILED','ERROR'):
        continue
    before = record['preamble'] + '\n' + record['formal_statement'] + '\n'
    after = before.replace('≤stop', '≤ stop').replace('≤selected','≤ selected').replace('≤mask','≤ mask').replace('∣_root_','∣ _root_')
    if before == after:
        continue
    name = record['name']
    item = state['items'].get(name, {})
    assert not item.get('theorem_id') and not record.get('existing_theorem_id'), name
    assert not item.get('job_id') or item.get('publish_status') in ('FAILED', 'ERROR'), name
    path = ROOT / record['theorem_path']
    original = path.read_bytes()
    revised = after.encode('utf-8')
    assert original == before.encode('utf-8')
    assert digest(original) == record['theorem_sha256']
    entry = conversion['items'][record['theorem_path']]
    assert entry['result_sha256'] == digest(original)
    backup = VER / 'server-proof-originals' / (path.stem + '-' + digest(original)[:12] + '.lean.txt')
    if backup.exists():
        assert backup.read_bytes() == original
    else:
        backup.write_bytes(original)
    change = {'name': name, 'path': record['theorem_path'], 'previous_sha256': digest(original),
              'current_sha256': digest(revised), 'reason': 'separate ≤ from the following natural-number binder stop',
              'changed_mathematical_declarations': False,
              'whitespace_insertions': before.count('≤stop'),
              'backup': str(backup.relative_to(ROOT))}
    fields = {key: record[key].replace('≤stop', '≤ stop').replace('≤selected','≤ selected').replace('≤mask','≤ mask').replace('∣_root_','∣ _root_') for key in ('preamble', 'formal_statement')}
    prepared.append((record, path, revised, entry, change, 'theorem_sha256', fields))
for record, path, revised, entry, change, hash_key, fields in prepared:
    path.write_bytes(revised)
    record[hash_key] = digest(revised)
    if fields:record.update(fields)
    entry.setdefault('post_conversion_changes', []).append(change)
    entry['result_sha256'] = digest(revised)
if prepared:
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    conversion_path.write_text(json.dumps(conversion, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    (VER / 'server-notation-spacing-repairs.json').write_text(
        json.dumps({'checked_at_utc': datetime.now(timezone.utc).isoformat(),
                    'changes': [p[4] for p in prepared]}, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Unpublished sources repaired:', len(prepared))
