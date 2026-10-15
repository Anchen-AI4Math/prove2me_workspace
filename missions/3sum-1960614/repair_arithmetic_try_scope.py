"""Parenthesize each optional clear without swallowing the following omega."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from platform import api

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
assert (VER / 'machine-server-first.pause').exists()
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
digest = lambda b: hashlib.sha256(b).hexdigest()
mp = VER / 'machine-platform-manifest.json'
sp = VER / 'machine-platform-publish.json'
cp = VER / 'server-macro-apply-state.json'
manifest, state, conversion = read(mp), read(sp), read(cp)
names = {
    'ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program_meets',
    'ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program_meets',
}
changes = []
for record in manifest['theorems']:
    name = record['name']
    if name not in names:
        continue
    item = state['items'][name]
    verdict = api('GET', '/verify?submission_id=' + item['submission_id'])
    item['proof_status'] = verdict['status']
    if verdict['status'] not in ('CE', 'WA', 'ERROR', 'FAILED'):
        print('Not changing current', verdict['status'], name, flush=True)
        continue
    path = ROOT / record['solution_path']
    original = path.read_bytes()
    source = original.decode('utf-8')
    revised, count = re.subn(r'try clear (H|HL|hreport|hselected|hlayout|hreportRun|Hparams|hscan);',
                             r'(try clear \1);', source)
    if not count:
        continue
    revised = revised.encode('utf-8')
    entry = conversion['items'][record['solution_path']]
    assert digest(original) == record['solution_sha256'] == entry['result_sha256']
    backup = VER / 'server-proof-originals' / (path.stem + '-' + digest(original)[:12] + '.lean.txt')
    backup.write_bytes(original)
    change = {'name': name, 'path': record['solution_path'],
              'previous_sha256': digest(original), 'current_sha256': digest(revised),
              'changed_statement': False, 'optional_clear_parentheses': count,
              'reason': 'parentheses delimit each optional clear before the mandatory arithmetic solver',
              'backup': str(backup.relative_to(ROOT))}
    path.write_bytes(revised)
    record['solution_sha256'] = digest(revised)
    entry.setdefault('post_conversion_changes', []).append(change)
    entry['result_sha256'] = digest(revised)
    changes.append(change)
if changes:
    mp.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    cp.write_text(json.dumps(conversion, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    receipt_path = VER / 'server-arithmetic-context-repairs.json'
    receipt = read(receipt_path)
    receipt['changes'].extend(changes)
    receipt['updated_at_utc'] = datetime.now(timezone.utc).isoformat()
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
sp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Corrected tactic scopes in', len(changes), 'terminal proof sources.', flush=True)
