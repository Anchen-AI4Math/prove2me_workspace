"""Reconcile persisted proof intents against own submissions before any retry."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from platform import api, p2m

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
state_path = VER / 'machine-platform-publish.json'
state = json.loads(state_path.read_text(encoding='utf-8'))
manifest = json.loads((VER / 'machine-platform-manifest.json').read_text(encoding='utf-8'))
records = {r['name']: r for r in manifest['theorems']}
pending = [(name, item) for name, item in state['items'].items()
           if item.get('verify_intent') and not item.get('submission_id')]
receipt = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'intents': []}
if pending:
    profile = api('GET', '/me')
    receipt['profile_user_id'] = profile.get('user_id', profile.get('id'))
    assert receipt['profile_user_id'] == '418b0711-62a5-416a-ba5d-876ae8758fe3'
    earliest = min(item['verify_intent']['requested_at_utc'] for _, item in pending)
    submissions = []
    page = 1
    while True:
        response = api('GET', '/submissions?page=' + str(page))
        rows = response['submissions']
        submissions.extend(rows)
        if not rows or min(r['created_at'] for r in rows) < earliest or page * 100 >= response['total']:
            break
        page += 1
    for name, item in pending:
        record = records[name]
        source = (ROOT / record['solution_path']).read_bytes()
        assert hashlib.sha256(source).hexdigest() == item['submitted_solution_sha256']
        candidates = [r for r in submissions if r['theorem_id'] == item['theorem_id']
                      and r['created_at'] >= item['verify_intent']['requested_at_utc']]
        matched = []
        for row in candidates:
            sid = row.get('submission_id', row.get('id'))
            status, code = p2m._request('GET', '/submissions/' + sid + '/solution', token=p2m.get_token())
            assert status == 200, (sid, status)
            if code.encode('utf-8') == source:
                matched.append((sid, row['status']))
        assert len(matched) <= 1, ('Ambiguous duplicate submissions', name, matched)
        entry = {'name': name, 'theorem_id': item['theorem_id'],
                 'intent': item['verify_intent'], 'scanned_pages': page,
                 'matching_submissions': matched}
        if matched:
            item['submission_id'], item['proof_status'] = matched[0]
        else:
            # The full own-history interval after this intent was scanned.
            # In particular the saved 404 response did not create a proof.
            item.setdefault('verify_intent_history', []).append(
                {**item.pop('verify_intent'), 'reconciled_no_submission': True})
        receipt['intents'].append(entry)
    state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
(VER / 'machine-proof-intent-reconciliation.json').write_text(
    json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Reconciled', len(pending), 'proof intents against own submission history.')
