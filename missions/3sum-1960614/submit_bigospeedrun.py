"""Idempotently submit the audited public proof via the official issue route.

The issue is only a request for official verification, never an acceptance claim.
No credentials are read or emitted; gh uses its existing signed-in session.
"""
from datetime import datetime, timezone
import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
VER = HERE / 'verification'
REPO = 'Anchen0823/three-sum-1960614'
COMMIT = '8c25c0325de5be4286413f39ca0c9278aad33f52'
BOUND = '980307/500000'
STATE = VER / 'bigospeedrun-submission.json'
BODY = ('### Problem\n\n3sum\n\n### Repository URL\n\nhttps://github.com/' + REPO
        + '\n\n### Commit SHA\n\n' + COMMIT + '\n\n### Bound\n\n' + BOUND + '\n')
env = os.environ.copy()
env.update(HTTPS_PROXY='http://127.0.0.1:65532', HTTP_PROXY='http://127.0.0.1:65532')


def gh(*args):
    result = subprocess.run(['gh', *args], env=env, text=True,
                            encoding='utf-8', capture_output=True, check=True)
    return result.stdout.strip()


def api(path):
    return json.loads(gh('api', path))


def save(state):
    STATE.write_text(json.dumps(state, indent=2) + '\n', encoding='utf-8')


repo = api('repos/' + REPO)
assert repo['private'] is False
commit = api('repos/' + REPO + '/commits/main')
assert commit['sha'] == COMMIT
remote = api('repos/' + REPO + '/contents/Submission/EndStatement.lean?ref=' + COMMIT)
frozen_hash = hashlib.sha256(base64.b64decode(remote['content'])).hexdigest()
assert frozen_hash == '4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987'
state = json.loads(STATE.read_text(encoding='utf-8')) if STATE.exists() else {}
state.update(repo_url=repo['html_url'], commit=COMMIT, bound=BOUND,
             frozen_statement_sha256=frozen_hash, public_source_verified=True)
state.setdefault('official_lean_verified',False)
body_path = VER / 'bigospeedrun-issue-body.md'
body_path.write_text(BODY, encoding='utf-8')
if not state.get('issue_url'):
    existing = json.loads(gh('issue', 'list', '--repo', 'bigospeedrun/verifier',
                            '--author', '@me', '--state', 'all', '--limit', '100',
                            '--json', 'number,url,body'))
    matches = [issue for issue in existing if issue['body'].replace('\r\n', '\n').strip()
               == BODY.strip()]
    assert len(matches) <= 1, 'Duplicate submission issues require inspection'
    if matches:
        issue_url = matches[0]['url']
    else:
        state.update(action='create official verification issue',
                     requested_at_utc=datetime.now(timezone.utc).isoformat())
        save(state)
        issue_url = gh('issue', 'create', '--repo', 'bigospeedrun/verifier',
                       '--title', '[Lean submission] 3SUM exponent ' + BOUND,
                       '--body-file', str(body_path))
    state.update(issue_url=issue_url, submitted=True)
    save(state)
number = state['issue_url'].rsplit('/', 1)[1]
issue = api('repos/bigospeedrun/verifier/issues/' + number)
assert issue['body'].replace('\r\n', '\n').strip() == BODY.strip()
state.update(issue_number=issue['number'], issue_state=issue['state'],
             issue_created_at=issue['created_at'],
             checked_at_utc=datetime.now(timezone.utc).isoformat())
save(state)
receipt_path = VER / 'bigospeedrun-package-receipt.json'
receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
receipt.update(submitted=True, public_repository=repo['html_url'],
               public_commit=COMMIT, submission_issue=state['issue_url'])
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print('Official verification request submitted:', state['issue_url'])
print('Public proof source:', repo['html_url'] + '/tree/' + COMMIT)
print('Site acceptance and official Lean verification are still pending.')
