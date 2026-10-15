"""Supervise this authorized run, reconciling interrupted writes before restart.

This is a current-task process, not a scheduled automation. Source errors remain
per-item review obligations. Only transient network failures trigger restarts.
"""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
VER = HERE / 'verification'
STATE = VER / 'machine-platform-publish.json'
LOG = VER / 'machine-server-first-publish-run.txt'
CHECKPOINT = VER / 'machine-publisher-supervisor.json'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
concurrency = int(sys.argv[1]) if len(sys.argv) > 1 else 32
assert 1 <= concurrency <= 32
failures = 0
attempt = 0
while True:
    if (VER / 'machine-server-first.pause').exists():
        print('Supervisor stopped at the requested safe pause.', flush=True)
        break
    before = read(STATE)
    accepted_before = sum(i.get('proof_status') == 'ACCEPTED' for i in before['items'].values())
    attempt += 1
    start = LOG.stat().st_size if LOG.exists() else 0
    with LOG.open('ab') as log:
        process = subprocess.Popen(
            [sys.executable, '-u', str(HERE / 'publish_machine_server_first.py'), '--watch', '--concurrency', str(concurrency)],
            stdout=log, stderr=subprocess.STDOUT,
            creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
        checkpoint = {'started_at_utc': datetime.now(timezone.utc).isoformat(),
                      'attempt': attempt, 'child_pid': process.pid,
                      'concurrency': concurrency, 'accepted_before': accepted_before,
                      'status': 'running'}
        CHECKPOINT.write_text(json.dumps(checkpoint, indent=2) + '\n', encoding='utf-8')
        print('Publisher attempt', attempt, 'PID', process.pid, 'accepted', accepted_before, flush=True)
        code = process.wait()
    checkpoint.update(exit_code=code, exited_at_utc=datetime.now(timezone.utc).isoformat(), status='exited')
    CHECKPOINT.write_text(json.dumps(checkpoint, indent=2) + '\n', encoding='utf-8')
    if code == 0:
        print('Publisher completed or stopped at a safe pause; inspect the proof and graph receipts.', flush=True)
        break
    with LOG.open('rb') as log:
        log.seek(start)
        output = log.read().decode('utf-8', 'replace')
    transient = any(marker in output for marker in (
        'URLError', 'RemoteDisconnected', 'SSLEOFError', 'TimeoutError',
        'ConnectionResetError', 'HTTP 502', 'HTTP 503', 'HTTP 504',
        'User profile not found', '(429,'))
    if not transient:
        print('Publisher needs a source, state, or graph review. It was not blindly restarted.', flush=True)
        sys.exit(code)
    current = read(STATE)
    accepted_after = sum(i.get('proof_status') == 'ACCEPTED' for i in current['items'].values())
    failures = 0 if accepted_after > accepted_before else failures + 1
    if failures >= 6:
        print('Six consecutive network restarts made no proof progress; retained all receipts for review.', flush=True)
        sys.exit(code)
    uncertain_publish = [n for n, i in current['items'].items()
                         if i.get('publish_intent') and not i.get('job_id') and not i.get('theorem_id')]
    if uncertain_publish:
        print('Publication intent needs exact own-job reconciliation:', ', '.join(uncertain_publish), flush=True)
        sys.exit(code)
    # Allow an interrupted server write to settle before own-history readback.
    time.sleep(10)
    uncertain_verify = any(i.get('verify_intent') and not i.get('submission_id') for i in current['items'].values())
    if uncertain_verify:
        result = subprocess.run([sys.executable, str(HERE / 'reconcile_machine_intents.py')],
                                creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
        if result.returncode:
            print('Intent reconciliation did not complete; no mutation was retried.', flush=True)
            sys.exit(result.returncode)
    print('Transient failure reconciled; continuing the same saved queue.', flush=True)
    time.sleep(min(30, 5 * (failures + 1)))
