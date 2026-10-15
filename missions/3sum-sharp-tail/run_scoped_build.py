"""Run the registered 3SUM build with one Lean worker and preserve its result."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VERIFY = HERE / 'verification'

def main():
    command = [sys.executable, '-X', 'utf8', str(ROOT / 'scripts/workspace.py'),
               'build', '3sum-sharp-tail']
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    files = sorted((ROOT / 'Solutions').glob('Sol_ThreeSumSharpTail_*.lean'))
    before = {str(p.relative_to(ROOT)).replace('\\','/'):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    started = datetime.now(timezone.utc).isoformat()
    with (VERIFY / 'scoped-build.txt').open('w', encoding='utf-8') as log:
        run = subprocess.Popen(command, cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding='utf-8', errors='replace', bufsize=1)
        for line in run.stdout:
            log.write(line)
            log.flush()
            if any(marker in line for marker in
                    ('selected root modules', 'error:', 'error(', 'Build completed',
                     'Build failed', 'Failed to build', '✔ [', '✖ [')):
                print(line, end='', flush=True)
        code = run.wait()
    after = {str(p.relative_to(ROOT)).replace('\\','/'):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    result = {'command': command, 'LEAN_NUM_THREADS': '1', 'started_at_utc': started,
        'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'exit_code': code,
        'solution_raw_sha256': after, 'sources_unchanged_during_build': before == after,
        'log': 'scoped-build.txt'}
    (VERIFY / 'scoped-build.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print('Scoped build exit ' + str(code), flush=True)
    return code if before == after else 1

if __name__ == '__main__':
    raise SystemExit(main())
