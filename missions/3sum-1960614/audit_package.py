"""Reproduce source certificates without modifying the supplied research package."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SOURCE = Path('D:/users/self_projects/math_discovery/3 SUM/3sum_certificate_1p960614_v3/3sum_certificate_v3')
OUT = HERE / 'verification'
OUT.mkdir(exist_ok=True)
env = os.environ.copy()
env['PYTHONDONTWRITEBYTECODE'] = '1'
result = subprocess.run([sys.executable, str(SOURCE / 'verify_certificate.py'), '--self-test'],
                        cwd=SOURCE, env=env, capture_output=True, text=True)
(OUT / 'certificate-check.txt').write_text(result.stdout + result.stderr, encoding='utf-8')
hashes = {p.relative_to(SOURCE).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in SOURCE.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
mismatches = []
for line in (SOURCE / 'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    expected, name = line.split(maxsplit=1)
    name = name.lstrip('*')
    if hashes.get(name) != expected.lower():
        mismatches.append(name)
record = dict(exit_code=result.returncode, source_hashes=hashes, hash_mismatches=mismatches,
              certificates_passed=result.stdout.count('CERTIFICATE PASS:'),
              negative_tests_passed=result.stdout.count('PASS rejection test:'),
              scope='Analytic, parametric-cost and fixed-model certificates; no complete machine theorem')
(OUT / 'source-audit.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
assert result.returncode == 0 and record['certificates_passed'] == 3
assert record['negative_tests_passed'] == 12 and not mismatches
print(json.dumps({k: v for k, v in record.items() if k != 'source_hashes'}))
