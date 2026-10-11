from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib, json, sys, time

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
AUTHOR = TASK / 'formalization/platform/analytic-phase/author-audit.json'
EXPECTED = '463c525179562e32fd3fabac328477908667e296138c6a14b94af7dde7afb211'

def sha(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()

def resolve(row):
    if 'task_relative' in row: return TASK / row['task_relative']
    if 'root_relative' in row: return ROOT / row['root_relative']
    return Path(row['absolute_path'])

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    target = OUT / 'personal-author-complete-binding-rehash.json'
    assert not target.exists(), 'Do not overwrite completed personal rehash'
    assert sha(AUTHOR) == EXPECTED
    report = json.loads(AUTHOR.read_text(encoding='utf-8'))
    assert report['verdict'] == 'PASS' and len(report['stable_files']) == 26180
    grant = json.loads((OUT/'Root-platform-independent-lane2-grant.json').read_text(encoding='utf-8'))
    assert grant['Root_explicit_grant'] and grant['owner'] == 'parameter_author_recovery_1007'
    assert grant['author_report_sha256'] == EXPECTED and grant['lane'] == 2
    start = time.monotonic()
    results = []
    def one(row):
        path = resolve(row)
        actual = dict(bytes=path.stat().st_size, sha256=sha(path))
        return dict(binding=row, observed=actual, exact=actual['bytes']==row['bytes'] and actual['sha256']==row['sha256'])
    with ThreadPoolExecutor(max_workers=2) as pool:
        for i, result in enumerate(pool.map(one, report['stable_files']), 1):
            results.append(result)
            if i % 5000 == 0: print(f'Personal platform author stream rehash {i}/26180', flush=True)
    assert sha(AUTHOR) == EXPECTED
    mismatches = [r for r in results if not r['exact']]
    data = dict(checked_at=datetime.now(timezone.utc).isoformat(), role='Analytic Phase platform INDEPENDENT',
        author_report_sha256=EXPECTED, personally_stream_rehashed_all=True, stable_bindings=len(results),
        total_bytes=sum(r['observed']['bytes'] for r in results), mismatches=len(mismatches),
        elapsed_seconds=round(time.monotonic()-start,3), observations=results,
        Lean_calls=0, API_calls=0, author_objects_not_imported=True)
    target.write_text(json.dumps(data,ensure_ascii=False,separators=(',',':'))+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k!='observations'},indent=2),flush=True)
    assert not mismatches
    print('Personal author rehash report SHA '+sha(target),flush=True)

if __name__ == '__main__': main()
