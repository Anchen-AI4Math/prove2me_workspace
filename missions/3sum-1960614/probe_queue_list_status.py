"""Inspect owner-list status schemas for this mission only; no mutations."""
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
from time import perf_counter
from platform import api

VER = Path(__file__).resolve().parent / 'verification'
state = json.loads((VER / 'machine-platform-publish.json').read_text(encoding='utf-8'))
jobs = {i['job_id'] for i in state['items'].values() if i.get('job_id') and not i.get('theorem_id')}
proofs = {i['submission_id'] for i in state['items'].values()
          if i.get('submission_id') and i.get('proof_status') in ('PENDING','RUNNING','VERIFYING','COMPILING')}


def inspect(task):
    kind, path, wanted = task
    start = perf_counter()
    response = api('GET', path)
    key = 'publish_jobs' if kind == 'jobs' else 'submissions'
    rows = response.get(key, [])
    selected = [r for r in rows if r.get('id', r.get('job_id', r.get('submission_id'))) in wanted]
    receipt = {'kind': kind, 'seconds': round(perf_counter()-start, 3),
               'response_keys': list(response), 'row_count': len(rows),
               'wanted_count': len(wanted), 'found_count': len(selected),
               'matching_row_keys': list(selected[0]) if selected else [],
               'matching_records': selected}
    (VER / ('queue-list-' + kind + '-probe.json')).write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in receipt.items() if k!='matching_records'}), flush=True)


with ThreadPoolExecutor(max_workers=2) as pool:
    list(pool.map(inspect, [('jobs','/publish-jobs?limit=100&offset=0',jobs),
                           ('proofs','/submissions?page=1',proofs)]))
