"""Batch owner-list status reads, retaining only this mission's exact IDs."""
from concurrent.futures import ThreadPoolExecutor
from platform import api, p2m


def owner_status_reads(items, include_accepted=False):
    jobs = {i['job_id']: i for i in items.values()
            if i.get('job_id') and not i.get('theorem_id') and i.get('publish_status') not in ('FAILED','ERROR')}
    active = (None,'PENDING','RUNNING','VERIFYING','COMPILING','SKETCH_ACCEPTED')
    proofs = {i['submission_id']: i for i in items.values()
              if i.get('submission_id') and (include_accepted or i.get('proof_status') in active)}
    p2m.get_token()  # Refresh once before parallel read-only requests.

    def collect(task):
        kind, wanted = task
        if not wanted:
            return {}
        remaining = set(wanted)
        result = {}
        timestamps = [item.get('publish_intent' if kind=='jobs' else 'verify_intent', {}).get('requested_at_utc')
                      for item in wanted.values()]
        earliest = min((t for t in timestamps if t), default=None)
        page = 1
        while remaining:
            endpoint = ('/publish-jobs?limit=100&offset=' + str((page-1)*100)
                        if kind=='jobs' else '/submissions?page=' + str(page))
            response = api('GET', endpoint)
            rows = response['publish_jobs' if kind=='jobs' else 'submissions']
            for row in rows:
                record_id = row['id']
                if record_id not in remaining:
                    continue
                item = wanted[record_id]
                if kind=='proofs':
                    assert row['theorem_id'] == item['theorem_id']
                path = '/publish-jobs/' + record_id if kind=='jobs' else '/verify?submission_id=' + record_id
                result[path] = row
                remaining.remove(record_id)
            if not rows or page*100 >= response['total']:
                break
            if earliest and min(row['created_at'] for row in rows) < earliest:
                break
            page += 1
        # Missing or unusually old IDs use their authoritative individual GET.
        for record_id in remaining:
            path = '/publish-jobs/' + record_id if kind=='jobs' else '/verify?submission_id=' + record_id
            result[path] = api('GET', path)
        return result

    with ThreadPoolExecutor(max_workers=2) as pool:
        parts = list(pool.map(collect, [('jobs',jobs),('proofs',proofs)]))
    return {path: record for part in parts for path, record in part.items()}
