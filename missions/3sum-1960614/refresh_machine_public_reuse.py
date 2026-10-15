"""Refresh public statuses and exact source hashes before reuse approval."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
from platform import api

HERE = Path(__file__).resolve().parent
VER = HERE / 'verification'
ROOT = HERE.parents[1]


def save(name, data):
    (VER / name).write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


def catalog(query):
    records, totals, offset = {}, [], 0
    while True:
        page = api('GET', '/theorems?' + query + '&limit=100&offset=' + str(offset))
        totals.append(page['total'])
        for record in page['theorems']:
            records[record['theorem_id']] = record
        offset += len(page['theorems'])
        if offset >= page['total']:
            break
        assert page['theorems'], 'Unexpected empty public catalog page'
    assert len(set(totals)) == 1 and len(records) == totals[0]
    return {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
            'reported_totals': totals, 'records': list(records.values()), 'snapshot_complete': True}


def main():
    if '--cached-catalogs' in sys.argv:
        current = json.loads((VER / 'machine-public-1962-catalog.json').read_text(encoding='utf-8'))
        apsp = json.loads((VER / 'machine-public-apsp-catalog.json').read_text(encoding='utf-8'))
        for snapshot in (current, apsp):
            assert (datetime.now(timezone.utc) - datetime.fromisoformat(snapshot['checked_at_utc'])).total_seconds() < 3600
    else:
        current = catalog('tags=three-sum-1962')
        save('machine-public-1962-catalog.json', current)
        apsp = catalog('q=APSPSource')
        save('machine-public-apsp-catalog.json', apsp)
    providers = {}
    index = json.loads((VER / 'extended-reuse-compact-index.json').read_text(encoding='utf-8'))
    required = {r['module'] for r in index['public'].values()}
    for record in current['records'] + apsp['records']:
        if record['status'] != 'Definition':
            continue
        module = 'Definitions.Def_' + record['theorem_name'].replace('.', '_')
        if module not in required:
            continue
        path = ROOT / Path(*module.split('.')).with_suffix('.lean')
        if not path.exists():
            continue
        public_text = record['definition'].replace('\r\n', '\n')
        local_text = path.read_text(encoding='utf-8')
        assert local_text.rstrip('\n') == public_text.rstrip('\n'), module
        providers[module] = {'module': module, 'theorem_id': record['theorem_id'],
                             'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                             'public_text_sha256': hashlib.sha256(public_text.encode()).hexdigest(),
                             'text_comparison': 'LF newlines; ignore only trailing newline characters',
                             'status': 'Definition', 'checked_at_utc': current['checked_at_utc']}
    save('machine-public-definition-providers.json', providers)
    print('Fresh public catalog:', len(current['records']), '; exact local definition providers:', len(providers), flush=True)
    for theorem_id in ('a53b364e-57a0-4d2c-adc6-983a74218a4b', '7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'):
        record = api('GET', '/theorems/' + theorem_id)
        save('machine-public-current-' + theorem_id + '.json', record)
        print(record['theorem_name'], record['status'], flush=True)


if __name__ == '__main__':
    main()
