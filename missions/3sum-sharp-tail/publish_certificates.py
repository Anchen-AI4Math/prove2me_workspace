"""Publish only the two checked logarithm bundles needed by this certificate.

State is recorded before requests; reruns poll recorded jobs, never duplicate
already queued or published declarations. Proof submissions are separate.
"""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
STATE = HERE / 'verification/certificate-nodes.json'
spec = importlib.util.spec_from_file_location('p2m', ROOT / 'scripts/p2m_api.py')
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)

DESCRIPTIONS = {
    'encoding_log_certificate': (
        'Exact rational logarithm enclosures for encoding and baseline entropy',
        'Encloses the natural logarithms of 2, 10, 3, 9, 1/21 and 20/21 between '
        'the exact rational endpoints in the statement. These enclosures certify '
        'the denominator log(4), the encoding cost and H(1/21) in the sharp-tail '
        'parameter certificate. They are obtained by rational atanh partial sums '
        'with explicit remainder bounds and power-of-two argument scaling.'),
    'entropy_log_certificate': (
        'Exact rational logarithm enclosures for the sharp-tail entropy arguments',
        'Encloses the natural logarithms of 44399/1050000, 1005601/1050000, '
        '5601/50000 and 44399/50000 between the exact rational endpoints in the '
        'statement. The first pair describes u=(1-0.11202)/21 and 1-u; the second '
        'describes theta=0.11202 and 1-theta. The bounds certify the sharp saving '
        'and query exponent. The proof reuses the log(2) bounds from the encoding '
        'logarithm certificate to scale all arguments into [1,2].'),
}


def save(state):
    STATE.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def api(method, path, data=None):
    status, raw = p2m._request(method, path, token=p2m.get_token(), data=data)
    if status not in (200, 202):
        raise RuntimeError(f'{method} {path}: HTTP {status}: {raw[:1500]}')
    return json.loads(raw)


def main():
    state = json.loads(STATE.read_text(encoding='utf-8')) if STATE.exists() else {}
    for suffix, (title, description) in DESCRIPTIONS.items():
        name = 'ThreeSumSharpTail.' + suffix
        record = state.setdefault(suffix, {})
        if record.get('status') == 'REQUEST_PREPARED' and not record.get('job_id'):
            raise RuntimeError('Uncertain prior creation for ' + name +
                               '; recover its existing publish job before retrying.')
        if record.get('job_id'):
            job = api('GET', '/publish-jobs/' + record['job_id'])
            record.update(status=job['status'], theorem_id=job.get('theorem_id'), job=job)
            save(state)
            print(name + ': ' + job['status'], flush=True)
            continue
        text = (ROOT / f'Theorems/Thm_ThreeSumSharpTail_{suffix}.lean').read_text(encoding='utf-8')
        marker = 'theorem ' + name
        assert text.count(marker) == 1
        preamble, statement = text.split(marker, 1)
        statement = marker + statement
        payload = {'theorem_name': name, 'theorem_title': title,
                   'formal_statement': statement.strip(), 'preamble': preamble.strip(),
                   'natural_language_statement': description,
                   'source': 'Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time '
                   'via a Sharper Binomial-Tail Analysis (13 October 2026), Section 6.2; '
                   'rational log-series certificate. Derived exact interval enclosures '
                   'for the existing parameter certificate.',
                   'tags': ['3sum', 'entropy', 'exact-certificates', 'logarithms']}
        record.update(status='REQUEST_PREPARED', payload=payload)
        save(state)
        response = api('POST', '/submit-problem',
                       {'problems': [payload], 'env': '0df444a360eaa60ab8c11dca51a86af692955474'})
        record['response'] = response
        assert not response.get('errors'), response
        assert len(response['jobs']) == 1, response
        record.update(job_id=response['jobs'][0]['job_id'], status='PENDING')
        save(state)
        print(name + ': queued ' + record['job_id'], flush=True)


if __name__ == '__main__':
    main()
