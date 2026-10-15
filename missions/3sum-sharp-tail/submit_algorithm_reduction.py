"""Submit the checked original bridge decomposition using its fresh target ID."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
TARGET = HERE / 'verification/algorithm-bridge-submission.json'
spec = importlib.util.spec_from_file_location('publisher', HERE / 'publish_bridge_nodes.py')
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)


def main():
    if TARGET.exists():
        previous = json.loads(TARGET.read_text(encoding='utf-8'))
        if previous.get('submission_id'):
            print('Existing reduction: ' + previous['submission_id'])
            return
        raise RuntimeError('Inspect the uncertain prior algorithm reduction request')
    snapshot = json.loads((HERE / 'verification/ThreeSumSharpTail_admissible_parameters_solve_3sum-current.json').read_text(encoding='utf-8'))
    theorem = publisher.api('GET', '/theorems/' + snapshot['theorem_id'])
    assert theorem['theorem_name'] == 'ThreeSumSharpTail.admissible_parameters_solve_3sum'
    assert theorem['status'] == 'Open'
    source_path = ROOT / 'Solutions/Sol_ThreeSumSharpTail_admissible_parameters_solve_3sum.lean'
    source = source_path.read_text(encoding='utf-8')
    assert 'by sorry' not in source and source.count('theorem solution') == 1
    fields = {'theorem_id': theorem['theorem_id'], 'proof_type': 'prove',
              'explanation': (HERE / 'verification/algorithm-reduction-explanation.md').read_text(encoding='utf-8')}
    body, ctype = publisher.p2m._multipart(fields, {'file': (source_path.name, source)})
    record = {'theorem_id': theorem['theorem_id'], 'status': 'REQUEST_PREPARED'}
    TARGET.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    status, raw = publisher.p2m._request('POST', '/verify', token=publisher.p2m.get_token(),
                                       raw_body=body, ctype=ctype)
    result = json.loads(raw)
    record.update(response=result, status=result.get('status', 'HTTP_ERROR'))
    if status in (200, 202):
        record['submission_id'] = result['submission_id']
    TARGET.write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    if status not in (200, 202):
        raise RuntimeError(f'HTTP {status}: {raw[:1000]}')
    print('Original algorithm reduction: ' + record['status'] + ' ' + record['submission_id'])


if __name__ == '__main__':
    main()
