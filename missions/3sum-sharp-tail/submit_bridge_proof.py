"""Submit a checked proof using the theorem ID from its published node record."""
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('publisher', HERE / 'publish_bridge_nodes.py')
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)


def main():
    arguments = sys.argv[1:]
    retry_failed = '--retry-failed' in arguments
    if retry_failed:
        arguments.remove('--retry-failed')
    suffix = arguments[0]
    state = json.loads(publisher.STATE.read_text(encoding='utf-8'))
    record = state[suffix]
    assert record['status'] == 'PUBLISHED' and record['theorem_id']
    if record.get('proof_submission_id'):
        if not retry_failed:
            print('Existing submission: ' + record['proof_submission_id'])
            return
        previous = publisher.api('GET', '/verify?submission_id=' + record['proof_submission_id'])
        assert previous['id'] == record['proof_submission_id']
        assert previous['theorem_id'] == record['theorem_id']
        assert previous['status'] == 'FAILED', previous['status']
        record.setdefault('proof_attempts', []).append(previous)
        record.pop('proof_submission_id')
        record.pop('proof_request_status', None)
        publisher.save(state)
    if record.get('proof_request_status') == 'REQUEST_PREPARED':
        raise RuntimeError('Recover the uncertain prior proof request before retrying')
    path = ROOT / f'Solutions/Sol_ThreeSumSharpTail_{suffix}.lean'
    source = path.read_text(encoding='utf-8')
    assert source.count('theorem solution') == 1
    assert 'by sorry' not in source and 'sorryAx' not in source
    fields = {'theorem_id': record['theorem_id'], 'proof_type': 'prove'}
    if len(arguments) > 1:
        fields['explanation'] = Path(arguments[1]).read_text(encoding='utf-8')
    body, ctype = publisher.p2m._multipart(fields, {'file': (path.name, source)})
    record['proof_request_status'] = 'REQUEST_PREPARED'
    publisher.save(state)
    status, raw = publisher.p2m._request('POST', '/verify', token=publisher.p2m.get_token(),
                                       raw_body=body, ctype=ctype)
    result = json.loads(raw)
    record['proof_response'] = result
    record['proof_request_status'] = 'RECEIVED' if status in (200, 202) else 'HTTP_ERROR'
    if status in (200, 202):
        record.update(proof_submission_id=result['submission_id'], proof_status=result['status'])
    publisher.save(state)
    if status not in (200, 202):
        raise RuntimeError(f'HTTP {status}: {raw[:1000]}')
    print(suffix + ': ' + result['status'] + ' ' + result['submission_id'])


if __name__ == '__main__':
    main()
