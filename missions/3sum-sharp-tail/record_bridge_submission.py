"""Read a bridge submission's fresh verdict and store it with its published node."""
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
    suffix, submission_id = sys.argv[1:]
    state = json.loads(publisher.STATE.read_text(encoding='utf-8'))
    result = publisher.api('GET', '/verify?submission_id=' + submission_id)
    assert result['theorem_id'] == state[suffix]['theorem_id']
    assert result['id'] == submission_id
    (HERE / 'verification' / (suffix + '-verdict.json')).write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    state[suffix].update(proof_submission_id=submission_id, proof_status=result['status'])
    publisher.save(state)
    print(suffix + ': ' + result['status'])
    if result.get('error_message'):
        print(result['error_message'])


if __name__ == '__main__':
    main()
