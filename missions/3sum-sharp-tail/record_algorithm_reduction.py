"""Read and retain the original algorithm reduction's fresh verification verdict."""
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('publisher', HERE / 'publish_bridge_nodes.py')
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)
target = HERE / 'verification/algorithm-bridge-submission.json'
record = json.loads(target.read_text(encoding='utf-8'))
verdict = publisher.api('GET', '/verify?submission_id=' + record['submission_id'])
assert verdict['theorem_id'] == record['theorem_id']
record.update(status=verdict['status'], verdict=verdict)
target.write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Algorithm reduction: ' + verdict['status'])
if verdict.get('error_message'):
    print(verdict['error_message'])
