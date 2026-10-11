"""Fetch only matching official API docs; no credentials or workspace update."""
import hashlib
import json
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / 'formalization/platform/readback-2026-10-04/api-docs-v0.11.8'
BASE = 'https://raw.githubusercontent.com/prove2me/prove2me_workspace/v0.11.8/'
NAMES = ['SKILL.md', 'references/mission_captain.md', 'references/missions.md',
         'references/prove.md', 'references/contribute.md']

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    receipt = {'checked_at': datetime.now(timezone.utc).isoformat(),
               'version': '0.11.8', 'files': []}
    for name in NAMES:
        url = BASE + name
        with urllib.request.urlopen(url, timeout=40) as response:
            data = response.read()
        if name == 'SKILL.md':
            assert 'version: "0.11.8"' in data.decode('utf-8')
        target = OUT / name
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert target.read_bytes() == data, 'Refusing to replace saved docs'
        else:
            target.write_bytes(data)
        receipt['files'].append({'path': name, 'url': url, 'bytes': len(data),
                                 'sha256': hashlib.sha256(data).hexdigest()})
    (OUT / 'download-receipt.json').write_text(
        json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(receipt))

if __name__ == '__main__':
    main()
