"""Copy the executable size initializer and its actual language dependencies."""
import hashlib
import json
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=HERE/'verification/upstream'
DST=HERE/'machine/lean'
pending=['Submission.ThreeSum.LightScales']
records={}
while pending:
    module=pending.pop()
    if module in records: continue
    rel=Path(*module.split('.')).with_suffix('.lean')
    original=(SRC/rel).read_bytes()
    out=DST/rel
    if not out.exists():
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_bytes(original.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8'))
    code=out.read_text(encoding='utf-8')
    records[module]={'upstream_sha256':hashlib.sha256(original).hexdigest(),
      'port_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'path':out.relative_to(ROOT).as_posix()}
    for imports in re.findall(r'^(?:public\s+)?import\s+([^\r\n]+)',code,re.M):
        pending.extend(x for x in imports.split('--',1)[0].split() if x.startswith('Submission.'))
(HERE/'verification/initializer-port-manifest.json').write_text(json.dumps({
    'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0','modules':records},indent=2)+'\n',encoding='utf-8')
print('Initializer dependency closure:',len(records),'modules; existing edits preserved.')
