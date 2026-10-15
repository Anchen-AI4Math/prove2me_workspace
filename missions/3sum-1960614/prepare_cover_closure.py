"""Extend the mutable machine port through the actual finite cover modules."""
import hashlib
import json
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=HERE/'verification/upstream'
DST=HERE/'machine/lean'
pending=['Submission.ThreeSum.LocalHashMoments','Submission.ThreeSum.TrimScales',
         'Submission.ThreeSum.BandScales']
records={}
while pending:
    module=pending.pop()
    if module in records:
        continue
    rel=Path(*module.split('.')).with_suffix('.lean')
    source=SRC/rel
    original=source.read_bytes()
    out=DST/rel
    copied=False
    if not out.exists():
        code=original.decode('utf-8-sig').replace('\r\n','\n')
        for before,after in [('514','466'),('512','464'),('511','463'),('256','232')]:
            code=re.sub(r'\b'+before+r'\b',after,code)
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_bytes(code.encode('utf-8'))
        copied=True
    code=out.read_text(encoding='utf-8')
    records[module]={'upstream_sha256':hashlib.sha256(original).hexdigest(),
      'port_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'newly_copied':copied,
      'path':out.relative_to(ROOT).as_posix()}
    for imports in re.findall(r'^(?:public\s+)?import\s+([^\r\n]+)',code,re.M):
        pending.extend(x for x in imports.split('--',1)[0].split() if x.startswith('Submission.'))
(HERE/'verification/cover-closure-manifest.json').write_text(json.dumps({
    'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0','modules':records},indent=2)+'\n',encoding='utf-8')
print('Finite cover closure:',len(records),'modules;',sum(r['newly_copied'] for r in records.values()),'new sources. Existing edits preserved.')
