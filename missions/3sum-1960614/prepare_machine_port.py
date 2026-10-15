"""Copy only the Light scalar dependency closure from the immutable upstream."""
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=HERE/'verification/upstream'
DEST=HERE/'machine/lean'
records={}
pending=['Submission.ThreeSum.LightSwitchScalar']
while pending:
    module=pending.pop()
    if module in records:
        continue
    rel=Path(*module.split('.')).with_suffix('.lean')
    original=(SOURCE/rel).read_bytes()
    code=original.decode('utf-8-sig')
    if module=='Submission.EndStatement':
        shared=(ROOT/'Definitions/Def_TrulySubcubicAPSP_SourceSpecification.lean').read_text(encoding='utf-8-sig')
        assert code.replace('\r\n','\n')==shared.replace('\r\n','\n')
        code='import Definitions.Def_TrulySubcubicAPSP_SourceSpecification\n'
    out=DEST/rel
    out.parent.mkdir(parents=True,exist_ok=True)
    if out.exists():
        assert out.read_text(encoding='utf-8-sig')==code.replace('\r\n','\n'), str(out)
    else:
        out.write_bytes(code.replace('\r\n','\n').encode('utf-8'))
    records[module]={'upstream_sha256':hashlib.sha256(original).hexdigest(),
        'port_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
        'path':out.relative_to(ROOT).as_posix()}
    for imports in re.findall(r'^(?:public\s+)?import\s+([^\r\n]+)',code,re.M):
        pending.extend(x for x in imports.split('--',1)[0].split() if x.startswith('Submission.'))
manifest={'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0',
    'entry':'Submission.ThreeSum.LightSwitchScalar','modules':records,
    'scope':'Light-language scalar safety dependency closure only; no complete solver claim'}
(HERE/'verification/machine-port-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print('Copied',len(records),'required Light scalar modules; immutable source unchanged.')
