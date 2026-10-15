"""Port the concrete expansion-232 local prime/bucket definitions and proofs."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=HERE/'verification/upstream/Submission/ThreeSum'
DST=HERE/'machine/lean/Submission/ThreeSum'
records={}
for name in ['LayerCounts','LocalCoverBounds']:
    original=(SRC/(name+'.lean')).read_bytes()
    code=original.decode('utf-8-sig').replace('\r\n','\n')
    changes=[]
    if name=='LocalCoverBounds':
        changes=['local universe 512h -> 464h','local expansion 256 -> 232']
        code=code.replace('512','464').replace('256','232')
    path=DST/(name+'.lean')
    if path.exists():
        assert path.read_text(encoding='utf-8')==code, 'Preserve edited port: '+str(path)
    else:
        path.write_bytes(code.encode('utf-8'))
    records[name]={'upstream_sha256':hashlib.sha256(original).hexdigest(),
      'port_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'changes':changes,
      'path':path.relative_to(ROOT).as_posix()}
(HERE/'verification/cover-port-manifest.json').write_text(json.dumps({
    'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0','modules':records},indent=2)+'\n',encoding='utf-8')
print('Prepared concrete local prime and bucket port at expansion 232; compilation required.')
