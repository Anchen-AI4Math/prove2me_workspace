"""Copy only the actual schedule's generic dependency modules from the pin."""
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=HERE/'verification/upstream/Submission/ThreeSum'
DST=HERE/'machine/lean/Submission/ThreeSum'
records={}
for name in ['BinomialEntropy','Asymptotics','PrimeDensity','Scales']:
    original=(SRC/(name+'.lean')).read_bytes()
    code=original.decode('utf-8-sig').replace('\r\n','\n')
    changes=[]
    if name in ['BinomialEntropy','Scales']:
        code=code.replace('512','464').replace('511','463').replace('256','232')
        changes=['local/output universe 512/256 -> 464/232','degree universe 511 -> 463']
    path=DST/(name+'.lean')
    if not path.exists():
        path.write_bytes(code.encode('utf-8'))
    records[name]={'upstream_sha256':hashlib.sha256(original).hexdigest(),
      'initial_changes':changes,'path':path.relative_to(ROOT).as_posix(),
      'current_port_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
(HERE/'verification/scales-port-manifest.json').write_text(json.dumps({
    'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0','modules':records},indent=2)+'\n',encoding='utf-8')
print('Prepared actual schedule dependency modules; rational schedule and rate proofs require adaptation.')
