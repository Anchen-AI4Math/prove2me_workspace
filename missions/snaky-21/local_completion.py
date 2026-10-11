"""Cache only the fully audited actual proof, tied to all task proof sources."""
import hashlib
import json
import re
from datetime import datetime,timezone
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
STAMP=HERE/'verification'/'local-complete.json'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def hashes():
    paths=list((ROOT/'Solutions'/'Snaky21').glob('*.lean'))
    paths+=list((ROOT/'Definitions').glob('Def_Snaky21*.lean'))
    paths+=[ROOT/'Definitions'/'Def_SnakyTwentyOne.lean',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']
    return {p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

def audited_axioms():
    log=(HERE/'verification'/'closed-build.log').read_text(encoding='utf-8')
    match=re.search(r"'OAI\.Snaky21\.snaky21_complete' depends on axioms: \[([^\]]*)\]",log)
    if not match or 'Build completed successfully' not in log:
        raise RuntimeError('The actual closed proof has not passed its full build and axiom audit')
    axioms={s.strip() for s in match.group(1).split(',') if s.strip()}
    if not axioms<=ALLOWED:
        raise RuntimeError('Unexpected proof axioms: '+str(axioms))
    return sorted(axioms)

def record():
    report={'checked_at':datetime.now(timezone.utc).isoformat(),'axioms':audited_axioms(),'source_sha256':hashes()}
    STAMP.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')

def unchanged():
    if not STAMP.exists():
        return False
    report=json.loads(STAMP.read_text(encoding='utf-8'))
    return report['source_sha256']==hashes() and report['axioms']==audited_axioms()

if __name__=='__main__':
    record()
    print('Recorded the completed actual proof and its standard-axiom audit.')
