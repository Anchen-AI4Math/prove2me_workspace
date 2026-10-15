"""Extend an explicitly selected machine import closure; never overwrite edits."""
import hashlib
import json
from pathlib import Path
import re
import sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=HERE/'verification/upstream'
DST=HERE/'machine/lean'
assert len(sys.argv)>1,'Supply actual machine root modules'
pending=sys.argv[1:]
assert all(re.fullmatch(r'Submission(?:\.[A-Za-z_][A-Za-z0-9_]*)+',m) for m in pending)
statepath=HERE/'verification/algorithm-port-manifest.json'
state=json.loads(statepath.read_text(encoding='utf-8')) if statepath.exists() else {
 'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0','roots':[],'modules':{}}
state['roots']=sorted(set(state['roots']+pending))
visited=set()
count=0
while pending:
    module=pending.pop()
    if module in visited: continue
    visited.add(module)
    rel=Path(*module.split('.')).with_suffix('.lean')
    source=SRC/rel
    assert source.resolve().is_relative_to(SRC.resolve())
    out=DST/rel
    assert out.resolve().is_relative_to(DST.resolve())
    original=source.read_bytes() if source.exists() else None
    assert original is not None or out.exists(), 'Missing source for '+module
    if not out.exists():
        code=original.decode('utf-8-sig').replace('\r\n','\n')
        # Cover constants change only in modules containing a concrete
        # universe/support dimension. Generic arithmetic constants such as
        # 256 = 2^8 must survive unchanged.
        dimension_module=bool(re.search(
            r'\b512\s*\*\s*(?:h\b|Scales\.microHalf|half\b|microHalf\b)|'
            r'\b256\s*\*\s*(?:mu\b|muZero\b|residualSize\b|Scales\.muZero\b)',code))
        dimension_module=dimension_module or module=='Submission.ThreeSum.BinomialEntropy'
        if dimension_module:
            for before,after in [('512','464'),('256','232')]:
                code=re.sub(r'\b'+before+r'\b',after,code)
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_bytes(code.encode('utf-8'))
        count+=1
    code=out.read_text(encoding='utf-8')
    state['modules'][module]={'upstream_sha256':hashlib.sha256(original).hexdigest() if original is not None else None,
      'port_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'path':out.relative_to(ROOT).as_posix()}
    for imports in re.findall(r'^(?:public\s+)?import\s+([^\r\n]+)',code,re.M):
        pending.extend(x for x in imports.split('--',1)[0].split() if x.startswith('Submission.'))
statepath.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
print('Selected import closure:',len(visited),'modules;',count,'new sources. Existing edits preserved.')
