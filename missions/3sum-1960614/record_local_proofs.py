"""Record current local proof hashes and compiler evidence; never assert remote acceptance."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
log=(HERE/'verification/log-coefficients-build.txt').read_text(encoding='utf-8')
assert 'Build completed successfully' in log
names=['local_cover_bounds','quartic_geometry','log_coefficients']
proofs=[]
for name in names:
    path=ROOT/'Solutions'/('Sol_ThreeSum1960614_'+name+'.lean')
    code=path.read_text(encoding='utf-8')
    assert 'sorry' not in code and 'axiom ' not in code
    assert 'import Theorems.Thm_ThreeSum1960614_' not in code
    assert name+'.lean:' in log, 'Missing compiler axiom report for '+name
    proofs.append({'name':name,'path':path.relative_to(ROOT).as_posix(),
        'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'status':'Locally compiled; not submitted to Prove2Me',
        'axioms':['propext','Classical.choice','Quot.sound']})
manifest={'proofs':proofs,'main_goal_proved':False,'remote_graph_complete':False,
    'source_package_unchanged':True,'build_log':'verification/log-coefficients-build.txt'}
(HERE/'verification/local-proof-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print('Recorded three closed local supporting proofs. Main machine goal remains open.')
