"""Make exact closed mirrors of accepted solutions for independent axiom checks."""
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
proofs=json.loads((VER/'proof-status.json').read_text(encoding='utf-8'))
DEST=HERE/'machine/lean/Closed3Sum'
DEST.mkdir(parents=True,exist_ok=True)
imports='''import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Max
import Mathlib.Tactic'''
definitions=HERE/'machine/lean/Submission/ThreeSum'
analysis=(ROOT/'Definitions/Def_ThreeSum1960614_Analysis.lean').read_text(encoding='utf-8')
assert analysis.startswith('import Mathlib\n')
(definitions/'AnalysisDefinitions.lean').write_bytes(analysis.replace('import Mathlib',imports,1).encode('utf-8'))
scales=(ROOT/'Definitions/Def_ThreeSum1960614_Scales.lean').read_text(encoding='utf-8')
scales=scales.replace('import Definitions.Def_ThreeSum1960614_Analysis','import Submission.ThreeSum.AnalysisDefinitions')
(definitions/'ScaleDefinitions.lean').write_bytes(scales.encode('utf-8'))
closed={k for k,v in proofs.items() if v['status']=='ACCEPTED'}
assert {'quartic_parameter_certificate','integer_schedule','executable_scale_rounding','executable_scale_limits'} <= closed
records={}
for key in sorted(closed):
    theorem=json.loads((VER/('ThreeSum1960614_'+key+'-current.json')).read_text(encoding='utf-8'))
    assert theorem['status']=='Proved'
    original=(ROOT/'Solutions'/('Sol_ThreeSum1960614_'+key+'.lean')).read_text(encoding='utf-8')
    assert 'sorry' not in original and 'axiom ' not in original
    assert original.count('theorem solution')==1
    code=original.replace('theorem solution','theorem ThreeSum1960614.'+key,1)
    code=code.replace('import Definitions.Def_ThreeSum1960614_Analysis','import Submission.ThreeSum.AnalysisDefinitions')
    code=code.replace('import Definitions.Def_ThreeSum1960614_Scales','import Submission.ThreeSum.ScaleDefinitions')
    code=code.replace('#print axioms solution','#print axioms ThreeSum1960614.'+key)
    for dependency in re.findall(r'^import Theorems.Thm_ThreeSum1960614_(\w+)',code,re.M):
        assert dependency in closed, (key,dependency)
        code=code.replace('import Theorems.Thm_ThreeSum1960614_'+dependency,'import Closed3Sum.'+dependency)
    path=DEST/(key+'.lean')
    path.write_bytes(code.replace('\r\n','\n').encode('utf-8'))
    records[key]={'theorem_id':proofs[key]['theorem_id'],
        'accepted_submission_id':proofs[key]['submission_id'],
        'solution_sha256':hashlib.sha256(original.encode('utf-8')).hexdigest(),
        'mirror_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'path':path.relative_to(ROOT).as_posix()}
(VER/'closed-analysis-manifest.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(records),'exact accepted-proof mirrors; kernel axiom build still required.')
