"""Independent rerun of the recorded finite single-pole experiment."""
from pathlib import Path
import hashlib
import json
import probe_single_pole_pade as m

root=Path(__file__).resolve().parents[1]
source=root/'verification/positive-hankel-2026-09-29/single-pole.json'
data=json.loads(source.read_text())
assert data['script_sha256']==hashlib.sha256((root/'scripts/probe_single_pole_pade.py').read_bytes()).hexdigest()
assert data['moment_dependency_sha256']==hashlib.sha256((root/'scripts/probe_positive_hankel.py').read_bytes()).hexdigest()
counts={3:{'below_one':0,'above_one':0},9:{'below_one':0,'above_one':0}}
for old in data['cases']:
    new=m.case(old['s'],old['pole'],old['dimension'])
    for key in ['integer_constant','integer_slope','positive_scalar']:
        assert old[key]==new[key]
    value=m.arb(new['integer_constant'])+m.arb(new['integer_slope'])*m.arb(new['s']).zeta()
    assert value>0
    assert value<1 or value>1
    counts[new['s']]['below_one' if value<1 else 'above_one']+=1
assert len(data['cases'])==60 and counts[9]['above_one']==30
out={'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
     'cases_recomputed':len(data['cases']),'rigorous_arb_classification':counts,
     'scope':'Finite exact coefficients and signs; uniform affine positivity is proved in the audit note.'}
dest=root/'verification/zenodo-route-audit-2026-09-29/single-pole-review.json'
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
