"""Stage exact elaborated-type snapshots and the frozen public root check."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
manifest=json.loads((VER/'model-platform-manifest.json').read_text(encoding='utf-8'))
root=next(t for t in manifest['theorems'] if t.get('existing_theorem_id'))
names=[t['name'] for t in manifest['theorems']]
for side in ['native','platform']:
    imported=('Submission.ThreeSum.ModelWitnessBounds' if side=='native' else root['solution_module'])
    pairs=[(n,('solution' if side=='platform' and n==root['name'] else n)) for n in names]
    selected=', '.join('("'+label+'", `'+actual+')' for label,actual in pairs)
    code='import '+imported+'''

open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

run_meta do
  let names : Array (String × Name) := #[SELECTED]
  let mut records : Array Json := #[]
  for (label, name) in names do
    let ci ← getConstInfo name
    records := records.push <| Json.mkObj [
      ("name", toJson label),
      ("levels", toJson (ci.levelParams.map Name.toString)),
      ("printedType", toJson (← Meta.ppExpr ci.type).pretty),
      ("rawType", toJson (reprStr ci.type))]
  IO.FS.writeFile "OUTPUT" (Json.arr records).pretty
  logInfo s!"recorded {records.size} exact declaration types"
'''.replace('SELECTED',selected).replace('OUTPUT',
             'missions/3sum-1960614/verification/model-types-'+side+'.json')
    (VER/('dump_model_types_'+side+'.lean')).write_text(code,encoding='utf-8',newline='\n')
check='import '+root['solution_module']+'''

/- The existing platform root uses the literal rational endpoint. The original
   source uses lowerTarget. This check preserves the frozen public contract
   and proves their definitional equality without importing the target stub. -/
example (e b S th terminal ratio R : ℝ)
    (hmodel : ThreeSum1960614.ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120 / 100000000000 : ℝ) < R :=
  solution e b S th terminal ratio R hmodel
'''
(VER/'check_model_frozen_target.lean').write_text(check,encoding='utf-8',newline='\n')
print('Prepared exact type snapshots and the unchanged frozen-root contract check.')
