"""Freeze the existing public bridge's exact reviewed interface before upload."""
import json
from pathlib import Path
from platform import api
from machine_skeleton import Renderer,ROOT,sha

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
NAME='ThreeSum1960614.costs_solve_3sum'
THEOREM_ID='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
expected=next(p for p in json.loads((HERE/'payloads.json').read_text(encoding='utf-8'))
              if p.get('theorem_name')==NAME)
current=api('GET','/theorems/'+THEOREM_ID)
assert current['theorem_name']==NAME
for key in ['preamble','formal_statement']:
    assert current[key]==expected[key],('Reviewed public bridge interface changed',key)
(VER/'machine-frozen-bridge-contract.json').write_text(json.dumps(current,indent=2)+'\n',encoding='utf-8')
code=current['preamble']+'\n\n'+current['formal_statement']+'''

open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

private partial def alphaThreeSumFrozenContract (expr : Expr) : Expr :=
  match expr with
  | .app f a => .app (alphaThreeSumFrozenContract f) (alphaThreeSumFrozenContract a)
  | .lam _ t b i => .lam .anonymous (alphaThreeSumFrozenContract t) (alphaThreeSumFrozenContract b) i
  | .forallE _ t b i => .forallE .anonymous (alphaThreeSumFrozenContract t) (alphaThreeSumFrozenContract b) i
  | .letE _ t v b d => .letE .anonymous (alphaThreeSumFrozenContract t) (alphaThreeSumFrozenContract v) (alphaThreeSumFrozenContract b) d
  | .mdata _ e => alphaThreeSumFrozenContract e
  | .proj n i e => .proj n i (alphaThreeSumFrozenContract e)
  | e => e

run_meta do
  let ci ← getConstInfo `ThreeSum1960614.costs_solve_3sum
  let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
  let normalized := alphaThreeSumFrozenContract (ci.type.instantiateLevelParams ci.levelParams levels)
  let record := Json.mkObj [
    ("name",toJson "ThreeSum1960614.costs_solve_3sum"),
    ("universeCount",toJson ci.levelParams.length),
    ("rawType",toJson (reprStr ci.type)),
    ("printedType",toJson (← Meta.ppExpr ci.type).pretty),
    ("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-frozen-bridge-type.json" record.pretty
  logInfo "Read back the exact reviewed public bridge type"
'''
module='Submission.PaperStatements'
source=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
facts=VER/'sketch-oracles'/(module.replace('.','_')+'.jsonl')
receipt=json.loads(facts.with_suffix('.receipt.json').read_text(encoding='utf-8'))
assert receipt['exit_code']==0 and sha(source.read_bytes())==receipt['source_sha256']
receipt.update(facts_sha256=sha(facts.read_bytes()),
               oracle_input_sha256=sha(source.read_text(encoding='utf-8').encode()))
renderer=Renderer({'units':{},'module_receipts':{module:receipt}})
command=next(c for c in renderer.contexts[module]['commands']
             if c['syntaxKind']=='Lean.Parser.Command.open' and c['opens']
             and c['opens'][0]['variant']=='explicit')
probe=renderer.context_command(module,command,'ThreeSumApsp')
code+='\n/- Actual filtered-open scope transplanted from the pinned source. -/\n'+probe+'''

example : Instr := EndStatement.Instr.accept
#check exec
#check loadWords
'''
(VER/'machine-filtered-open-probe.json').write_text(json.dumps({'source_module':module,
    'source_sha256':receipt['source_sha256'],'official_facts_sha256':receipt['facts_sha256'],
    'parsed_command':command,'generated_scope':probe},indent=2)+'\n',encoding='utf-8')
(VER/'dump_frozen_bridge_contract.lean').write_text(code,encoding='utf-8',newline='\n')
print('Frozen bridge interface matches the original human-reviewed proposal byte for byte.')
