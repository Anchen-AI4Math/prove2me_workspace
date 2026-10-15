"""Kernel equality witnesses for the two generated Syntax definition bodies.

Inputs are elaborated Expr values, never substituted source expressions.
Only universe parameter labels are aligned; Lean checks definitional equality.
"""
import json
from pathlib import Path
from textwrap import indent

HERE = Path(__file__).resolve().parent
VER = HERE / 'verification'
snapshots = {}
for side in ('native', 'platform'):
    snapshots[side] = {r['name']: r for r in map(json.loads,
        (VER / f'reuse-interfaces-{side}.jsonl').read_text(encoding='utf-8').splitlines())}

code = '''import Lean
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax

open Lean
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
'''
for i, name in enumerate(('Light.Op.noConfusion', 'Light.instDecidableEqOp')):
    original = snapshots['native'][name]['matcherValue']
    published = snapshots['platform'][name]['matcherValue']
    assert original and published
    code += '\nrun_meta do\n'
    code += '  let originalRaw : Expr := (\n' + indent(original, '    ') + ')\n'
    code += '  let publishedRaw : Expr := (\n' + indent(published, '    ') + ')\n'
    code += f'''  let ci ← getConstInfo `{name}
  let originalParams := (collectLevelParams {{}} originalRaw).params.toList
  let publishedParams := (collectLevelParams {{}} publishedRaw).params.toList
  unless originalParams.length == ci.levelParams.length && publishedParams.length == ci.levelParams.length do
    throwError "Unexpected universe parameter count"
  let original := originalRaw.instantiateLevelParams originalParams (ci.levelParams.map Level.param)
  let published := publishedRaw.instantiateLevelParams publishedParams (ci.levelParams.map Level.param)
  unless (← Meta.isDefEq original published) do
    throwError "Definition bodies are not definitionally equal: {name}"
  let type ← Meta.mkEq original published
  let value ← Meta.mkEqRefl original
  addDecl <| .thmDecl {{
    name := `ThreeSum1960614.ReuseAudit.interface_{i}
    levelParams := ci.levelParams
    type := (← instantiateMVars type)
    value := (← instantiateMVars value) }}
  logInfo "Kernel checked definition-body equality: {name}"

#print axioms ThreeSum1960614.ReuseAudit.interface_{i}
'''

(VER / 'check_reuse_generated_equalities.lean').write_text(code, encoding='utf-8', newline='\n')
print('Prepared two kernel equality witnesses.')
