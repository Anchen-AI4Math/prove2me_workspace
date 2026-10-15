"""Read solution CI types from successfully built .olean artifacts in one pass.

Lean's ModuleData is authoritative compiled ConstantInfo. Keeping solutions
out of the imported environment avoids collisions between their root names
`solution`; their types can still be pretty-printed in the common stub/Def
environment. This does not execute solution modules or alter upload code.
"""
import argparse
import json
from pathlib import Path
from machine_skeleton import ROOT,VER,sha
from prepare_machine_type_checks import COMMON,LOAD

# The imported preparer has already parsed the identical regression switches.
parser=argparse.ArgumentParser()
parser.add_argument('--model-regression',action='store_true')
parser.add_argument('--scope-regression',action='store_true')
args=parser.parse_args()
stem=('machine-scope-regression' if args.scope_regression else
      'machine-regression' if args.model_regression else 'machine-platform')
manifest_path=VER/(stem+'-manifest.json')
manifest=json.loads(manifest_path.read_text(encoding='utf-8'))
inputs=[]
for theorem in manifest['theorems']:
    artifact=ROOT/'.lake/build/lib/lean'/Path(*theorem['solution_module'].split('.')).with_suffix('.olean')
    assert artifact.is_file(),artifact
    assert sha((ROOT/theorem['solution_path']).read_bytes())==theorem['solution_sha256']
    inputs.append({'name':theorem['original_decl'],'module':theorem['solution_module'],
                   'path':artifact.as_posix(),'artifact_sha256':sha(artifact.read_bytes()),
                   'solution_sha256':theorem['solution_sha256']})
input_name=stem+'-compiled-solution-inputs.json'
(VER/input_name).write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
code='\n'.join('import '+t['theorem_module'] for t in manifest['theorems'])+'\n'
code+=COMMON.split('run_meta do',1)[0]
body='''run_meta do
  let mut names : Std.HashMap Name Name := {}
  LOAD_NAMES
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/INPUTS"
  let items ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut records : Array Json := #[]
  let mut retainedRegions : Array CompactedRegion := #[]
  for item in items do
    let label ← match item.getObjValAs? String "name" with
      | .ok value => pure value
      | .error message => throwError message
    let path ← match item.getObjValAs? String "path" with
      | .ok value => pure value
      | .error message => throwError message
    let (data,region) ← readModuleData path
    retainedRegions := retainedRegions.push region
    let candidates := data.constants.filter (fun ci => ci.name == `solution)
    unless candidates.size == 1 do
      throwError "Expected exactly one root solution CI in {path}; got {candidates.size}"
    let ci := candidates[0]!
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let original := ci.type.instantiateLevelParams ci.levelParams levels
    let normalized := normalizeThreeSumUploadType names original
    records := records.push <| Json.mkObj [
      ("name",toJson label),("universeCount",toJson ci.levelParams.length),
      ("rawType",toJson (reprStr ci.type)),
      ("printedType",toJson (← Meta.ppExpr ci.type).pretty),
      ("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/OUTPUT" (Json.arr records).pretty
  logInfo s!"recorded {records.size} compiled solution CI types; retained {retainedRegions.size} regions"
'''
code+=body.replace('LOAD_NAMES',LOAD).replace('INPUTS',input_name).replace('OUTPUT',stem+'-types-compiled-solutions.json')
(VER/(stem+'-types-compiled-solutions.lean')).write_text(code,encoding='utf-8',newline='\n')
print('Prepared one-pass compiled CI readback for',len(inputs),'exact solution artifacts.')
