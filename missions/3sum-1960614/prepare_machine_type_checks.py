"""Prepare native, stub and solution CI type readbacks for exact comparison."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
from machine_skeleton import VER,HERE,ROOT,sha

parser=argparse.ArgumentParser()
parser.add_argument('--model-regression',action='store_true')
parser.add_argument('--scope-regression',action='store_true')
args=parser.parse_args()
assert not (args.model_regression and args.scope_regression)
stem=('machine-scope-regression' if args.scope_regression else
      'machine-regression' if args.model_regression else 'machine-platform')
manifest=json.loads((VER/(stem+'-manifest.json')).read_text(encoding='utf-8'))
inverse={new:old for old,new in manifest['rename_map'].items() if old!=new}
if not (args.model_regression or args.scope_regression):
    # Internal `_auto_` definitions are deliberately omitted by Stage 1.
    # Validate their types and Syntax bodies before approving exact identity
    # relocations; never erase autoParam wrappers or unfold theorem types.
    result=subprocess.run([sys.executable,str(HERE/'audit_machine_auto_companions.py')],cwd=ROOT)
    assert result.returncode==0,'Compiler companion audit failed'
    companions=json.loads((VER/'machine-auto-validation.json').read_text(encoding='utf-8'))
    assert not companions['probe_only'] and companions['all_companion_types_and_bodies_equal']
    assert companions['manifest_sha256']==sha((VER/(stem+'-manifest.json')).read_bytes())
    assert companions['theorem_count']==len(manifest['theorems'])
    for new,old in companions['mapping'].items():
        assert new not in inverse or inverse[new]==old
        inverse[new]=old
(VER/(stem+'-inverse-names.json')).write_text(json.dumps(inverse,indent=2)+'\n',encoding='utf-8')
COMMON='''
open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false
set_option maxRecDepth 10000

private partial def normalizeThreeSumUploadType (names : Std.HashMap Name Name) (expr : Expr) : Expr :=
  match expr with
  | .const name levels => .const ((names.get? name).getD name) levels
  | .app f a => .app (normalizeThreeSumUploadType names f) (normalizeThreeSumUploadType names a)
  | .lam _ type body info => .lam .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names body) info
  | .forallE _ type body info => .forallE .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names body) info
  | .letE _ type value body nondep => .letE .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names value) (normalizeThreeSumUploadType names body) nondep
  | .mdata _ value => normalizeThreeSumUploadType names value
  | .proj name index value => .proj ((names.get? name).getD name) index (normalizeThreeSumUploadType names value)
  | other => other

run_meta do
  let mut names : Std.HashMap Name Name := {}
  LOAD_NAMES
  let selected : Array (String × Name) := #[SELECTED]
  let mut records : Array Json := #[]
  for (label, name) in selected do
    let ci ← getConstInfo name
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let original := ci.type.instantiateLevelParams ci.levelParams levels
    let normalized := normalizeThreeSumUploadType names original
    records := records.push <| Json.mkObj [
      ("name",toJson label),("universeCount",toJson ci.levelParams.length),
      ("rawType",toJson (reprStr ci.type)),
      ("printedType",toJson (← Meta.ppExpr ci.type).pretty),
      ("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "OUTPUT" (Json.arr records).pretty
  logInfo s!"recorded {records.size} exact declaration types"
'''
LOAD='''let raw ← IO.FS.readFile "missions/3sum-1960614/verification/INVERSE"
  let json ← match Json.parse raw with
    | .ok value => pure value
    | .error message => throwError message
  let object ← match json.getObj? with
    | .ok value => pure value
    | .error message => throwError message
  for (new,old) in object.toArray do
    let original ← match old.getStr? with
      | .ok value => pure value
      | .error message => throwError message
    names := names.insert new.toName original.toName
'''.replace('INVERSE',stem+'-inverse-names.json')
checks=[]

def prepare(label,imports,pairs,platform):
    target=stem+'-types-'+label
    output='missions/3sum-1960614/verification/'+target+'.json'
    selected=', '.join('('+json.dumps(old)+', `'+new+')' for old,new in pairs)
    body=COMMON.replace('LOAD_NAMES',LOAD if platform else 'pure ()').replace('SELECTED',selected).replace('OUTPUT',output)
    code='\n'.join('import '+m for m in imports)+'\n'+body
    path=VER/(target+'.lean')
    path.write_text(code,encoding='utf-8',newline='\n')
    checks.append({'label':label,'path':path.name,'output':target+'.json','declaration_count':len(pairs)})

native_imports=(sorted({t['original_module'] for t in manifest['theorems']}) if args.scope_regression else
                ['Submission.ThreeSum.ModelWitnessBounds' if args.model_regression else 'Submission.ThreeSum.CompleteCostBridge'])
prepare('native',native_imports,[(t['original_decl'],t['original_decl']) for t in manifest['theorems']],False)
prepare('stubs',[t['theorem_module'] for t in manifest['theorems']],[(t['original_decl'],t['name']) for t in manifest['theorems']],True)
for i,theorem in enumerate(manifest['theorems']):
    prepare('solution-'+str(i),[theorem['solution_module']],[(theorem['original_decl'],'solution')],True)
(VER/(stem+'-type-checks.json')).write_text(json.dumps(checks,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(checks),'separate CI snapshots, with an explicit inverse relocation map.')
