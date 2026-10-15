"""Read three already-built loop interfaces early; never seal main gates."""
import ast
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
digest=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
manifest_path=VER/'machine-platform-manifest.json'
manifest=json.loads(manifest_path.read_text(encoding='utf-8'))
companions=json.loads((VER/'machine-auto-early-validation.json').read_text(encoding='utf-8'))
assert companions['all_companion_types_and_bodies_equal'] and companions['probe_only']
assert companions['manifest_sha256']==digest(manifest_path)
inverse={new:old for old,new in manifest['rename_map'].items() if old!=new}
inverse.update(companions['mapping'])
(VER/'machine-early-inverse-names.json').write_text(json.dumps(inverse)+'\n',encoding='utf-8')
selected_names={'Light.Ends.for','Light.Ends.of_blockSafe','Light.Ends.while'}
selected=[t for t in manifest['theorems'] if t['original_decl'] in selected_names]
assert len(selected)==3
assert not manifest['validation_complete']
inputs=[]
for theorem in selected:
    artifact=ROOT/'.lake/build/lib/lean'/Path(*theorem['solution_module'].split('.')).with_suffix('.olean')
    assert artifact.stat().st_mtime>manifest_path.stat().st_mtime,'Only current-build artifacts may be probed'
    assert digest(ROOT/theorem['solution_path'])==theorem['solution_sha256']
    inputs.append({'name':theorem['original_decl'],'staged_name':theorem['name'],
                   'path':artifact.as_posix(),'sha256':digest(artifact)})
(VER/'machine-early-type-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')

def literal_assignment(path,target):
    tree=ast.parse(path.read_text(encoding='utf-8'))
    return next(ast.literal_eval(node.value) for node in tree.body if isinstance(node,ast.Assign)
                and any(isinstance(t,ast.Name) and t.id==target for t in node.targets))

common=literal_assignment(HERE/'prepare_machine_type_checks.py','COMMON')
body=literal_assignment(HERE/'prepare_batch_solution_types.py','body')
load='''let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-early-inverse-names.json"
  let object ← ofExcept (Json.parse raw >>= Json.getObj?)
  for (new,old) in object.toArray do
    let original ← ofExcept old.getStr?
    names := names.insert new.toName original.toName
'''
code='\n'.join('import '+t['theorem_module'] for t in selected)+'\n'+common.split('run_meta do',1)[0]
code+=body.replace('LOAD_NAMES',load).replace('INPUTS','machine-early-type-inputs.json').replace('OUTPUT','machine-early-solution-types.json')
# The stub type is read in this same environment, independently of the
# compiled solution CI. Native CIs were previously extracted from the frozen
# complete native proof and remain untouched by this probe.
code+='''
run_meta do
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-early-inverse-names.json"
  let object ← ofExcept (Json.parse raw >>= Json.getObj?)
  let mut names : Std.HashMap Name Name := {}
  for (new,old) in object.toArray do
    let original ← ofExcept old.getStr?
    names := names.insert new.toName original.toName
  let mut records := #[]
  for (label,name) in #[SELECTED] do
    let ci ← getConstInfo name
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let normalized := normalizeThreeSumUploadType names (ci.type.instantiateLevelParams ci.levelParams levels)
    records := records.push <| Json.mkObj [("name",toJson label),
      ("universeCount",toJson ci.levelParams.length),("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-early-stub-types.json" (Json.arr records).pretty
'''.replace('SELECTED',', '.join('('+json.dumps(t['original_decl'])+', `'+t['name']+')' for t in selected))
path=VER/'machine-early-types.lean'
path.write_text(code,encoding='utf-8')
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
lake=Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe'
with (VER/'machine-early-types.txt').open('w',encoding='utf-8') as handle:
    result=subprocess.run([str(lake),'env','lean',str(path)],cwd=ROOT,env=env,stdout=handle,stderr=subprocess.STDOUT)
assert result.returncode==0,'Early probe failed; inspect machine-early-types.txt'
native={r['name']:r for r in json.loads((VER/'machine-platform-types-native.json').read_text(encoding='utf-8'))}
differences=[]
for side in ['solution','stub']:
    rows=json.loads((VER/('machine-early-'+side+'-types.json')).read_text(encoding='utf-8'))
    for row in rows:
        for key in ['universeCount','normalizedType']:
            if row[key]!=native[row['name']][key]:
                differences.append({'name':row['name'],'side':side,'key':key,'native':native[row['name']][key],'staged':row[key]})
for item in inputs:assert digest(Path(item['path']))==item['sha256']
receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'probe_only':True,
         'manifest_sha256':digest(manifest_path),'count':3,'differences':differences,
         'full_490_node_gate_passed':False,'inputs':inputs}
(VER/'machine-early-type-validation.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
assert not differences,'Early exact type differences found'
print('Three current-build loop solution and stub CIs match frozen native types; full gate remains pending.',flush=True)
