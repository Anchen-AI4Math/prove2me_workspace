"""Validate source-free default-argument companions before adding relocations.

The official graph intentionally omits internal compiler-generated constants.
This supplements only their identities; no source spans or proof cuts change.
"""
import argparse
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
parser=argparse.ArgumentParser()
parser.add_argument('--early',action='store_true')
args=parser.parse_args()
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
manifest_path=VER/'machine-platform-manifest.json'
manifest=json.loads(manifest_path.read_text(encoding='utf-8'))
stem='machine-auto-early' if args.early else 'machine-auto'
selected=[t for t in manifest['theorems'] if not args.early or t['original_decl'] in
          {'Light.Ends.for','Light.Ends.of_blockSafe','Light.Ends.while'}]
inputs=[]
for t in selected:
    path=ROOT/'.lake/build/lib/lean'/Path(*t['solution_module'].split('.')).with_suffix('.olean')
    assert path.is_file(),path
    assert sha(ROOT/t['solution_path'])==t['solution_sha256']
    inputs.append({'original':t['original_decl'],'stub':t['name'],'implementation':t['solution_implementation'],
                   'path':path.as_posix(),'artifact_sha256':sha(path)})
(VER/(stem+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
base_inverse={new:old for old,new in manifest['rename_map'].items() if old!=new}
(VER/(stem+'-base-inverse.json')).write_text(json.dumps(base_inverse)+'\n',encoding='utf-8')
tree=ast.parse((HERE/'prepare_machine_type_checks.py').read_text(encoding='utf-8'))
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)
            and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
template=r'''
private def requiredString (item : Json) (key : String) : MetaM String :=
  ofExcept (item.getObjValAs? String key)

-- Lean.ToExpr encodes quoted Names with mkStr1..8 or str/num. Decode only
-- these constructors, then apply the exact existing relocation dictionary.
-- This is confined to auditing Syntax-valued compiler defaults, never types.
private partial def quotedName? (e : Expr) : Option Name := do
  let head ← e.getAppFn.constName?
  let args := e.getAppArgs
  if head == ``Lean.Name.anonymous && args.isEmpty then return .anonymous
  if head == ``Lean.Name.str && args.size == 2 then
    let parent ← quotedName? args[0]!
    let .lit (.strVal value) := args[1]! | none
    return .str parent value
  if head == ``Lean.Name.num && args.size == 2 then
    let parent ← quotedName? args[0]!
    let .lit (.natVal value) := args[1]! | none
    return .num parent value
  let heads := #[``Lean.Name.mkStr1, ``Lean.Name.mkStr2, ``Lean.Name.mkStr3,
    ``Lean.Name.mkStr4, ``Lean.Name.mkStr5, ``Lean.Name.mkStr6, ``Lean.Name.mkStr7, ``Lean.Name.mkStr8]
  let some index := heads.findIdx? (fun n => n == head) | none
  unless args.size == index+1 do none
  let mut result := Name.anonymous
  for arg in args do
    let .lit (.strVal value) := arg | none
    result := .str result value
  return result

private partial def normalizeQuotedNames (names : Std.HashMap Name Name) (e : Expr) : Expr :=
  if let some name := quotedName? e then toExpr ((names.get? name).getD name)
  else match e with
    | .app f a => .app (normalizeQuotedNames names f) (normalizeQuotedNames names a)
    | .mdata _ value => normalizeQuotedNames names value
    | other => other

private def companionRecords (names : Std.HashMap Name Name) (label owner : Name)
    (ci : ConstantInfo) (localConstants : Array ConstantInfo) : MetaM (Array Json) := do
  let mut records := #[]
  for name in ci.type.getUsedConstants do
    let .str parent leaf := name | continue
    unless leaf.startsWith "_auto_" do continue
    unless parent == owner do throwError "Unexpected external auto companion {name} in {owner}"
    let generated ← match localConstants.find? (fun c => c.name == name) with
      | some value => pure value
      | none => getConstInfo name
    let .defnInfo info := generated | throwError "Expected a transparent auto-argument definition: {name}"
    unless info.type == mkConst ``Lean.Syntax do throwError "Unexpected auto companion type: {name}"
    let levels := info.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let norm := fun expr => normalizeThreeSumUploadType names (expr.instantiateLevelParams info.levelParams levels)
    records := records.push <| Json.mkObj [
      ("original",toJson (Name.str label leaf).toString),("name",toJson name.toString),
      ("universeCount",toJson info.levelParams.length),
      ("normalizedType",toJson (reprStr (norm info.type))),
      ("normalizedValue",toJson (reprStr (normalizeQuotedNames names (norm info.value))))]
  return records

run_meta do
  let inverseRaw ← IO.FS.readFile "missions/3sum-1960614/verification/STEM-base-inverse.json"
  let inverse ← ofExcept (Json.parse inverseRaw >>= Json.getObj?)
  let mut names : Std.HashMap Name Name := {}
  for (new,old) in inverse.toArray do
    let old ← ofExcept old.getStr?
    names := names.insert new.toName old.toName
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/STEM-inputs.json"
  let items ← ofExcept (Json.parse raw >>= Json.getArr?)
  let mut records := #[]
  let mut retainedRegions : Array CompactedRegion := #[]
  for item in items do
    let original := (← requiredString item "original").toName
    if NATIVE then
      let ci ← getConstInfo original
      records := records ++ (← companionRecords {} original original ci #[])
    else
      let stub := (← requiredString item "stub").toName
      let stubCI ← getConstInfo stub
      records := records ++ (← companionRecords names original stub stubCI #[])
      let path ← requiredString item "path"
      let (data,region) ← readModuleData path
      retainedRegions := retainedRegions.push region
      let some ci := data.constants.find? (fun c => c.name == `solution) | throwError "No solution CI"
      let implementation := (← requiredString item "implementation").toName
      records := records ++ (← companionRecords names original implementation ci data.constants)
  IO.FS.writeFile "missions/3sum-1960614/verification/STEM-SIDE.json" (Json.arr records).pretty
  logInfo s!"Recorded {records.size} source-free auto companions"
'''
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
lake=Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe'
evidence={p.name:sha(p) for p in [Path(__file__),VER/(stem+'-inputs.json'),VER/(stem+'-base-inverse.json')]}
for side in ['native','staged']:
    imports=['Submission.ThreeSum.CompleteCostBridge'] if side=='native' else [t['theorem_module'] for t in selected]
    code='\n'.join('import '+m for m in imports)+'\n'+common.split('run_meta do',1)[0]
    code+=template.replace('STEM',stem).replace('SIDE',side).replace('NATIVE','true' if side=='native' else 'false')
    path=VER/(stem+'-'+side+'.lean');path.write_text(code,encoding='utf-8')
    log=path.with_suffix('.txt')
    with log.open('w',encoding='utf-8') as handle:
        result=subprocess.run([str(lake),'env','lean',str(path)],cwd=ROOT,env=env,stdout=handle,stderr=subprocess.STDOUT)
    assert result.returncode==0,('Companion readback failed',log)
    for artifact in [path,log,VER/(stem+'-'+side+'.json')]:evidence[artifact.name]=sha(artifact)
native={r['original']:r for r in json.loads((VER/(stem+'-native.json')).read_text(encoding='utf-8'))}
staged=json.loads((VER/(stem+'-staged.json')).read_text(encoding='utf-8'))
mapping={};differences=[]
assert {r['original'] for r in staged}==set(native),'Missing companion readback'
assert len(staged)==2*len(native),'Expected independent stub and implementation companions'
for record in staged:
    expected=native[record['original']]
    for key in ['universeCount','normalizedType','normalizedValue']:
        if record[key]!=expected[key]:differences.append({'name':record['name'],'original':record['original'],
                                                          'key':key,'native':expected[key],'staged':record[key]})
    mapping[record['name']]=record['original']
for item in inputs:assert sha(Path(item['path']))==item['artifact_sha256']
receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'manifest_sha256':sha(manifest_path),
         'probe_only':args.early,'theorem_count':len(selected),'native_companions':len(native),
         'staged_companions':len(staged),'mapping':mapping,'differences':differences,
         'all_companion_types_and_bodies_equal':not differences,'evidence_sha256':evidence,
         'body_normalization':'Exact recorded constant and quoted Name relocations; canonical Lean.ToExpr Name constructors. No theorem-type unfolding or simplification.'}
(VER/(stem+'-validation.json')).write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
assert not differences,'Companion body/type mismatch; no relocation approved'
print('Validated',len(mapping),'compiler companion relocations; probe_only =',args.early,flush=True)
