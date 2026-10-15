"""Pure single-pass AP16 snapshot, reusing the genuine unchanged mirror OLean."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_clearing_child_mirror as original
import validate_namespace_context_providers as context
parent=original.parent
TASK,ROOT,V=parent.TASK,parent.ROOT,parent.V
SELF=Path(__file__).resolve()
STAGE=V/'ap16/clearing-child-mirror-probe-v2'
EMITTER_STAGE=original.STAGE
MODULE,OUTPUT,SNAPSHOT=original.MODULE,original.OUTPUT,original.SNAPSHOT
TYPE_JSON,REFS_JSON,MAPPING_JSON=original.TYPE_JSON,original.REFS_JSON,original.MAPPING_JSON
CERTIFICATE=original.CERTIFICATE
ACCEPTED=EMITTER_STAGE/'accepted-publication-record.json'
RUNNER=TASK/'scripts/preflight_staged_module_windows_bounded.py'
LEGACY_RUNNER=TASK/'scripts/preflight_staged_module.py'
CONSUMER=TASK/'scripts/certify_selected_minor_clearing_child_mirror_probe_v2.py'
read,sha,sha_bytes,encode,need,rel=parent.read,parent.sha,parent.sha_bytes,parent.encode,parent.need,parent.rel
EXPECTED_OLEAN='d75dcfab33165c6e89c750fa8220fd1e32b6d0f1f8b9484fdc9eb04896485e93'

RESOLVER=r'''
namespace ClearingPrivateMirrorSnapshot
open Lean Meta FullRowMinorProofSnapshot

def resolveRoots (helpers : Array Name) (target : Name) (equations : Array Name)
    (moduleName output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? target
    | throwError "Original clearing target has no imported module owner"
  unless env.header.moduleNames[moduleIndex.toNat]?.map Name.toString == some moduleName &&
      (Lean.privateToUserName? target).isNone do
    throwError "Original clearing target is not the exact public source theorem"
  for userName in helpers do
    unless (env.find? userName).isNone do
      throwError "Original helper unexpectedly has a public kernel binding: {userName}"
  let mut candidates : Array (Name × Name) := #[]
  let mut publicNames : Array Name := #[]
  -- One environment traversal. Ownership is filtered by the exact module index
  -- before private user-name decoding or any effectful owner export.
  for (actualName, _) in env.constants.toList do
    if env.getModuleIdxFor? actualName == some moduleIndex then
      match Lean.privateToUserName? actualName with
      | some userName =>
          if helpers.contains userName then
            candidates := candidates.push (userName, actualName)
      | none => publicNames := publicNames.push actualName
  let mut resolved : Array Name := #[]
  let mut mapping : Array Json := #[]
  for userName in helpers do
    let found := candidates.filter (fun pair => pair.1 == userName)
    unless found.size == 1 do
      throwError "Exact actual private name/module binding is missing or ambiguous: {userName}"
    let actualName := found[0]!.2
    let some ci := env.find? actualName | throwError "Actual private CI is absent"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Private original helper is not a theorem"
    resolved := resolved.push actualName
    mapping := mapping.push <| Json.mkObj [
      ("sourceName",toJson userName.toString),("actualName",toJson actualName.toString),
      ("privateUserName",toJson ((Lean.privateToUserName? actualName).map Name.toString)),
      ("owner",← ownerOf env actualName)]
  publicNames := publicNames.qsort (fun a b => a.toString < b.toString)
  for n in publicNames do
    unless n == target || equations.contains n do
      throwError "Local mirror exports an unintended public CI: {n}"
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),("mapping",Json.arr mapping),
    ("publicTarget",toJson target.toString),("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("officialDataEquationCandidates",toJson (equations.map Name.toString))]).compress
  return resolved.push target ++ equations
end ClearingPrivateMirrorSnapshot
'''

def stage_files():
    original.check_only()
    emitter=context.record(EMITTER_STAGE/OUTPUT,EMITTER_STAGE/'c1.json','emit-olean',MODULE,EMITTER_STAGE)
    e=emitter['data'];need(e['success'] is True and e['timed_out'] is False and 0<e['seconds']<=300,'Genuine original mirror emitter did not pass bounded preflight')
    olean=context.file(e['output_olean']);need(e['output_olean_sha256']==sha(olean)==EXPECTED_OLEAN,'Original unchanged proof OLean differs')
    need(not (EMITTER_STAGE/SNAPSHOT).with_suffix('.lean.preflight.json').exists(),'Failed v1 probe unexpectedly has a completed preflight record')
    interruption=EMITTER_STAGE/'interrupted-probe-record.json';need(interruption.is_file(),'Root interruption evidence is missing')
    raw=(EMITTER_STAGE/SNAPSHOT).read_bytes()
    anchor=original.PRIVATE_RESOLVER.encode();need(raw.count(anchor)==1,'Frozen private resolver anchor differs')
    probe=raw.replace(anchor,RESOLVER.encode(),1).replace(parent.workspace_rel(EMITTER_STAGE).encode(),parent.workspace_rel(STAGE).encode())
    need(probe.count(b'env.constants.toList')==1 and b'resolvePrivate' not in probe,'Optimized exact private resolver is not single-pass')
    p=read(EMITTER_STAGE/'preparation.json');inputs=dict(p['input_hashes'])
    paths=[SELF,CONSUMER,RUNNER,LEGACY_RUNNER,original.SELF,EMITTER_STAGE/'preparation.json',EMITTER_STAGE/'c1.json',EMITTER_STAGE/OUTPUT,(EMITTER_STAGE/OUTPUT).with_suffix('.lean.preflight.json'),EMITTER_STAGE/'c2.json',EMITTER_STAGE/SNAPSHOT,interruption,context.file(e['log']),olean]
    # Partial v1 equation files are retained as failed-attempt evidence only.
    # All certified equation/type/ref outputs must be written afresh by v2.
    paths += sorted(EMITTER_STAGE.glob('generated-equation-*.json'))
    for path in paths:inputs[rel(path)]=sha(path)
    command='python scripts/preflight_staged_module_windows_bounded.py ap16/clearing-child-mirror-probe-v2/GeneratedSnapshot.lean --root ap16/clearing-child-mirror-probe-v2 --imports-manifest ap16/clearing-child-mirror-probe-v2/c2.json --timeout-seconds 300'
    manifest={'schema_version':1,'artifact_kind':'ap16-private-clearing-child-single-pass-probe-v2-manifest','output':parent.workspace_rel(STAGE/SNAPSHOT),'output_sha256':sha_bytes(probe),'imports':['Lean',MODULE],'input_hashes':inputs,'runtime_sha256':sha(parent.RUNTIME),'mode':'modecheck','emit_olean':False,'timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'reused_emitter_preflight':emitter['record'],'reused_emitter_preflight_sha256':emitter['record_sha256'],'reused_olean_sha256':EXPECTED_OLEAN,'validated':False,'submission_ready':False}
    prep=dict(p);prep.update({'artifact_kind':'ap16-private-clearing-child-single-pass-probe-v2-preparation','input_hashes':inputs,'reused_emitter_root':rel(EMITTER_STAGE),'reused_emitter_preflight':emitter['record'],'reused_emitter_preflight_sha256':emitter['record_sha256'],'reused_olean_sha256':EXPECTED_OLEAN,'failed_v1_probe_record':rel(interruption),'failed_v1_probe_record_sha256':sha(interruption),'failed_v1_partial_JSON_not_certified':True,'private_name_inventory_environment_traversals':1,'proof_source_and_OLean_unchanged':True,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'commands':[command]})
    return {SNAPSHOT:probe,'c2.json':encode(manifest),'preparation.json':encode(prep),'compile-commands.txt':(command+'\n').encode()}

def check_only():
    outputs=stage_files()
    for filename,raw in outputs.items():need((STAGE/filename).read_bytes()==raw,'Immutable probe-v2 staging differs: '+filename)
    manifest=read(STAGE/'c2.json');parent.base.runner.verify_manifest_inputs(manifest);parent.base.runner.verify_source_certificate(STAGE/SNAPSHOT,manifest)
    return {'checked_files':len(outputs),'reused_genuine_emitter_olean_sha256':EXPECTED_OLEAN,'one_pass_private_inventory':True,'proof_bytes_unchanged':True,'validated':False,'Lean_started':False,'API_used':False}

def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');args=parser.parse_args()
    if args.prepare:
        for filename,raw in stage_files().items():
            path=STAGE/filename
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite probe-v2 artifact: '+filename)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),indent=2))
if __name__=='__main__':main()
