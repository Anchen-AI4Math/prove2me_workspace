"""Pure single-pass AP16 snapshot with certified official data-equation provenance, reusing the genuine unchanged mirror OLean."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_clearing_child_mirror_probe_v2 as previous
original=previous.original
import validate_namespace_context_providers as context
parent=original.parent
TASK,ROOT,V=parent.TASK,parent.ROOT,parent.V
SELF=Path(__file__).resolve()
STAGE=V/'ap16/clearing-child-mirror-probe-v3'
EMITTER_STAGE=original.STAGE
MODULE,OUTPUT,SNAPSHOT=original.MODULE,original.OUTPUT,original.SNAPSHOT
TYPE_JSON,REFS_JSON,MAPPING_JSON=original.TYPE_JSON,original.REFS_JSON,original.MAPPING_JSON
CERTIFICATE=original.CERTIFICATE
ACCEPTED=EMITTER_STAGE/'accepted-publication-record.json'
RUNNER=TASK/'scripts/preflight_staged_module_windows_bounded.py'
LEGACY_RUNNER=TASK/'scripts/preflight_staged_module.py'
CONSUMER=TASK/'scripts/certify_selected_minor_clearing_child_mirror_probe_v3.py'
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
  let mut dataEquations : Array Json := #[]
  for n in publicNames do
    if n != target && !equations.contains n then
      let some primary ← Lean.Meta.isEqnThm? n
        | throwError "Owned auxiliary public CI is not an official data equation: {n}"
      let certified := certifiedPrimaries.filter (fun pair => pair.1 == primary)
      unless certified.size == 1 do
        throwError "Owned data equation has no exact Published full-Def primary certificate: {n}"
      let expectedModule := certified[0]!.2
      unless (← ownerModule env primary) == expectedModule do
        throwError "Auxiliary data-equation primary owner differs: {primary}"
      let primaryCI ← getConstInfo primary
      match primaryCI with
      | .defnInfo _ => pure ()
      | _ => throwError "Auxiliary equation inverse primary is not a definition"
      let some actualEquations ← Lean.Meta.getEqnsFor? primary
        | throwError "Auxiliary equation primary has no official equation array"
      unless actualEquations.contains n do
        throwError "Auxiliary equation is absent from official primary equation array: {n}"
      let equationCI ← getConstInfo n
      match equationCI with
      | .thmInfo _ => pure ()
      | _ => throwError "Auxiliary data equation is not a theorem CI"
      dataEquations := dataEquations.push <| Json.mkObj [
        ("actualName",toJson n.toString),("primaryName",toJson primary.toString),
        ("primaryExpectedModule",toJson expectedModule),
        ("inverseGetter",toJson "Lean.Meta.isEqnThm?"),
        ("inversePrimary",toJson primary.toString),
        ("getter",toJson "Lean.Meta.getEqnsFor?"),
        ("actualEquationNames",toJson (actualEquations.map Name.toString)),
        ("primaryBinding",← PiExponentEquationProvenanceProbe.checkedCI primary),
        ("equation",← PiExponentEquationProvenanceProbe.checkedCI n),
        ("closedEquationProofReferences",Json.mkObj (← ciRow n true))]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),("mapping",Json.arr mapping),
    ("publicTarget",toJson target.toString),("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("officialDataEquationCandidates",toJson (equations.map Name.toString)),
    ("ownedDataEquations",Json.arr dataEquations)]).compress
  return resolved.push target ++ equations
end ClearingPrivateMirrorSnapshot
'''

def primary_evidence():
    bindings=read(parent.STAGE/parent.CERTIFICATE)['actual_provider_bindings'];result=[];paths=[]
    for key,folder,dest in [('AP10_interpolation','ap10/interpolation','publication'),('AP10_arithmetic','ap10/arithmetic','publication'),('scales_costs','ap15/scales-costs','publication-v2')]:
        root=V/folder;binding=bindings[key];certificate=TASK/binding['certificate'];cert=read(certificate)
        need(sha(certificate)==binding['certificate_sha256'] and cert['validated'] is True and cert['Std3_only'] is True and cert['definition_values_equal_and_exported'] is True,'Exact full Def provider certificate differs')
        source_file=root/'source-full-ci.jsonl';generated_file=root/'generated-full-ci.jsonl'
        for f in [source_file,generated_file]:need(cert['output_json_sha256'][rel(f)]==sha(f),'Certified primary full-CI JSON changed')
        source={r['sourceName']:r for r in map(json.loads,source_file.read_bytes().splitlines())};generated={r['sourceName']:r for r in map(json.loads,generated_file.read_bytes().splitlines())}
        publication=root/dest/'publication.json';pub=read(publication);wire=pub['publish_intent']['payload']['definition'];body=pub['target_readback']['body']
        need(pub['last_publish_verdict']['http_status']==200 and pub['last_publish_verdict']['body']['status']=='PUBLISHED' and pub['target_readback']['http_status']==200 and body['status']=='Definition' and body['definition']==wire and body['theorem_id']==pub['definition_id'] and pub['definition_name']==binding['module'].removeprefix('Definitions.Def_'),'Actual Published primary provider literal wire/readback differs')
        need(sha_bytes(wire.encode())==cert['provider_source_sha256'],'Published full Def bytes differ from actual kernel certificate')
        need(set(source)==set(generated)==set(cert['provided_names']),'Complete certified primary Def domain differs')
        for name in cert['provided_names']:
            a,b=source[name],generated[name]
            need(a['envKind']==b['envKind']=='def' and a['closedType'] is True and b['closedType'] is True and a['closedValue'] is True and b['closedValue'] is True and a['levelParams']==b['levelParams'] and a['type']==b['type'] and a['value']==b['value'] and a['axioms']==b['axioms'] and b['sourceModule']==binding['module'],'Original/Published primary complete Def value/type/Std3/owner differs')
            result.append({'name':name,'module':binding['module'],'certificate':rel(certificate),'certificate_sha256':sha(certificate),'source_json':rel(source_file),'generated_json':rel(generated_file),'source_row_sha256':sha_bytes(encode(a)),'generated_row_sha256':sha_bytes(encode(b)),'publication':rel(publication),'publication_sha256':sha(publication),'published_definition_id':pub['definition_id']})
        paths += [certificate,source_file,generated_file,publication]
    need(len(result)==17 and len({r['name'] for r in result})==17,'Certified exact auxiliary primary domain differs')
    return result,paths

def stage_files():
    previous.check_only(); evidence, evidence_paths=primary_evidence()
    emitter=context.record(EMITTER_STAGE/OUTPUT,EMITTER_STAGE/'c1.json','emit-olean',MODULE,EMITTER_STAGE)
    e=emitter['data'];need(e['success'] is True and e['timed_out'] is False and 0<e['seconds']<=300,'Genuine original mirror emitter did not pass bounded preflight')
    olean=context.file(e['output_olean']);need(e['output_olean_sha256']==sha(olean)==EXPECTED_OLEAN,'Original unchanged proof OLean differs')
    need(not (EMITTER_STAGE/SNAPSHOT).with_suffix('.lean.preflight.json').exists(),'Failed v1 probe unexpectedly has a completed preflight record')
    interruption=EMITTER_STAGE/'interrupted-probe-record.json';need(interruption.is_file(),'Root interruption evidence is missing')
    raw=(previous.STAGE/SNAPSHOT).read_bytes()
    anchor=previous.RESOLVER.encode();need(raw.count(anchor)==1,'Frozen private resolver anchor differs')
    decl='def certifiedPrimaries : Array (Name × String) := #['+', '.join('(`'+r['name']+', '+json.dumps(r['module'])+')' for r in evidence)+']\n'
    resolver=RESOLVER.replace('def resolveRoots',decl+'\ndef resolveRoots',1)
    probe=raw.replace(anchor,resolver.encode(),1).replace(parent.workspace_rel(previous.STAGE).encode(),parent.workspace_rel(STAGE).encode())
    need(probe.count(b'env.constants.toList')==1 and b'resolvePrivate' not in probe,'Optimized exact private resolver is not single-pass')
    p=read(EMITTER_STAGE/'preparation.json');inputs=dict(p['input_hashes'])
    paths=[SELF,CONSUMER,RUNNER,LEGACY_RUNNER,original.SELF,EMITTER_STAGE/'preparation.json',EMITTER_STAGE/'c1.json',EMITTER_STAGE/OUTPUT,(EMITTER_STAGE/OUTPUT).with_suffix('.lean.preflight.json'),EMITTER_STAGE/'c2.json',EMITTER_STAGE/SNAPSHOT,interruption,context.file(e['log']),olean]
    # Partial v1 equation files are retained as failed-attempt evidence only.
    # All certified equation/type/ref outputs must be written afresh by v2.
    paths += sorted(EMITTER_STAGE.glob('generated-equation-*.json'))
    paths += evidence_paths+[previous.SELF,previous.STAGE/'preparation.json',previous.STAGE/'c2.json',previous.STAGE/SNAPSHOT,(previous.STAGE/SNAPSHOT).with_suffix('.lean.preflight.json')]
    failed=read((previous.STAGE/SNAPSHOT).with_suffix('.lean.preflight.json'));need(failed['success'] is False and failed['timed_out'] is False and failed['exit_code']!=0 and 0<failed['seconds']<=300,'Expected bounded failed v2 probe evidence differs');paths.append(context.file(failed['log']))
    for path in paths:inputs[rel(path)]=sha(path)
    command='python scripts/preflight_staged_module_windows_bounded.py ap16/clearing-child-mirror-probe-v3/GeneratedSnapshot.lean --root ap16/clearing-child-mirror-probe-v3 --imports-manifest ap16/clearing-child-mirror-probe-v3/c2.json --timeout-seconds 300'
    manifest={'schema_version':1,'artifact_kind':'ap16-private-clearing-child-single-pass-probe-v3-manifest','output':parent.workspace_rel(STAGE/SNAPSHOT),'output_sha256':sha_bytes(probe),'imports':['Lean',MODULE],'input_hashes':inputs,'runtime_sha256':sha(parent.RUNTIME),'mode':'modecheck','emit_olean':False,'timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'reused_emitter_preflight':emitter['record'],'reused_emitter_preflight_sha256':emitter['record_sha256'],'reused_olean_sha256':EXPECTED_OLEAN,'validated':False,'submission_ready':False}
    prep=dict(p);prep.update({'artifact_kind':'ap16-private-clearing-child-single-pass-probe-v3-preparation','input_hashes':inputs,'reused_emitter_root':rel(EMITTER_STAGE),'reused_emitter_preflight':emitter['record'],'reused_emitter_preflight_sha256':emitter['record_sha256'],'reused_olean_sha256':EXPECTED_OLEAN,'failed_v1_probe_record':rel(interruption),'failed_v1_probe_record_sha256':sha(interruption),'failed_v1_partial_JSON_not_certified':True,'private_name_inventory_environment_traversals':1,'certified_auxiliary_primary_definitions':evidence,'public_platform_boundary_excludes_owned_data_equation_CIs':True,'failed_v2_probe_preflight':rel((previous.STAGE/SNAPSHOT).with_suffix('.lean.preflight.json')),'proof_source_and_OLean_unchanged':True,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'commands':[command]})
    return {SNAPSHOT:probe,'c2.json':encode(manifest),'preparation.json':encode(prep),'compile-commands.txt':(command+'\n').encode()}

def check_only():
    outputs=stage_files()
    for filename,raw in outputs.items():need((STAGE/filename).read_bytes()==raw,'Immutable probe-v3 staging differs: '+filename)
    manifest=read(STAGE/'c2.json');parent.base.runner.verify_manifest_inputs(manifest);parent.base.runner.verify_source_certificate(STAGE/SNAPSHOT,manifest)
    return {'checked_files':len(outputs),'reused_genuine_emitter_olean_sha256':EXPECTED_OLEAN,'one_pass_private_inventory':True,'proof_bytes_unchanged':True,'validated':False,'Lean_started':False,'API_used':False}

def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');args=parser.parse_args()
    if args.prepare:
        for filename,raw in stage_files().items():
            path=STAGE/filename
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite probe-v3 artifact: '+filename)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),indent=2))
if __name__=='__main__':main()
