"""Pure AP17 metadata successor with six actual AP9 full Def witnesses and early inventory."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_lower_child_mirror_probe_v2 as previous
import validate_namespace_context_providers as context
original=previous.original
TASK,ROOT,V=previous.TASK,previous.ROOT,previous.V
SELF=Path(__file__).resolve();STAGE=V/'ap17/generic-lower-child-mirror-probe-v3'
EMITTER_STAGE=previous.EMITTER_STAGE
MODULE,OUTPUT,SNAPSHOT=previous.MODULE,previous.OUTPUT,previous.SNAPSHOT
TYPE_JSON,REFS_JSON,MAPPING_JSON=previous.TYPE_JSON,previous.REFS_JSON,previous.MAPPING_JSON
CERTIFICATE=previous.CERTIFICATE;ACCEPTED=previous.ACCEPTED;PARENT_CERTIFICATE=previous.PARENT_CERTIFICATE
parent,mechanism=previous.parent,previous.mechanism
RUNNER,LEGACY_RUNNER=previous.RUNNER,previous.LEGACY_RUNNER
CONSUMER=TASK/'scripts/certify_selected_minor_lower_child_mirror_probe_v3.py'
read,sha,sha_bytes,encode,need,rel=previous.read,previous.sha,previous.sha_bytes,previous.encode,previous.need,previous.rel
automatic_evidence=previous.automatic_evidence;EQUATIONS=previous.EQUATIONS
INVENTORY_JSON='actual-owned-public-inventory.json'

def primary_evidence():
    result,paths=original.primary_evidence()
    import certify_weighted_simplex_domains_existing as ap9
    for key in ['simplex','domains']:
        root=V/'ap9'/key;certificate=root/'actual-provider-validation.json';cert=read(certificate)
        module=cert['platform_module'];publication=root/'publication/publication.json';pub=read(publication)
        need(cert['validated'] is True and cert['Std3_only'] is True and cert['definition_values_equal_and_exported'] is True and cert['contains_theorems'] is False,'Actual AP9 full Def certificate differs')
        source_file=root/'source-full-ci.jsonl';generated_file=root/'generated-full-ci.jsonl'
        for f in [source_file,generated_file]:need(cert['output_json_sha256'][rel(f)]==sha(f),'Actual AP9 full CI bytes differ')
        source={r['sourceName']:r for r in map(json.loads,source_file.read_bytes().splitlines())};generated={r['sourceName']:r for r in map(json.loads,generated_file.read_bytes().splitlines())}
        wire=pub['publish_intent']['payload']['definition'];body=pub['target_readback']['body']
        need(pub['last_publish_verdict']['http_status']==pub['target_readback']['http_status']==200 and pub['last_publish_verdict']['body']['status']=='PUBLISHED' and body['status']=='Definition' and body['definition']==wire and body['theorem_id']==pub['definition_id'] and pub['definition_name']==module.removeprefix('Definitions.Def_') and sha_bytes(wire.encode())==cert['provider_source_sha256'],'Genuine AP9 Published literal full Def readback differs')
        need(set(source)==set(generated)==set(cert['provided_names']),'AP9 complete Def domain differs')
        olean=TASK/cert['provider_olean'];need(sha(olean)==cert['provider_olean_sha256'],'Genuine AP9 provider OLean differs')
        for name in cert['provided_names']:
            a,b=source[name],generated[name]
            for row,expected in [(a,cert['source_module']),(b,module)]:
                need(set(row)==ap9.ROW_FIELDS and row['sourceName']==row['resolvedName']==name and row['sourceModule']==expected and row['graphKind']==row['envKind']=='def' and row['closedType'] is True and row['closedValue'] is True and row['value'] is not None and row['kindMetadata']=={'valueExported':True,'safety':'Lean.DefinitionSafety.safe'} and row['familyReferences']==row['transitiveNames']==[],'Actual AP9 Def full CI kind/owner/closure differs')
                ap9.checked_expr(row['type'],set(row['levelParams']));ap9.checked_expr(row['value'],set(row['levelParams']))
                need(set(row['axioms'])<=ap9.STD3 and row['axioms']==sorted(set(row['axioms'])),'Actual AP9 Def exceeds Std3')
            need(a['levelParams']==b['levelParams'] and a['type']==b['type'] and a['value']==b['value'] and a['axioms']==b['axioms'],'AP9 original/Published full Def type/value/Std3 mismatch')
            result.append({'name':name,'module':module,'certificate':rel(certificate),'certificate_sha256':sha(certificate),'source_json':rel(source_file),'generated_json':rel(generated_file),'source_row_sha256':sha_bytes(encode(a)),'generated_row_sha256':sha_bytes(encode(b)),'publication':rel(publication),'publication_sha256':sha(publication),'published_definition_id':pub['definition_id']})
        paths += [certificate,source_file,generated_file,publication,olean]
    need(len(result)==23 and len({r['name'] for r in result})==23,'Exact 17 prior plus six AP9 full Def domain differs')
    return result,paths

INVENTORY=r'''
  let mut inventory : Array Json := #[]
  for n in publicNames do
    let ci ← getConstInfo n
    let (binderCount, primary?) ← forallTelescope ci.type fun xs body => do
      let primary? := if body.isAppOfArity ``Eq 3 then
        match (body.getAppArgs[1]!).getAppFn with
        | .const primary _ => some primary
        | _ => none
        else none
      return (xs.size, primary?)
    let equations? ← match primary? with
      | some primary => Lean.Meta.getEqnsFor? primary
      | none => pure none
    let unfolding? ← match primary? with
      | some primary => Lean.Meta.getUnfoldEqnFor? primary
      | none => pure none
    let inverse? ← Lean.Meta.isEqnThm? n
    inventory := inventory.push <| Json.mkObj [
      ("actualName",toJson n.toString),("binderCount",toJson binderCount),
      ("closedForallEqLhsHead",toJson (primary?.map Name.toString)),
      ("actualEquationNames",toJson (equations?.map (·.map Name.toString))),
      ("actualUnfoldingName",toJson (unfolding?.map Name.toString)),
      ("inversePrimary",toJson (inverse?.map Name.toString)),
      ("CI",Json.mkObj (← ciRow n true))]
  liftIO <| IO.FS.writeFile inventoryOutput (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("rows",Json.arr inventory)]).compress
'''

def stage_files():
    previous.check_only();evidence,paths=primary_evidence()
    emitter=context.record(EMITTER_STAGE/OUTPUT,EMITTER_STAGE/'c1.json','emit-olean',MODULE,EMITTER_STAGE);e=emitter['data']
    need(e['success'] is True and e['timed_out'] is False and 0<e['seconds']<=300,'Genuine unchanged emitter did not pass')
    olean=context.file(e['output_olean']);need(sha(olean)==e['output_olean_sha256'],'Unchanged proof OLean differs')
    failed_path=(previous.STAGE/SNAPSHOT).with_suffix('.lean.preflight.json');failed=read(failed_path);log=context.file(failed['log'])
    need(failed['success'] is False and failed['exit_code']!=0 and failed['timed_out'] is False and 0<failed['seconds']<=300 and 'no exact Published full-Def primary certificate' in log.read_text(encoding='utf-8'),'Actual bounded v2 full Def domain failure differs')
    p=read(previous.STAGE/'preparation.json');raw=(previous.STAGE/SNAPSHOT).read_bytes()
    old_decl='def certifiedPrimaries : Array (Name × String) := #['+', '.join('(`'+r['name']+', '+json.dumps(r['module'])+')' for r in p['certified_auxiliary_primary_definitions'])+']\n'
    new_decl='def certifiedPrimaries : Array (Name × String) := #['+', '.join('(`'+r['name']+', '+json.dumps(r['module'])+')' for r in evidence)+']\n'
    need(raw.count(old_decl.encode())==1,'Exact old primary declaration differs')
    probe=raw.replace(old_decl.encode(),new_decl.encode(),1).replace(parent.workspace_rel(previous.STAGE).encode(),parent.workspace_rel(STAGE).encode())
    anchor=b'  let mut dataEquations : Array Json := #[]'
    inventory=('  let inventoryOutput := '+json.dumps(parent.workspace_rel(STAGE/INVENTORY_JSON))+'\n').encode()+INVENTORY.encode()
    need(probe.count(anchor)==1,'Exact pre-gate inventory anchor differs');probe=probe.replace(anchor,inventory+b'\n'+anchor,1)
    need(probe.count(b'env.constants.toList')==1 and probe.count(b'def checkedCI ')==1 and probe.index(b'def checkedCI ')<probe.index(b'namespace GenericLowerPrivateMirrorSnapshot'),'Single scan and declaration-before-use contract differs')
    inputs=dict(p['input_hashes'])
    paths += [SELF,CONSUMER,previous.SELF,previous.CONSUMER,previous.STAGE/'preparation.json',previous.STAGE/'c2.json',previous.STAGE/SNAPSHOT,failed_path,log]
    for path in paths:inputs[rel(path)]=sha(path)
    command='python scripts/preflight_staged_module_windows_bounded.py ap17/generic-lower-child-mirror-probe-v3/GeneratedSnapshot.lean --root ap17/generic-lower-child-mirror-probe-v3 --imports-manifest ap17/generic-lower-child-mirror-probe-v3/c2.json --timeout-seconds 300'
    manifest=dict(read(previous.STAGE/'c2.json'));manifest.update({'artifact_kind':'ap17-generic-lower-complete-AP9-probe-v3-manifest','output':parent.workspace_rel(STAGE/SNAPSHOT),'output_sha256':sha_bytes(probe),'input_hashes':inputs})
    prep=dict(p);prep.update({'artifact_kind':'ap17-generic-lower-complete-AP9-probe-v3-preparation','input_hashes':inputs,'certified_auxiliary_primary_definitions':evidence,'actual_primary_Def_domain_size':23,'exact_six_AP9_complete_Def_witnesses_added':True,'early_owned_inventory_output':INVENTORY_JSON,'early_inventory_export_before_strict_primary_gate':True,'failed_v2_probe_preflight':rel(failed_path),'failed_v2_probe_preflight_sha256':sha(failed_path),'failed_v2_probe_log_sha256':sha(log),'compile_commands':[command]})
    return {SNAPSHOT:probe,'c2.json':encode(manifest),'preparation.json':encode(prep),'compile-commands.txt':(command+'\n').encode()}

def check_only():
    for name,raw in stage_files().items():need((STAGE/name).read_bytes()==raw,'Immutable v3 stage differs: '+name)
    m=read(STAGE/'c2.json');parent.clearing.base.runner.verify_manifest_inputs(m);parent.clearing.base.runner.verify_source_certificate(STAGE/SNAPSHOT,m)
    return {'checked_files':4,'actual_certified_Def_domain_size':23,'early_inventory_before_strict_gate':True,'proof_source_and_OLean_unchanged':True,'validated':False,'Lean_started':False,'API_used':False}

def check_candidate():return check_only()

def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=parser.parse_args()
    if a.prepare:
        for name,raw in stage_files().items():
            path=STAGE/name
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+name)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),indent=2))
if __name__=='__main__':main()
