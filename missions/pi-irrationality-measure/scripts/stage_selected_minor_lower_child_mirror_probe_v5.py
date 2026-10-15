"""Pure AP17 probe with an exact observed partition of unused closed Prop caches."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_lower_child_mirror_probe_v4 as previous
import validate_namespace_context_providers as context
TASK,ROOT,V=previous.TASK,previous.ROOT,previous.V
SELF=Path(__file__).resolve();STAGE=V/'ap17/generic-lower-child-mirror-probe-v5'
original=previous.original;EMITTER_STAGE=previous.EMITTER_STAGE
MODULE,OUTPUT,SNAPSHOT=previous.MODULE,previous.OUTPUT,previous.SNAPSHOT
TYPE_JSON,REFS_JSON,MAPPING_JSON=previous.TYPE_JSON,previous.REFS_JSON,previous.MAPPING_JSON
CERTIFICATE=previous.CERTIFICATE;ACCEPTED=previous.ACCEPTED;PARENT_CERTIFICATE=previous.PARENT_CERTIFICATE
parent,mechanism=previous.parent,previous.mechanism
RUNNER,LEGACY_RUNNER=previous.RUNNER,previous.LEGACY_RUNNER
CONSUMER=TASK/'scripts/certify_selected_minor_lower_child_mirror_probe_v5.py'
read,sha,sha_bytes,encode,need,rel=previous.read,previous.sha,previous.sha_bytes,previous.encode,previous.need,previous.rel
primary_evidence,automatic_evidence=previous.primary_evidence,previous.automatic_evidence
EQUATIONS,INVENTORY_JSON=previous.EQUATIONS,previous.INVENTORY_JSON
OBSERVED_INVENTORY=previous.STAGE/INVENTORY_JSON
OBSERVED_INVENTORY_SHA='b6775cc565df2caa6864f502ddc7b7d3ee6003b9034a779e1bcb8e3eddf210fb'

def observed_cache_evidence():
    need(sha(OBSERVED_INVENTORY)==OBSERVED_INVENTORY_SHA,'Genuine v4 actual owned-CI inventory differs')
    doc=read(OBSERVED_INVENTORY);primaries={r['name'] for r in primary_evidence()[0]}
    need(doc['mirrorModule']==MODULE and len(doc['rows'])==14 and [r['actualName'] for r in doc['rows']]==doc['actualOwnedPublicNames'],'Actual 14-CI owner inventory differs')
    caches=[];data=[]
    project=lambda n:n.startswith('OAI.') or n.startswith('_private.') and '.OAI.' in n
    for row in doc['rows']:
        n=row['actualName'];ci=row['CI']
        if n==parent.TARGET:continue
        if row['closedForallEqLhsHead'] in primaries:data.append(n);continue
        need(ci['name']==n and ci['closedType'] is True and ci['closedValue'] is True and ci['owner']['kind']=='ImportedModule' and ci['owner']['module']==MODULE and set(ci['axioms'])<={'propext','Classical.choice','Quot.sound'} and not any(project(x) for x in ci['allUsedConstants']),'Actual non-Def auxiliary lacks exact closed zero-project proof provenance')
        caches.append({'name':n,'actual_inventory_row':row,'actual_inventory_CI_sha256':sha_bytes(encode(ci))})
    names={r['name'] for r in caches}
    need(len(caches)==7 and len(data)==6 and all(not names&set(r['CI']['allUsedConstants']) for r in doc['rows']),'Observed caches are not exactly finite7 unused helpers plus six data equations')
    return caches,data

CACHE_BRANCH=r'''
    if exactObservedUnusedCaches.contains n then
      let ci ← getConstInfo n
      unless (← isProp ci.type) do
        throwError "Observed internal cache is not a genuine Prop theorem"
      match ci with
      | .thmInfo _ => pure ()
      | _ => throwError "Observed internal cache is not a theorem CI"
      let row ← ciRow n true
      for used in refs ci.type ++ refs (valueOf ci |>.getD ci.type) do
        if (Lean.privateToUserName used).toString.startsWith "OAI." then
          throwError "Observed internal cache has a project reference"
      internalCaches := internalCaches.push <| Json.mkObj [
        ("actualName",toJson n.toString),("actualIsProp",toJson true),
        ("CI",Json.mkObj row)]
    else if n != target && !equations.contains n then
'''

def stage_files():
    previous.check_only();caches,data=observed_cache_evidence()
    emitter=context.record(EMITTER_STAGE/OUTPUT,EMITTER_STAGE/'c1.json','emit-olean',MODULE,EMITTER_STAGE);e=emitter['data'];olean=context.file(e['output_olean'])
    need(e['success'] is True and sha(olean)==e['output_olean_sha256'],'Genuine unchanged emitter differs')
    failed_path=(previous.STAGE/SNAPSHOT).with_suffix('.lean.preflight.json');failed=read(failed_path);log=context.file(failed['log'])
    need(failed['success'] is False and failed['timed_out'] is False and failed['exit_code']!=0 and 0<failed['seconds']<=300 and 'not definitionally equal' in log.read_text(encoding='utf-8'),'Actual v4 non-DefEq cache failure differs')
    p=read(previous.STAGE/'preparation.json');raw=(previous.STAGE/SNAPSHOT).read_bytes()
    namespace=b'namespace GenericLowerPrivateMirrorSnapshot\nopen Lean Meta FullRowMinorProofSnapshot\n'
    # Exact observed names are derived from the compiler inventory, never a suffix pattern.
    decl=('def exactObservedUnusedCaches : Array Name := #['+', '.join('`'+r['name'] for r in caches)+']\n').encode()
    need(raw.count(namespace)==1,'Observed cache declaration namespace anchor differs');probe=raw.replace(namespace,namespace+decl,1)
    anchor=b'  let mut dataEquations : Array Json := #[]';need(probe.count(anchor)==1,'Exact auxiliary partition anchor differs')
    probe=probe.replace(anchor,b'  let mut internalCaches : Array Json := #[]\n'+anchor,1)
    anchor=b'    if n != target && !equations.contains n then';need(probe.count(anchor)==1,'Exact auxiliary gate branch differs');probe=probe.replace(anchor,CACHE_BRANCH.encode().strip(b'\n'),1)
    anchor=b'("ownedDataEquations",Json.arr dataEquations)]';need(probe.count(anchor)==1,'Exact mapping ledger anchor differs')
    probe=probe.replace(anchor,b'("ownedDataEquations",Json.arr dataEquations),\n    ("ownedUnusedPropCaches",Json.arr internalCaches)]',1)
    probe=probe.replace(parent.workspace_rel(previous.STAGE).encode(),parent.workspace_rel(STAGE).encode())
    need(probe.count(b'env.constants.toList')==1 and b'liftIO' not in probe,'Single-pass declaration contract differs')
    inputs=dict(p['input_hashes'])
    for path in [SELF,CONSUMER,previous.SELF,previous.CONSUMER,previous.STAGE/'preparation.json',previous.STAGE/'c2.json',previous.STAGE/SNAPSHOT,failed_path,log,OBSERVED_INVENTORY]:inputs[rel(path)]=sha(path)
    command='python scripts/preflight_staged_module_windows_bounded.py ap17/generic-lower-child-mirror-probe-v5/GeneratedSnapshot.lean --root ap17/generic-lower-child-mirror-probe-v5 --imports-manifest ap17/generic-lower-child-mirror-probe-v5/c2.json --timeout-seconds 300'
    manifest=dict(read(previous.STAGE/'c2.json'));manifest.update({'artifact_kind':'ap17-generic-lower-observed-unused-cache-probe-v5-manifest','output':parent.workspace_rel(STAGE/SNAPSHOT),'output_sha256':sha_bytes(probe),'input_hashes':inputs})
    prep=dict(p);prep.update({'artifact_kind':'ap17-generic-lower-observed-unused-cache-probe-v5-preparation','input_hashes':inputs,'exact_observed_unused_cache_evidence':caches,'exact_observed_data_equation_names':data,'observed_owned_CI_inventory':rel(OBSERVED_INVENTORY),'observed_owned_CI_inventory_sha256':sha(OBSERVED_INVENTORY),'failed_v4_probe_preflight':rel(failed_path),'failed_v4_probe_preflight_sha256':sha(failed_path),'failed_v4_probe_log_sha256':sha(log),'cache_ledger_requires_actual_isProp_closed_proof_Std3_zero_project_refs_and_unused_by_proof_closure':True,'compile_commands':[command]})
    return {SNAPSHOT:probe,'c2.json':encode(manifest),'preparation.json':encode(prep),'compile-commands.txt':(command+'\n').encode()}

def check_only():
    for name,raw in stage_files().items():need((STAGE/name).read_bytes()==raw,'Immutable v5 stage differs: '+name)
    m=read(STAGE/'c2.json');parent.clearing.base.runner.verify_manifest_inputs(m);parent.clearing.base.runner.verify_source_certificate(STAGE/SNAPSHOT,m)
    return {'checked_files':4,'actual_certified_Def_domain_size':23,'exact_unused_Prop_cache_domain_size':7,'exact_data_equation_domain_size':6,'proof_source_and_OLean_unchanged':True,'validated':False,'Lean_started':False,'API_used':False}

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
