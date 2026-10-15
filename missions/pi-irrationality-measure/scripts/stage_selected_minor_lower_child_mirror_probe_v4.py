"""Pure isolated one-line AP17 inventory IO repair; proof emitter remains unchanged."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_lower_child_mirror_probe_v3 as previous
import validate_namespace_context_providers as context
TASK,ROOT,V=previous.TASK,previous.ROOT,previous.V
SELF=Path(__file__).resolve();STAGE=V/'ap17/generic-lower-child-mirror-probe-v4'
original=previous.original;EMITTER_STAGE=previous.EMITTER_STAGE
MODULE,OUTPUT,SNAPSHOT=previous.MODULE,previous.OUTPUT,previous.SNAPSHOT
TYPE_JSON,REFS_JSON,MAPPING_JSON=previous.TYPE_JSON,previous.REFS_JSON,previous.MAPPING_JSON
CERTIFICATE=previous.CERTIFICATE;ACCEPTED=previous.ACCEPTED;PARENT_CERTIFICATE=previous.PARENT_CERTIFICATE
parent,mechanism=previous.parent,previous.mechanism
RUNNER,LEGACY_RUNNER=previous.RUNNER,previous.LEGACY_RUNNER
CONSUMER=TASK/'scripts/certify_selected_minor_lower_child_mirror_probe_v4.py'
read,sha,sha_bytes,encode,need,rel=previous.read,previous.sha,previous.sha_bytes,previous.encode,previous.need,previous.rel
primary_evidence,automatic_evidence=previous.primary_evidence,previous.automatic_evidence
EQUATIONS,INVENTORY_JSON=previous.EQUATIONS,previous.INVENTORY_JSON

def stage_files():
    previous.check_only()
    emitter=context.record(EMITTER_STAGE/OUTPUT,EMITTER_STAGE/'c1.json','emit-olean',MODULE,EMITTER_STAGE)
    e=emitter['data'];olean=context.file(e['output_olean']);need(e['success'] is True and sha(olean)==e['output_olean_sha256'],'Genuine unchanged emitter differs')
    failed_path=(previous.STAGE/SNAPSHOT).with_suffix('.lean.preflight.json');failed=read(failed_path);log=context.file(failed['log'])
    need(failed['success'] is False and failed['timed_out'] is False and failed['exit_code']!=0 and 0<failed['seconds']<=300 and "Unknown identifier `liftIO`" in log.read_text(encoding='utf-8'),'Actual bounded v3 inventory IO failure differs')
    p=read(previous.STAGE/'preparation.json');raw=(previous.STAGE/SNAPSHOT).read_bytes()
    anchor=b'  liftIO <| IO.FS.writeFile inventoryOutput';need(raw.count(anchor)==1,'Finite inventory IO repair anchor differs')
    probe=raw.replace(anchor,b'  IO.FS.writeFile inventoryOutput',1).replace(parent.workspace_rel(previous.STAGE).encode(),parent.workspace_rel(STAGE).encode())
    need(b'liftIO' not in probe and probe.count(b'env.constants.toList')==1 and probe.index(b'def checkedCI ')<probe.index(b'namespace GenericLowerPrivateMirrorSnapshot'),'Repaired snapshot declaration/inventory contract differs')
    inputs=dict(p['input_hashes'])
    for path in [SELF,CONSUMER,previous.SELF,previous.CONSUMER,previous.STAGE/'preparation.json',previous.STAGE/'c2.json',previous.STAGE/SNAPSHOT,failed_path,log]:inputs[rel(path)]=sha(path)
    command='python scripts/preflight_staged_module_windows_bounded.py ap17/generic-lower-child-mirror-probe-v4/GeneratedSnapshot.lean --root ap17/generic-lower-child-mirror-probe-v4 --imports-manifest ap17/generic-lower-child-mirror-probe-v4/c2.json --timeout-seconds 300'
    manifest=dict(read(previous.STAGE/'c2.json'));manifest.update({'artifact_kind':'ap17-generic-lower-inventory-IO-probe-v4-manifest','output':parent.workspace_rel(STAGE/SNAPSHOT),'output_sha256':sha_bytes(probe),'input_hashes':inputs})
    prep=dict(p);prep.update({'artifact_kind':'ap17-generic-lower-inventory-IO-probe-v4-preparation','input_hashes':inputs,'failed_v3_probe_preflight':rel(failed_path),'failed_v3_probe_preflight_sha256':sha(failed_path),'failed_v3_probe_log_sha256':sha(log),'only_inventory_IO_identifier_and_output_directory_changed':True,'compile_commands':[command]})
    return {SNAPSHOT:probe,'c2.json':encode(manifest),'preparation.json':encode(prep),'compile-commands.txt':(command+'\n').encode()}

def check_only():
    for name,raw in stage_files().items():need((STAGE/name).read_bytes()==raw,'Immutable v4 stage differs: '+name)
    m=read(STAGE/'c2.json');parent.clearing.base.runner.verify_manifest_inputs(m);parent.clearing.base.runner.verify_source_certificate(STAGE/SNAPSHOT,m)
    return {'checked_files':4,'actual_certified_Def_domain_size':23,'one_line_inventory_IO_repair':True,'proof_source_and_OLean_unchanged':True,'validated':False,'Lean_started':False,'API_used':False}

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
