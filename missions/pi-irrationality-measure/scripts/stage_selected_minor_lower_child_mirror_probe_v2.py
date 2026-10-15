"""Pure isolated AP17 metadata repair; reuse the genuine unchanged mirror emitter."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_lower_child_mirror as original
import validate_namespace_context_providers as context
TASK,ROOT,V=original.TASK,original.ROOT,original.V
SELF=Path(__file__).resolve();STAGE=V/'ap17/generic-lower-child-mirror-probe-v2'
EMITTER_STAGE=original.STAGE
MODULE,OUTPUT,SNAPSHOT=original.MODULE,original.OUTPUT,original.SNAPSHOT
TYPE_JSON,REFS_JSON,MAPPING_JSON=original.TYPE_JSON,original.REFS_JSON,original.MAPPING_JSON
CERTIFICATE=original.CERTIFICATE;ACCEPTED=original.ACCEPTED
PARENT_CERTIFICATE=original.PARENT_CERTIFICATE
parent,mechanism=original.parent,original.mechanism
RUNNER,LEGACY_RUNNER=original.RUNNER,original.LEGACY_RUNNER
CONSUMER=TASK/'scripts/certify_selected_minor_lower_child_mirror_probe_v2.py'
read,sha,sha_bytes,encode,need,rel=original.read,original.sha,original.sha_bytes,original.encode,original.need,original.rel
primary_evidence,automatic_evidence=original.primary_evidence,original.automatic_evidence
EQUATIONS=original.EQUATIONS
PROVENANCE_SOURCE=mechanism.STAGE/mechanism.SNAPSHOT

def provenance_block():
    raw=PROVENANCE_SOURCE.read_bytes()
    start=b'namespace PiExponentEquationProvenanceProbe'
    end=b'end PiExponentEquationProvenanceProbe'
    need(raw.count(start)==raw.count(end)==1,'Actual v4 provenance namespace domain differs')
    block=raw[raw.index(start):raw.index(end)+len(end)]
    need(block.count(b'def checkedCI ')==1 and b'PiExponentInterfaceSnapshot.exprJson' in block,'Actual v4 checkedCI declaration is missing')
    return block

def stage_files():
    original.check_only()
    emitter=context.record(EMITTER_STAGE/OUTPUT,EMITTER_STAGE/'c1.json','emit-olean',MODULE,EMITTER_STAGE)
    e=emitter['data'];need(e['success'] is True and e['exit_code']==0 and e['timed_out'] is False and 0<e['seconds']<=300,'Genuine AP17 emitter did not pass')
    olean=context.file(e['output_olean']);need(sha(olean)==e['output_olean_sha256'],'Unchanged AP17 proof OLean differs')
    failed_path=(EMITTER_STAGE/SNAPSHOT).with_suffix('.lean.preflight.json');failed=read(failed_path)
    need(failed['success'] is False and failed['exit_code']!=0 and failed['timed_out'] is False and 0<failed['seconds']<=300,'Original bounded metadata failure evidence differs')
    failed_log=context.file(failed['log']);need('unknown' in failed_log.read_text(encoding='utf-8') and 'PiExponentEquationProvenanceProbe.checkedCI' in failed_log.read_text(encoding='utf-8'),'Actual failure is not the recorded missing declaration')
    p=read(EMITTER_STAGE/'preparation.json');raw=(EMITTER_STAGE/SNAPSHOT).read_bytes();block=provenance_block()
    anchor=b'namespace GenericLowerPrivateMirrorSnapshot'
    need(raw.count(anchor)==1 and b'namespace PiExponentEquationProvenanceProbe' not in raw,'Original finite missing-block diagnosis differs')
    probe=raw.replace(anchor,block+b'\n\n'+anchor,1).replace(parent.workspace_rel(EMITTER_STAGE).encode(),parent.workspace_rel(STAGE).encode())
    need(probe.count(b'env.constants.toList')==1 and probe.count(b'def checkedCI ')==1,'Repaired declarations or one-pass inventory differs')
    need(probe.index(b'def checkedCI ')<probe.index(anchor)<probe.index(b'run_meta do'),'Provenance declarations are not defined before use')
    inputs=dict(p['input_hashes'])
    paths=[SELF,CONSUMER,original.SELF,original.CONSUMER,EMITTER_STAGE/'preparation.json',EMITTER_STAGE/'c1.json',EMITTER_STAGE/OUTPUT,(EMITTER_STAGE/OUTPUT).with_suffix('.lean.preflight.json'),context.file(e['log']),olean,EMITTER_STAGE/'c2.json',EMITTER_STAGE/SNAPSHOT,failed_path,failed_log,PROVENANCE_SOURCE,ACCEPTED]
    for path in paths:inputs[rel(path)]=sha(path)
    command='python scripts/preflight_staged_module_windows_bounded.py ap17/generic-lower-child-mirror-probe-v2/GeneratedSnapshot.lean --root ap17/generic-lower-child-mirror-probe-v2 --imports-manifest ap17/generic-lower-child-mirror-probe-v2/c2.json --timeout-seconds 300'
    manifest={'schema_version':1,'artifact_kind':'ap17-generic-lower-repaired-probe-v2-manifest','output':parent.workspace_rel(STAGE/SNAPSHOT),'output_sha256':sha_bytes(probe),'imports':['Lean',MODULE],'input_hashes':inputs,'runtime_sha256':sha(parent.clearing.RUNTIME),'mode':'modecheck','emit_olean':False,'timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'reused_emitter_preflight':emitter['record'],'reused_emitter_preflight_sha256':emitter['record_sha256'],'reused_olean_sha256':sha(olean),'validated':False,'submission_ready':False}
    prep=dict(p);prep.update({'artifact_kind':'ap17-generic-lower-repaired-probe-v2-preparation','input_hashes':inputs,'reused_emitter_root':rel(EMITTER_STAGE),'reused_emitter_preflight':emitter['record'],'reused_emitter_preflight_sha256':emitter['record_sha256'],'reused_olean_sha256':sha(olean),'failed_original_probe_preflight':rel(failed_path),'failed_original_probe_preflight_sha256':sha(failed_path),'failed_original_probe_log_sha256':sha(failed_log),'provenance_block_source':rel(PROVENANCE_SOURCE),'provenance_block_source_sha256':sha(PROVENANCE_SOURCE),'inserted_exact_provenance_block_sha256':sha_bytes(block),'only_missing_provenance_declarations_and_output_directory_changed':True,'proof_source_and_OLean_unchanged':True,'actual_Accepted_evidence_sha256':sha(ACCEPTED),'compile_commands':[command]})
    return {SNAPSHOT:probe,'c2.json':encode(manifest),'preparation.json':encode(prep),'compile-commands.txt':(command+'\n').encode()}

def check_only():
    for filename,raw in stage_files().items():need((STAGE/filename).read_bytes()==raw,'Isolated repaired probe changed: '+filename)
    manifest=read(STAGE/'c2.json');parent.clearing.base.runner.verify_manifest_inputs(manifest);parent.clearing.base.runner.verify_source_certificate(STAGE/SNAPSHOT,manifest)
    return {'checked_files':4,'proof_source_and_OLean_unchanged':True,'one_pass_private_inventory':True,'exact_v4_provenance_declarations_inserted':True,'validated':False,'Lean_started':False,'API_used':False}

def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');args=parser.parse_args()
    if args.prepare:
        for filename,raw in stage_files().items():
            path=STAGE/filename
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+filename)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),indent=2))
if __name__=='__main__':main()
