"""One-process AP17 finalize/certify with one genuine fixed-locator child replay."""
from __future__ import annotations
import argparse,copy,json
from pathlib import Path
import stage_actual_minor_arithmetic_lower_bound_source017_node as stage
import certify_actual_minor_arithmetic_lower_bound_source017_node as consumer
import certify_selected_minor_lower_child_mirror_probe_v5 as child
SELF=Path(__file__).resolve()
CHILD_CERT_SHA='5a069b378459a9b894325772277f70732e335e44758b1f51c301000af1e655cd'
CHILD_CONSUMER_SHA='abf27d1445d9d18c6f6b3f6f59a5f00aa0d96de17cf7d97e9c43d8ce2d5d8c28'

def run(mode):
    cert_path=stage.MIRROR_STAGE/stage.mirror.CERTIFICATE
    stage.need(stage.sha(cert_path)==CHILD_CERT_SHA and stage.sha(Path(child.__file__))==CHILD_CONSUMER_SHA,'Root-confirmed genuine v5 certificate/consumer differs')
    pins={str(cert_path):CHILD_CERT_SHA,str(Path(child.__file__)):CHILD_CONSUMER_SHA,str(stage.SELF):stage.sha(stage.SELF),str(consumer.SELF):stage.sha(consumer.SELF)}
    manifest=stage.read(stage.MIRROR_STAGE/'c2.json')
    for path,h in manifest['input_hashes'].items():pins[str(stage.TASK/path)]=h
    recorded=stage.read(cert_path)
    for path,h in recorded['implementation_hashes'].items():pins[str(stage.TASK/path)]=h
    for f,h in recorded['generated_json_sha256'].items():pins[str(stage.MIRROR_STAGE/f)]=h
    pins[str(stage.MIRROR_STAGE/'preparation.json')]=recorded['preparation_sha256']
    pins[str(stage.TASK/recorded['provider_olean'])]=recorded['provider_olean_sha256']
    for row in recorded['preflights'].values():
        pins[str(stage.TASK/row['record'])]=row['record_sha256']
        for key in ['source','manifest','log']:
            path=child.context.file(row['data'][key]);pins[str(path)]=stage.sha(path)
    def hash_gate():
        for path,h in pins.items():stage.need(stage.sha(Path(path))==h,'Fixed child replay input changed: '+path)
    original=child.validate;cached=None;calls=0;reuses=0
    def once():
        nonlocal cached,calls,reuses
        hash_gate()
        if cached is None:
            calls+=1;cached=original()
            stage.need(stage.encode(cached)==cert_path.read_bytes(),'First full mathematical replay differs from genuine child certificate')
        else:reuses+=1
        hash_gate();return copy.deepcopy(cached)
    child.validate=once
    try:
        if mode=='finalize':
            outputs=stage.final_files()  # Exactly once; do not call stage.check_only afterwards.
            for name,raw in outputs.items():
                path=stage.STAGE/name
                if path.exists():stage.need(path.read_bytes()==raw,'Refusing overwrite: '+name)
                else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
            for name,raw in outputs.items():stage.need((stage.STAGE/name).read_bytes()==raw,'Written output differs: '+name)
            result={'prepared':True,'files':{name:stage.sha(stage.STAGE/name) for name in outputs},'compile_commands':stage.read(stage.STAGE/'preparation.json')['compile_commands']}
        else:
            report=consumer.validate();raw=stage.encode(report);path=stage.STAGE/stage.CERTIFICATE
            if path.exists():stage.need(path.read_bytes()==raw,'Immutable node certificate differs')
            else:path.write_bytes(raw)
            result={'certificate':stage.rel(path),'certificate_sha256':stage.sha(path),'validated':report['validated'],'Std3_only':report['Std3_only'],'max_file_seconds':report['max_file_seconds']}
    finally:child.validate=original
    stage.need(calls==1,'Fixed child must have exactly one full mathematical replay')
    hash_gate()
    invocation={'schema_version':1,'artifact_kind':'ap17-one-process-actual-node-'+mode,'helper_sha256':stage.sha(SELF),'node_producer_sha256':stage.sha(stage.SELF),'node_consumer_sha256':stage.sha(consumer.SELF),'fixed_child_certificate':stage.rel(cert_path),'fixed_child_certificate_sha256':CHILD_CERT_SHA,'fixed_child_consumer_sha256':CHILD_CONSUMER_SHA,'full_child_mathematical_replays':calls,'same_process_child_reuses':reuses,'all_fixed_inputs_rehashed_before_each_reuse':True,'first_full_replay_not_skipped':True,'result':result,'Lean_started':False,'API_used':False}
    record=stage.STAGE/('one-process-'+mode+'-invocation.json');data=stage.encode(invocation)
    if record.exists():stage.need(record.read_bytes()==data,'Invocation preimage differs')
    else:record.write_bytes(data)
    return invocation

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--finalize',action='store_true');g.add_argument('--certify-existing',action='store_true');a=p.parse_args()
    print(json.dumps(run('finalize' if a.finalize else 'certify-existing'),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
