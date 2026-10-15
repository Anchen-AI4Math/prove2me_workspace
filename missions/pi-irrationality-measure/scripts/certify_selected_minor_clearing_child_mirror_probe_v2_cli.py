"""CLI repair only: call the unchanged, compiler-pinned private-mirror validator."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import certify_selected_minor_clearing_child_mirror_probe_v2 as frozen

SELF=Path(__file__).resolve()
stage=frozen.stage
PROVENANCE=stage.STAGE/'cli-adapter'
PREIMAGE=PROVENANCE/'consumer-main-preimage.py.txt'
INVOCATION=PROVENANCE/'certificate-invocation.json'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--certify-existing',action='store_true')
    modes.add_argument('--check-only',action='store_true')
    args=parser.parse_args()
    need,sha,rel=stage.need,stage.sha,stage.rel
    need(PREIMAGE.read_bytes()==frozen.SELF.read_bytes(),
         'Frozen consumer/main preimage differs')
    manifest=stage.read(stage.STAGE/'c2.json')
    need(manifest['input_hashes'][rel(frozen.SELF)]==sha(frozen.SELF),
         'Compiler-pinned validator changed')
    report=frozen.validate()
    certificate=stage.STAGE/stage.CERTIFICATE
    raw=stage.encode(report)
    if certificate.exists():
        need(certificate.read_bytes()==raw,'Existing private mirror certificate differs')
    elif args.certify_existing:
        certificate.write_bytes(raw)
    else:
        need(False,'Check-only requires the existing exact certificate')
    invocation={'schema_version':1,
        'artifact_kind':'ap16-private-mirror-v2-cli-adapter-invocation',
        'adapter':rel(SELF),'adapter_sha256':sha(SELF),
        'frozen_consumer':rel(frozen.SELF),'frozen_consumer_sha256':sha(frozen.SELF),
        'consumer_main_preimage':rel(PREIMAGE),'consumer_main_preimage_sha256':sha(PREIMAGE),
        'called_function':'certify_selected_minor_clearing_child_mirror_probe_v2.validate',
        'mathematical_validator_unchanged':True,
        'producer_sha256':sha(stage.SELF),
        'certificate':rel(certificate),'certificate_sha256':sha(certificate),
        'certificate_report_bytes_equal_frozen_validate':True,
        'validated':True,'Lean_started':False,'API_used':False}
    invocation_raw=stage.encode(invocation)
    if INVOCATION.exists():
        need(INVOCATION.read_bytes()==invocation_raw,'Existing adapter invocation differs')
    elif args.certify_existing:
        INVOCATION.write_bytes(invocation_raw)
    else:
        need(False,'Check-only requires the existing invocation provenance')
    print(json.dumps({'certificate':rel(certificate),'certificate_sha256':sha(certificate),
        'invocation_record':rel(INVOCATION),'invocation_record_sha256':sha(INVOCATION),
        'validated':True,'Std3_only':report['Std3_only'],
        'max_file_seconds':report['max_file_seconds'],
        'Lean_started':False,'API_used':False},indent=2))

if __name__=='__main__':main()
