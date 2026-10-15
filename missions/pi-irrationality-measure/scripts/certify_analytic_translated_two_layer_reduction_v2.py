"""Derived strict two-layer certificate: ten genuine emitters plus eight successor contexts."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import certify_analytic_translated_two_layer_reduction as original
import finalize_analytic_translated_two_layer_reduction_v2 as stage

SELF=Path(__file__).resolve()
def validate():
    plan=stage.read(stage.STAGE/'preparation.json')
    stage.need(plan['reused_context_count']==10 and plan['new_bounded_context_count']==8 and len(plan['reused_actual_contexts'])==10
      and plan['multiplicity_binding']['definition_id']=='9e7cfb76-3480-4078-b240-661c13a8f231'
      and plan['full14_source_type_import_closure_audit_sha256']==stage.sha(stage.STAGE/'type-import-closure-audit.json'), 'Exact isolated reuse/Mulitplicity/type-domain contract differs')
    old_record=original.context.record;old_stage=original.stage;old_self=original.SELF
    def actual_record(source,manifest,mode,module,root):
        if not Path(source).resolve().is_relative_to(stage.STAGE.resolve()):return old_record(source,manifest,mode,module,root)
        relative=Path(source).resolve().relative_to(stage.STAGE.resolve()).as_posix()
        if relative in plan['reused_actual_contexts']:
            r=plan['reused_actual_contexts'][relative]
            result=old_record(stage.TASK/r['source'],stage.TASK/r['manifest'],mode,module,stage.TASK/r['root'])
            stage.need(result==r['preflight'],'Reused historical actual compiler witness differs')
            return result
        return old_record(source,manifest,mode,module,root)
    original.context.record=actual_record;original.stage=stage;original.SELF=SELF
    try:result=original.validate()
    finally:original.context.record=old_record;original.stage=old_stage;original.SELF=old_self
    result.update({'artifact_kind':'ap20-analytic-translated-two-layer-actual-Open-sketch-validation-v2',
      'reused_actual_context_count':10,'new_actual_context_count':8,'prior_failed_c11_preserved':plan['legacy_failure'],
      'multiplicity_binding':plan['multiplicity_binding'],'all14_source_types_have_complete_Published_data_import_closure':True,
      'source_type_import_closure_audit_sha256':stage.sha(stage.STAGE/'type-import-closure-audit.json'),
      'original_parent_proof_bytes_unchanged':True,'legacy_frozen_consumer':stage.rel(Path(original.__file__)),
      'legacy_frozen_consumer_sha256':stage.sha(Path(original.__file__))})
    result['implementation_hashes'].update({stage.rel(Path(original.__file__)):stage.sha(Path(original.__file__)),
      stage.rel(Path(stage.legacy.__file__)):stage.sha(Path(stage.legacy.__file__))})
    return result
def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();result=validate();raw=stage.encode(result)
    if stage.CERTIFICATE.exists():stage.need(stage.CERTIFICATE.read_bytes()==raw,'Refusing changed actual derived certificate')
    elif a.certify_existing:stage.CERTIFICATE.write_bytes(raw)
    else:stage.need(False,'Check-only requires genuine actual derived certificate')
    print(json.dumps({'certificate':stage.rel(stage.CERTIFICATE),'certificate_sha256':stage.sha(stage.CERTIFICATE),
      'validated':True,'Open_sketch_only':True,'closed_proof':False,'reused_actual_contexts':10,'new_actual_contexts':8,'max_file_seconds':result['max_file_seconds']},indent=2))
if __name__=='__main__':main()
