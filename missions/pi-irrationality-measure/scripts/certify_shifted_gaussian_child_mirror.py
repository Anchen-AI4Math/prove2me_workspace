"""Strict pure replay of two local closed-child contexts against historical AP13 source evidence."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_shifted_gaussian_child_mirror as stage
import certify_shifted_gaussian_node as old
import validate_namespace_context_providers as context
import certify_full_row_minor_node as kernel
SELF=Path(__file__).resolve()
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel

def validate():
    stage.check_only();parent=stage.parent
    previous=old.validate();need(parent.encode(previous)==(parent.STAGE/parent.CERTIFICATE).read_bytes(),'Historical AP13 certificate does not replay exactly')
    p=read(stage.STAGE/'preparation.json');records={}
    for i,(f,mode,module) in enumerate([(stage.OUTPUT,'emit-olean',stage.MODULE),(stage.SNAPSHOT,'modecheck','GeneratedSnapshot')],1):
        pf=context.record(stage.STAGE/f,stage.STAGE/f'c{i}.json',mode,module,stage.STAGE);d=pf['data']
        need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300 and d['timeout_seconds']==300 and d['mode']==mode and 'emit_olean' not in d,'Bounded actual local-child compiler did not pass')
        if mode=='modecheck':need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Snapshot emitted OLean')
        records[f]=pf
    olean=parent.base.runner.STAGED_LIB/Path(stage.OUTPUT).with_suffix('.olean');emitter=records[stage.OUTPUT]['data']
    need(emitter['output_olean']==rel(olean) and emitter['output_olean_sha256']==sha(olean),'Closed-child actual OLean differs')
    dep=kernel.imported_dep(records[stage.SNAPSHOT],stage.MODULE)
    need(Path(dep['path']).resolve()==olean.resolve() and dep['stable_during_compile'] is True and dep['sha256_before']==sha(olean),'Snapshot did not import exact emitted child OLean')
    names=p['provided_names'];source_pf=previous['preflights'][parent.SOURCE_SNAPSHOT]
    source=old.type_rows(parent.SOURCE_TYPE_JSON,source_pf,names)
    source_refs=old.proof_rows(parent.SOURCE_REFS_JSON,source_pf,'source',names,[parent.TARGET_MODULE],set())
    saved=old.STAGE
    try:
        old.STAGE=stage.STAGE
        generated=old.type_rows(stage.TYPE_JSON,records[stage.SNAPSHOT],names)
        generated_refs=old.proof_rows(stage.REFS_JSON,records[stage.SNAPSHOT],'generated',names,[stage.MODULE],set())
    finally:old.STAGE=saved
    public_map={n:n for n in names}
    mapping=old.pair_extra({n:r for n,r in source_refs.items() if n not in public_map},{n:r for n,r in generated_refs.items() if n not in public_map},public_map)
    for n in names:
        a,b=source[n],generated[n]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1],'Closed child differs from original full theorem type: '+n)
    for n,m in mapping.items():
        a,b=source_refs[n],generated_refs[m]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1] and a['axioms']==b['axioms'],'Closed child actual CI type/Std3 differs: '+n)
        for field in ['typeRefs','valueRefs','allUsedConstants']:need(sorted({mapping.get(x,x) for x in a[field]})==b[field],'Actual child proof constants differ: '+n+':'+field)
        for x in b['allUsedConstants']:
            if x.startswith('OAI.') or x.startswith('_private.OAI.'):need(x in generated_refs,'Actual child project dependency lacks full proof/source provenance: '+x)
    need(read(stage.STAGE/'preparation.json')['published_wire_sha256']==sha(parent.STAGE/parent.TARGET_OUTPUT),'Existing published wire changed')
    return {'schema_version':1,'artifact_kind':'ap14-closed-child-mirror-validation','source_name':parent.TARGET,'source_commit':parent.COMMIT,'platform_module':stage.MODULE,'provided_names':names,'provider_source_sha256':sha(stage.STAGE/stage.OUTPUT),'provider_olean':rel(olean),'provider_olean_sha256':sha(olean),'preparation_sha256':sha(stage.STAGE/'preparation.json'),'historical_source_certificate':rel(parent.STAGE/parent.CERTIFICATE),'historical_source_certificate_sha256':sha(parent.STAGE/parent.CERTIFICATE),'historical_source_json_sha256':{f:sha(parent.STAGE/f) for f in [parent.SOURCE_TYPE_JSON,parent.SOURCE_REFS_JSON]},'generated_json_sha256':{f:sha(stage.STAGE/f) for f in [stage.TYPE_JSON,stage.REFS_JSON]},'preflights':records,'source_and_generated_types_equal':True,'source_and_generated_actual_proof_references_paired':True,'actual_automatic_CI_pairs':[[n,m] for n,m in mapping.items() if n not in public_map],'axioms':{side:{n:r['axioms'] for n,r in rows.items()} for side,rows in [('source',source_refs),('generated',generated_refs)]},'all_original_port_command_bytes_preserved':True,'existing_port_adaptations':p['existing_port_adaptations'],'published_wire_unchanged':True,'no_global_solution':True,'Std3_only':True,'max_file_seconds':max(x['data']['seconds'] for x in records.values()),'implementation_hashes':{rel(x):sha(x) for x in [SELF,stage.SELF,Path(old.__file__),Path(kernel.__file__),Path(context.__file__)]},'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();r=validate();path=stage.STAGE/stage.CERTIFICATE;raw=stage.encode(r)
    if path.exists():need(path.read_bytes()==raw,'Immutable closed-child certificate changed')
    elif a.certify_existing:path.write_bytes(raw)
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path) if path.exists() else None,'validated':True,'Std3_only':True,'max_file_seconds':r['max_file_seconds'],'Lean_started_by_consumer':False,'API_used':False},indent=2))
if __name__=='__main__':main()
