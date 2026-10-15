"""Strict offline actual type/reference/Std3 certificate for Accepted LogDiv mirror."""
from __future__ import annotations
import argparse, json
from pathlib import Path
import stage_log_div_child_mirror as stage
import certify_sum_weight_child_mirror as common
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing
import validate_namespace_context_providers as context

SELF=Path(__file__).resolve();read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel


def validate():
    stage.check_only();prep=read(stage.STAGE/'preparation.json')
    need(prep['original_AST_units']==1 and prep['original_source_lines']==19
         and prep['private_helper_names']==[] and prep['public_platform_boundary_names']==[stage.TARGET]
         and prep['all_original_proof_suffixes_unchanged'] is True,'Literal single public source target differs')
    records={}
    for i,(f,mode,module) in enumerate([(stage.OUTPUT,'emit-olean',stage.MODULE),
        (stage.SOURCE_SNAPSHOT,'modecheck','SourceSnapshot'),(stage.GENERATED_SNAPSHOT,'modecheck','GeneratedSnapshot')],1):
        r=context.record(stage.STAGE/f,stage.STAGE/f'c{i}.json',mode,module,stage.STAGE);d=r['data']
        need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False
             and 0<d['seconds']<=300 and d['timeout_seconds']==300 and d['mode']==mode
             and 'emit_olean' not in d and d['runner']==rel(stage.RUNNER)
             and d['runner_sha256']==sha(stage.RUNNER) and d['legacy_runner_sha256']==sha(stage.LEGACY_RUNNER)
             and d['cleanup_completed'] is True,'Actual bounded standard mirror context differs')
        if mode=='modecheck':need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Snapshot emitted OLean')
        records[f]=r
    olean=stage.V/'staged-build/lib/lean'/Path(stage.OUTPUT).with_suffix('.olean')
    need(records[stage.OUTPUT]['data']['output_olean_sha256']==sha(olean),'Mirror actual OLean differs')
    dep=kernel.imported_dep(records[stage.GENERATED_SNAPSHOT],stage.MODULE)
    need(Path(dep['path']).resolve()==olean.resolve() and dep['sha256_before']==sha(olean),'Generated snapshot imported a different actual OLean')
    st=common.type_rows(stage.STAGE/stage.SOURCE_TYPE_JSON,records[stage.SOURCE_SNAPSHOT],[stage.TARGET])
    gt=common.type_rows(stage.STAGE/stage.GENERATED_TYPE_JSON,records[stage.GENERATED_SNAPSHOT],[stage.TARGET])
    sr=common.proof_rows(stage.STAGE/stage.SOURCE_REFS_JSON,records[stage.SOURCE_SNAPSHOT],'source',[stage.TARGET],stage.SOURCE_MODULE)
    gr=common.proof_rows(stage.STAGE/stage.GENERATED_REFS_JSON,records[stage.GENERATED_SNAPSHOT],'generated',[stage.TARGET],stage.MODULE)
    mapping={stage.TARGET:stage.TARGET}
    mapping.update(pairing.pair_extra({n:r for n,r in sr.items() if n!=stage.TARGET},
                                     {n:r for n,r in gr.items() if n!=stage.TARGET},mapping))
    need(kernel.normalized_type(read(stage.OLD/'original-type.json')[0])==kernel.normalized_type(st[stage.TARGET])
         and kernel.normalized_type(st[stage.TARGET])==kernel.normalized_type(gt[stage.TARGET]),
         'Historical Accepted/full source/generated kernel type differs')
    for name,mapped in mapping.items():
        a,b=sr[name],gr[mapped]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1]
             and a['axioms']==b['axioms'],'Actual source/generated CI full type/Std3 differs: '+name)
        for f in ['typeRefs','valueRefs','allUsedConstants']:
            need({mapping.get(n,n) for n in a[f]}==set(b[f]),'Actual source/generated CI references differ: '+name+':'+f)
        need(not any(n.startswith('OAI.') or n.startswith('_private.') and '.OAI.' in n
                     for n in b['allUsedConstants'] if n not in gr),'Unknown project proof reference')
    inventory=common.written(stage.STAGE/stage.INVENTORY_JSON,records[stage.GENERATED_SNAPSHOT])
    need(set(inventory)=={'schemaVersion','probeMainModule','mirrorModule','rawOwnedNames','rawOwnedCIs'}
         and inventory['schemaVersion']==1 and inventory['probeMainModule']=='GeneratedSnapshot'
         and inventory['mirrorModule']==stage.MODULE
         and inventory['rawOwnedNames']==sorted(gr)
         and [r['name'] for r in inventory['rawOwnedCIs']]==sorted(gr),
         'Raw complete owned CI domain differs; early inventory preserved for exact audit')
    public=[]
    for row in inventory['rawOwnedCIs']:
        need(set(row)=={'name','kind','privateUserName','owner','levelParams','closedType','closedValue','isProp','type','typeRefs','valueRefs','allUsedConstants','axioms'}
             and row['kind']=='theorem' and row['closedType'] is True and row['closedValue'] is True
             and row['isProp'] is True,'Actual owned CI is not a closed theorem proposition')
        kernel.imported_owner(row,stage.MODULE)
        actual=gr[row['name']]
        need(all(row[f]==actual[f] for f in ['owner','levelParams','type','typeRefs','valueRefs','allUsedConstants','axioms']),
             'Actual raw owned CI differs from full proof-reference export')
        if row['privateUserName'] is None:public.append(row['name'])
    need(public==[stage.TARGET],'Additional public compiler helper requires isolated explicit audit')
    return {'schema_version':1,'artifact_kind':'ap19-original-name-closed-log-div-child-mirror-validation',
        'source_commit':prep['source_commit'],'source_name':stage.TARGET,'platform_module':stage.MODULE,
        'accepted_theorem_id':prep['historical_Accepted_theorem_id'],'accepted_proof_id':prep['historical_Accepted_proof_id'],
        'accepted_evidence_sha256':sha(stage.OLD/'publication.json'),'public_platform_boundary_names':public,
        'actual_private_helper_mappings':[],'actual_automatic_CI_pairs':mapping,
        'raw_owned_inventory_exact':True,'no_uncertified_owned_CI':True,
        'source_and_generated_types_equal':True,'source_and_generated_actual_proof_references_paired':True,
        'references_bitwise_equal_under_actual_mapping':True,'all_original_proof_suffixes_unchanged':True,
        'historical_Accepted_wire_and_type_verified':True,'Std3_only':True,
        'provider_olean':rel(olean),'provider_olean_sha256':sha(olean),'preparation_sha256':sha(stage.STAGE/'preparation.json'),
        'generated_json_sha256':{f:sha(stage.STAGE/f) for f in [stage.SOURCE_TYPE_JSON,stage.GENERATED_TYPE_JSON,stage.SOURCE_REFS_JSON,stage.GENERATED_REFS_JSON,stage.INVENTORY_JSON]},
        'preflights':records,'actual_source_and_generated_CI_count':len(mapping),
        'implementation_hashes':{rel(p):sha(p) for p in [SELF,stage.SELF,Path(common.__file__),Path(kernel.__file__),Path(pairing.__file__),Path(context.__file__)]},
        'max_file_seconds':max(r['data']['seconds'] for r in records.values()),
        'validated':True,'submission_ready':False,'Lean_started_by_consumer':False,'API_used':False}


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    report=validate();path=stage.STAGE/stage.CERTIFICATE;raw=stage.encode(report)
    if path.exists():need(path.read_bytes()==raw,'Existing immutable LogDiv mirror certificate differs')
    elif a.certify_existing:path.write_bytes(raw)
    else:need(False,'Actual LogDiv mirror certificate pending')
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path),'validated':True,
        'max_file_seconds':report['max_file_seconds'],'Lean_started':False,'API_used':False},indent=2))


if __name__=='__main__':main()
