"""Strict pure replay of two local closed-child contexts against historical AP14 source evidence."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_entry_gaussian_child_mirror as stage
import certify_entry_gaussian_node as old
import validate_namespace_context_providers as context
import certify_full_row_minor_node as kernel
SELF=Path(__file__).resolve()
STD3={'propext','Classical.choice','Quot.sound'}
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel

def equation_pairs(records,source,generated,source_refs,generated_refs):
    pairs=[]
    for index,n in enumerate(stage.parent.EQUATIONS,1):
        docs=[]
        for side,types,refs in [('source',source,source_refs),('generated',generated,generated_refs)]:
            primary,module,filename=stage.parent.equation_specs(side)[index-1];pf=records[stage.parent.SOURCE_SNAPSHOT if side=='source' else stage.parent.GENERATED_SNAPSHOT];d=old.written((stage.parent.STAGE if side=='source' else stage.STAGE)/filename,pf)
            need(set(d)=={'side','expectedModule','primaryBinding','getEqnsForReturnedSome','actualEquationNames','equations','unfolding','probeMainModule','theoremProofValuesExported'} and d['side']==side and d['expectedModule']==module and d['probeMainModule']==('SourceSnapshot' if side=='source' else 'GeneratedSnapshot') and d['getEqnsForReturnedSome'] is True and d['actualEquationNames']==[n] and d['theoremProofValuesExported'] is False and len(d['equations'])==1,'Actual official equation API domain differs: '+n)
            pr=d['primaryBinding'];need(set(pr)=={'actualName','userName','levelParams','kind','type','value','owner','axioms'} and pr['actualName']==pr['userName']==primary and pr['kind']=='def' and pr['value'] is not None and pr['owner']['kind']=='ImportedModule' and set(pr['owner'])=={'kind','index','module'} and pr['owner']['module']==module and type(pr['owner']['index']) is int and pr['owner']['index']>=0,'Actual primary full Def/owner differs')
            kernel.checked_expr(pr['type'],set(pr['levelParams']));kernel.checked_expr(pr['value'],set(pr['levelParams']));need(isinstance(pr['axioms'],list) and len(pr['axioms'])==len(set(pr['axioms'])) and set(pr['axioms'])<=STD3,'Primary Def exceeds Std3')
            eq=d['equations'][0];need(set(eq)=={'getter','inversePrimary','CI'} and eq['getter']=='Lean.Meta.getEqnsFor?' and eq['inversePrimary']==primary,'Official equation inverse primary differs')
            ci=eq['CI'];need(set(ci)==set(pr) and ci['actualName']==ci['userName']==n and ci['kind']=='theorem' and ci['value'] is None and sorted(ci['axioms'])==refs[n]['axioms'] and kernel.normalized_type(ci)==kernel.normalized_type(types[n]),'Actual official equation type/Std3 differs')
            ro=refs[n]['owner'];need(ci['owner']['kind']==ro['kind'] and ci['owner']['module']==ro['module'],'Official equation proof-reference owner differs')
            if d['unfolding'] is not None:
                unfold=d['unfolding'];need(set(unfold)=={'getter','CI'} and unfold['getter']=='Lean.Meta.getUnfoldEqnFor?','Unexpected unfolding theorem getter');uc=unfold['CI'];need(set(uc)==set(pr) and uc['kind']=='theorem' and uc['actualName']==uc['userName'] and uc['value'] is None and set(uc['axioms'])<=STD3 and uc['owner']['module'] in [module,d['probeMainModule']],'Actual unfolding CI differs');kernel.checked_expr(uc['type'],set(uc['levelParams']))
            docs.append(d)
        a,b=docs;pa,pb=a['primaryBinding'],b['primaryBinding']
        need(pa['levelParams']==pb['levelParams'] and pa['type']==pb['type'] and pa['value']==pb['value'] and sorted(pa['axioms'])==sorted(pb['axioms']),'Original/generated complete primary Def type/value/Std3 differs')
        need((a['unfolding'] is None)==(b['unfolding'] is None),'Official unfolding API results differ')
        if a['unfolding'] is not None:
            ua,ub=a['unfolding']['CI'],b['unfolding']['CI'];need(ua['actualName']==ub['actualName'] and kernel.normalized_type(ua)==kernel.normalized_type(ub) and sorted(ua['axioms'])==sorted(ub['axioms']),'Actual original/generated unfolding CI type/Std3 differs')
        pairs.append({'primary':pa['actualName'],'equation':n,'getter':'Lean.Meta.getEqnsFor?','inverse_getter':'Lean.Meta.isEqnThm?','actual_primary_definition_values_equal':True,'equation_types_and_Std3_equal':True,'source_owner':source_refs[n]['owner'],'generated_owner':generated_refs[n]['owner'],'json_sha256':{side+'-equation-'+str(index)+'.json':sha((stage.parent.STAGE if side=='source' else stage.STAGE)/(side+'-equation-'+str(index)+'.json')) for side in ['source','generated']}})
    return pairs

def validate():
    stage.check_only();parent=stage.parent
    previous=old.validate();need(parent.encode(previous)==(parent.STAGE/parent.CERTIFICATE).read_bytes(),'Historical AP14 certificate does not replay exactly')
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
    source_refs=old.proof_rows(parent.SOURCE_REFS_JSON,source_pf,'source',names,list(parent.HELPER_NAMES)+['SourceSnapshot'],set(p['provider_subtracted_names']))
    saved=old.STAGE
    try:
        old.STAGE=stage.STAGE
        generated=old.type_rows(stage.TYPE_JSON,records[stage.SNAPSHOT],names)
        generated_refs=old.proof_rows(stage.REFS_JSON,records[stage.SNAPSHOT],'generated',names,[stage.MODULE,parent.INTERPOLATION['platform_module'],parent.rowdata.PLATFORM_MODULE,'GeneratedSnapshot'],set(p['provider_subtracted_names']))
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
            if x.startswith('OAI.') or x.startswith('_private.OAI.'):need(x in generated_refs or x in p['provider_subtracted_names'],'Actual child project dependency lacks full proof/source provenance: '+x)
    owners={u['name']:u['module'] for u in p['inline_original_AST_units']}
    for n,module in owners.items():need(source_refs[n]['owner']['module']==module and generated_refs[n]['owner']['module']==stage.MODULE,'Original-name public CI actual owner differs: '+n)
    pair_records={parent.SOURCE_SNAPSHOT:source_pf,parent.GENERATED_SNAPSHOT:records[stage.SNAPSHOT]}
    equations=equation_pairs(pair_records,source,generated,source_refs,generated_refs)
    prior={}
    for key,w in previous['actual_provider_bindings'].items():
        module=w['module'];cached=stage.TASK/w['olean'];d=kernel.imported_dep(records[stage.OUTPUT],module)
        need(Path(d['path']).resolve()==cached.resolve() and d['sha256_before']==sha(cached)==w['olean_sha256'],'Local child did not import exact certified prerequisite: '+key)
        prior[key]=w
    need(read(stage.STAGE/'preparation.json')['published_wire_sha256']==sha(parent.STAGE/parent.TARGET_OUTPUT),'Existing published wire changed')
    return {'schema_version':1,'artifact_kind':'ap15-closed-entry-child-mirror-validation','source_name':parent.TARGET,'source_commit':parent.COMMIT,'platform_module':stage.MODULE,'provided_names':names,'provider_source_sha256':sha(stage.STAGE/stage.OUTPUT),'provider_olean':rel(olean),'provider_olean_sha256':sha(olean),'preparation_sha256':sha(stage.STAGE/'preparation.json'),'historical_source_certificate':rel(parent.STAGE/parent.CERTIFICATE),'historical_source_certificate_sha256':sha(parent.STAGE/parent.CERTIFICATE),'historical_source_json_sha256':{f:sha(parent.STAGE/f) for f in [parent.SOURCE_TYPE_JSON,parent.SOURCE_REFS_JSON]},'generated_json_sha256':{f:sha(stage.STAGE/f) for f in [stage.TYPE_JSON,stage.REFS_JSON]},'preflights':records,'source_and_generated_types_equal':True,'source_and_generated_actual_proof_references_paired':True,'official_equation_pairs':equations,'actual_prior_provider_bindings':prior,'public_platform_boundary_names':[parent.TARGET],'mirror_helpers_are_not_public_platform_interfaces':True,'accepted_evidence_sha256':sha(stage.PUBLISHED),'accepted_theorem_id':p['accepted_theorem_id'],'accepted_proof_id':p['accepted_proof_id'],'actual_automatic_CI_pairs':[[n,m] for n,m in mapping.items() if n not in public_map],'axioms':{side:{n:r['axioms'] for n,r in rows.items()} for side,rows in [('source',source_refs),('generated',generated_refs)]},'all_original_port_command_bytes_preserved':True,'existing_port_adaptations':p['existing_port_adaptations'],'published_wire_unchanged':True,'no_global_solution':True,'Std3_only':True,'max_file_seconds':max(x['data']['seconds'] for x in records.values()),'implementation_hashes':{rel(x):sha(x) for x in [SELF,stage.SELF,Path(old.__file__),Path(kernel.__file__),Path(context.__file__)]},'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();r=validate();path=stage.STAGE/stage.CERTIFICATE;raw=stage.encode(r)
    if path.exists():need(path.read_bytes()==raw,'Immutable closed-child certificate changed')
    elif a.certify_existing:path.write_bytes(raw)
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path) if path.exists() else None,'validated':True,'Std3_only':True,'max_file_seconds':r['max_file_seconds'],'Lean_started_by_consumer':False,'API_used':False},indent=2))
if __name__=='__main__':main()
