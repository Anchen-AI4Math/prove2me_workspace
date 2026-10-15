"""Strict isolated AP17 repaired metadata replay with genuine original emitter."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_lower_child_mirror_probe_v3 as stage
import certify_selected_minor_arithmetic_lower_bound_node_v2 as source_consumer
import certify_selected_minor_clearing_bound_node as pairing
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context
SELF=Path(__file__).resolve();STD3={'propext','Classical.choice','Quot.sound'}
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel
ACCEPTED=stage.ACCEPTED

def accepted_record(record):
    parent=stage.parent;body=record.get('target_readback',{}).get('body',{});verdict=record.get('last_verify_verdict',{}).get('body',{})
    need(record.get('confirmed_proved') is True and verdict.get('status')=='ACCEPTED' and body.get('status')=='Proved','Generic private mirror requires real Accepted/Proved parent')
    need(record.get('theorem_name')==parent.TARGET and body.get('theorem_name')==parent.TARGET and isinstance(record.get('theorem_id'),str) and record['theorem_id'] and body.get('theorem_id')==verdict.get('theorem_id')==record['theorem_id'] and isinstance(verdict.get('id'),str) and verdict['id'],'Accepted generic parent identity differs')
    need(record['target_readback']['http_status']==record['last_verify_verdict']['http_status']==200 and (body['preamble']+body['formal_statement']).encode()==(parent.STAGE/parent.TARGET_OUTPUT).read_bytes(),'Accepted generic parent exact wire differs')
    need(record['preparation']['validation_sha256']==sha(stage.PARENT_CERTIFICATE) and record['preparation']['solution_sha256']==sha(parent.STAGE/parent.SOLUTION_OUTPUT),'Accepted generic proof does not bind actual certified source')
    return record

def bind_accepted():
    matches=[]
    for path in stage.parent.STAGE.glob('publication*/publication.json'):
        record=read(path)
        if record.get('confirmed_proved') is True and record.get('last_verify_verdict',{}).get('body',{}).get('status')=='ACCEPTED':matches.append((path,accepted_record(record)))
    need(len(matches)==1,'Await exactly one genuine generic lower Accepted record')
    raw=matches[0][0].read_bytes()
    if ACCEPTED.exists():need(ACCEPTED.read_bytes()==raw,'Frozen generic Accepted record differs')
    else:ACCEPTED.write_bytes(raw)
    return {'bound_actual_Accepted':True,'accepted_evidence_sha256':sha(ACCEPTED),'Lean_started':False,'API_used':False}

def owned_data_equations(mapping_doc, preparation):
    allowed,paths=stage.primary_evidence()
    need(allowed==preparation['certified_auxiliary_primary_definitions'],'Exact Published primary evidence domain differs')
    automatic,_=stage.automatic_evidence()
    need(automatic==preparation['certified_historical_automatic_data_helper_pair'],'Exact historical automatic data-helper evidence differs')
    pair=automatic['pair'];automatic_name=pair['name']
    historical_source=next(r for r in read(stage.TASK/automatic['source_json'])['rows'] if r['name']==automatic_name)
    historical_generated=next(r for r in read(stage.TASK/automatic['generated_json'])['rows'] if r['name']==automatic_name)
    kernel.evidence_row(historical_source,name=automatic_name,module=pair['source_owner']['module'],helper=True)
    kernel.evidence_row(historical_generated,name=automatic_name,module=pair['generated_owner']['module'],helper=True)
    need(kernel.normalized_type(historical_source)==kernel.normalized_type(historical_generated) and historical_source['axioms']==historical_generated['axioms'] and all(historical_source[k]==historical_generated[k] for k in ['typeRefs','valueRefs','allUsedConstants']),'Historical automatic data proof kernel pair differs')
    by_name={r['name']:r for r in allowed};rows=mapping_doc['ownedDataEquations'];names=[r['actualName'] for r in rows]
    public=mapping_doc['actualOwnedPublicNames']
    need(names==sorted(set(names)) and set(names)==set(public)-set([stage.parent.TARGET]+stage.EQUATIONS),'Actual public auxiliary CI inventory is not complete or exact')
    result=[]
    for row in rows:
        need(set(row)=={'actualName','primaryName','primaryExpectedModule','inverseGetter','inversePrimary','getter','actualEquationNames','unfoldingGetter','actualUnfoldingName','candidateBasis','provenanceRoute','kernelEqualityProbe','primaryBinding','equation','closedEquationProofReferences','actualCertifiedAutomaticDataHelpers'},'Auxiliary data-equation provenance shape differs')
        name,primary=row['actualName'],row['primaryName'];need(primary in by_name,'Auxiliary inverse primary has no exact full Def certificate')
        binding=by_name[primary];module=binding['module']
        need(row['inverseGetter']=='Lean.Meta.isEqnThm?' and row['getter']=='Lean.Meta.getEqnsFor?' and row['unfoldingGetter']=='Lean.Meta.getUnfoldEqnFor?' and row['inversePrimary'] in [None,primary] and row['primaryExpectedModule']==module,'Actual nullable auxiliary getter/inverse/owner differs')
        equations=row['actualEquationNames'];need(equations is None or isinstance(equations,list) and len(equations)==len(set(equations)) and all(isinstance(n,str) for n in equations),'Actual nullable equation array differs')
        unfolding=row['actualUnfoldingName'];need(unfolding is None or isinstance(unfolding,str),'Actual nullable unfolding getter differs')
        route='equation-registry-forward' if name in (equations or []) else 'unfolding-registry-forward' if unfolding==name else 'closed-typed-definitional-equality'
        need(row['provenanceRoute']==route and row['candidateBasis']=='actual closed CI forall/Eq lhs head constant','Honest auxiliary provenance route differs')
        fields={'actualName','userName','levelParams','kind','type','value','owner','axioms'}
        pr,eq=row['primaryBinding'],row['equation'];need(set(pr)==set(eq)==fields and pr['actualName']==pr['userName']==primary and pr['kind']=='def' and pr['value'] is not None and eq['actualName']==eq['userName']==name and eq['kind']=='theorem' and eq['value'] is None,'Official auxiliary equation or primary complete CI differs')
        for ci,expected in [(pr,module),(eq,stage.MODULE)]:
            owner=ci['owner'];need(set(owner)=={'kind','index','module'} and owner['kind']=='ImportedModule' and owner['module']==expected and type(owner['index']) is int and owner['index']>=0,'Official auxiliary equation/primary actual imported owner differs')
            kernel.checked_expr(ci['type'],set(ci['levelParams']));need(len(ci['axioms'])==len(set(ci['axioms'])) and set(ci['axioms'])<=STD3,'Auxiliary CI axioms exceed Std3')
        probe=row['kernelEqualityProbe']
        need(set(probe)=={'checker','transparency','constantApproximation','binderCount','closedEqualityType','closedBeforeAndAfter','noMetavariablesBeforeAndAfter','lhsHeadConstant','definitionalEquality'} and probe['checker']=='Lean.Meta.isDefEqNoConstantApprox' and probe['transparency']=='all' and probe['constantApproximation'] is False and probe['closedBeforeAndAfter'] is True and probe['noMetavariablesBeforeAndAfter'] is True and probe['definitionalEquality'] is True and probe['lhsHeadConstant']==primary and type(probe['binderCount']) is int and probe['binderCount']>=0,'Actual no-approximation closed auxiliary defEq check differs')
        kernel.checked_expr(probe['closedEqualityType'],set(eq['levelParams']))
        need(probe['closedEqualityType']==eq['type'],'Reclosed actual equality telescope differs from full theorem CI type')
        body=eq['type'];count=0
        while isinstance(body,list) and body and body[0]=='forall':count+=1;body=body[3]
        args=[];head=body
        while isinstance(head,list) and head and head[0]=='app':args.append(head[2]);head=head[1]
        args.reverse();need(isinstance(head,list) and head[:2]==['const','Eq'] and len(args)==3 and count==probe['binderCount'],'Actual auxiliary type is not exactly the recorded forall/Eq telescope')
        lhs=args[1]
        while isinstance(lhs,list) and lhs and lhs[0]=='app':lhs=lhs[1]
        need(isinstance(lhs,list) and lhs[:2]==['const',primary],'Auxiliary inverse primary does not match actual Eq lhs head constant')
        kernel.checked_expr(pr['value'],set(pr['levelParams']))
        original={r['sourceName']:r for r in map(json.loads,(stage.TASK/binding['source_json']).read_bytes().splitlines())}[primary]
        generated={r['sourceName']:r for r in map(json.loads,(stage.TASK/binding['generated_json']).read_bytes().splitlines())}[primary]
        need(pr['levelParams']==original['levelParams']==generated['levelParams'] and pr['type']==original['type']==generated['type'] and pr['value']==original['value']==generated['value'] and sorted(pr['axioms'])==original['axioms']==generated['axioms'],'Auxiliary primary full Def type/value/Std3 differs from original/Published actual witnesses')
        proof=row['closedEquationProofReferences'];kernel.evidence_row(proof,name=name,module=stage.MODULE,helper=True)
        need(kernel.normalized_type(eq)==kernel.normalized_type(proof) and sorted(eq['axioms'])==proof['axioms'],'Auxiliary official equation full type/closed proof/Std3 evidence differs')
        cached=row['actualCertifiedAutomaticDataHelpers'];cached_names=[]
        for exported in cached:
            need(set(exported)=={'actualIsProp','CI'} and exported['actualIsProp'] is True,'Automatic data cache is not an actual genuine Prop CI')
            ci=exported['CI'];need(ci['name']==automatic_name,'Unrecorded automatic data-helper CI')
            kernel.evidence_row(ci,name=automatic_name,module=pair['generated_owner']['module'],helper=True)
            need(kernel.normalized_type(ci)==kernel.normalized_type(historical_generated) and ci['axioms']==historical_generated['axioms'] and all(ci[k]==historical_generated[k] for k in ['typeRefs','valueRefs','allUsedConstants']),'Actual automatic data-helper full type/refs/Std3 differs from original/Published kernel pair')
            cached_names.append(ci['name'])
        need(cached_names==([automatic_name] if automatic_name in proof['allUsedConstants'] else []),'Actual auxiliary cache-CI reference/export finite domain differs')
        for n in proof['allUsedConstants']:
            if n.startswith('OAI.') or n.startswith('_private.') and '.OAI.' in n:
                need(n in by_name or n in names or n in stage.EQUATIONS or n in preparation['provider_subtracted_names'] or n in cached_names,'Auxiliary data equation uses an uncertified project constant')
        result.append({'actual_name':name,'primary_name':primary,'official_getter_and_nullable_inverse_results_recorded':True,'inverse_primary':row['inversePrimary'],'actual_equation_names':equations,'actual_unfolding_name':unfolding,'provenance_route':route,'kernel_no_approximation_definitional_equality_verified':True,'full_primary_definition_equals_original_and_Published':True,'equation_full_type_closed_proof_and_Std3_verified':True,'equation_owner':eq['owner'],'primary_owner':pr['owner'],'primary_certificate_sha256':binding['certificate_sha256'],'primary_publication_sha256':binding['publication_sha256'],'exact_additional_project_ref_boundary_from_historical_source_certificate':preparation['provider_subtracted_names'],'actual_automatic_data_helper_names':cached_names,'historical_automatic_data_helper_certificate_sha256':automatic['certificate_sha256'],'actual_automatic_cache_types_closed_proofs_all_refs_owners_and_Std3_paired':True,'data_equation_not_an_additional_platform_theorem_interface':True})
    return result

def validate():
    stage.check_only();parent=stage.parent;p=read(stage.STAGE/'preparation.json')
    previous=source_consumer.validate();need(stage.encode(previous)==(stage.PARENT_CERTIFICATE).read_bytes(),'Actual AP16 source certificate replay differs')
    need(ACCEPTED.is_file(),'Generic mirror platform boundary awaits genuine Accepted readback');accepted=accepted_record(read(ACCEPTED))
    records={}
    for i,(filename,mode,module) in enumerate([(stage.OUTPUT,'emit-olean',stage.MODULE),(stage.SNAPSHOT,'modecheck','GeneratedSnapshot')],1):
        root=stage.EMITTER_STAGE if i==1 else stage.STAGE
        r=context.record(root/filename,root/f'c{i}.json',mode,module,root);d=r['data']
        need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300 and d['timeout_seconds']==300 and d['mode']==mode and 'emit_olean' not in d,'Actual generic mirror bounded preflight failed')
        need(d.get('runner')==rel(stage.RUNNER) and d.get('runner_sha256')==sha(stage.RUNNER) and d.get('legacy_runner_sha256')==sha(stage.LEGACY_RUNNER) and d.get('cleanup_completed') is True,'Actual generic mirror runner provenance differs')
        if mode=='modecheck':need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Snapshot unexpectedly emitted OLean')
        records[filename]=r
    olean=parent.clearing.base.runner.STAGED_LIB/Path(stage.OUTPUT).with_suffix('.olean');need(records[stage.OUTPUT]['data']['output_olean_sha256']==sha(olean),'Actual generic mirror OLean differs')
    dep=kernel.imported_dep(records[stage.SNAPSHOT],stage.MODULE);need(Path(dep['path']).resolve()==olean.resolve() and dep['sha256_before']==sha(olean),'Generic snapshot imported a different actual mirror OLean')
    old_deps=previous['preflights'][parent.SOLUTION_OUTPUT]['data']['dependency_oleans'];new_deps=records[stage.OUTPUT]['data']['dependency_oleans']
    fields=['module','path','sha256_before'];need([{k:r[k] for k in fields} for r in old_deps]==[{k:r[k] for k in fields} for r in new_deps],'Generic mirror source solution import/OLean environment differs')
    mapping_doc=source_consumer.written(stage.STAGE/stage.MAPPING_JSON,records[stage.SNAPSHOT])
    need(set(mapping_doc)=={'schemaVersion','probeMainModule','mirrorModule','mapping','publicTarget','actualOwnedPublicNames','officialDataEquationCandidates','ownedDataEquations'} and mapping_doc['schemaVersion']==1 and mapping_doc['probeMainModule']=='GeneratedSnapshot' and mapping_doc['mirrorModule']==stage.MODULE and mapping_doc['publicTarget']==parent.TARGET and mapping_doc['officialDataEquationCandidates']==[],'Exact actual generic private mapping envelope differs')
    helpers=p['private_helper_names'];pairs=mapping_doc['mapping'];need(len(pairs)==21 and [r['sourceName'] for r in pairs]==helpers and len({r['actualName'] for r in pairs})==21,'Actual private lower finite domain differs')
    roots_map={}
    for row in pairs:
        need(set(row)=={'sourceName','actualName','privateUserName','owner'} and row['privateUserName']==row['sourceName'] and row['actualName']!=row['sourceName'],'Actual private lower identity differs');kernel.imported_owner(row,stage.MODULE);roots_map[row['sourceName']]=row['actualName']
    public=mapping_doc['actualOwnedPublicNames'];need(public==sorted(set(public)) and parent.TARGET in public and not set(helpers)&set(public),'Generic lower mirror publicly exposes an original helper')
    inventory=source_consumer.written(stage.STAGE/stage.INVENTORY_JSON,records[stage.SNAPSHOT])
    need(set(inventory)=={'schemaVersion','probeMainModule','mirrorModule','actualOwnedPublicNames','rows'} and inventory['schemaVersion']==1 and inventory['probeMainModule']=='GeneratedSnapshot' and inventory['mirrorModule']==stage.MODULE and inventory['actualOwnedPublicNames']==public,'Actual early owned-CI inventory envelope differs')
    need([r['actualName'] for r in inventory['rows']]==public,'Actual early inventory omits owned public CI')
    for row in inventory['rows']:
        need(set(row)=={'actualName','binderCount','closedForallEqLhsHead','actualEquationNames','actualUnfoldingName','inversePrimary','CI'},'Early inventory full CI/getter shape differs')
        kernel.evidence_row(row['CI'],name=row['actualName'],module=stage.MODULE,helper=True)
    auxiliary=owned_data_equations(mapping_doc,p)
    for actual in mapping_doc['ownedDataEquations']:
        row=next(r for r in inventory['rows'] if r['actualName']==actual['actualName'])
        need(row['closedForallEqLhsHead']==actual['primaryName'] and row['binderCount']==actual['kernelEqualityProbe']['binderCount'] and row['CI']==actual['closedEquationProofReferences'],'Actual early closed CI/forall-Eq lhs provenance differs from strict final export')

    roots_map[parent.TARGET]=parent.TARGET
    source_names=helpers+[parent.TARGET];generated_names=[roots_map[n] for n in source_names];boundary=set(p['provider_subtracted_names'])
    source_pf=previous['preflights'][parent.SOURCE_SNAPSHOT]
    source=source_consumer.types(parent.SOURCE_TYPE_JSON,source_pf,source_names)
    source_refs=source_consumer.proofs(parent.SOURCE_REFS_JSON,source_pf,'source',source_names,list(parent.HELPER_NAMES),boundary)
    saved=source_consumer.STAGE
    try:
        source_consumer.STAGE=stage.STAGE
        generated=source_consumer.types(stage.TYPE_JSON,records[stage.SNAPSHOT],generated_names)
        generated_refs=source_consumer.proofs(stage.REFS_JSON,records[stage.SNAPSHOT],'generated',generated_names,[stage.MODULE,*parent.IMPORTS,'GeneratedSnapshot'],boundary)
    finally:source_consumer.STAGE=saved
    mapping=pairing.pair_extra({n:r for n,r in source_refs.items() if n not in roots_map},{n:r for n,r in generated_refs.items() if n not in roots_map.values()},roots_map)
    for n,m in roots_map.items():
        need(kernel.normalized_type(source[n])[0]==kernel.normalized_type(generated[m])[0] and kernel.rename_expr(kernel.normalized_type(source[n])[1],mapping)==kernel.normalized_type(generated[m])[1],'Original/private generic full type differs')
    historical=previous.get('actual_external_instance_reference_differences',{});observed={}
    for n,m in mapping.items():
        a,b=source_refs[n],generated_refs[m];need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1] and a['axioms']==b['axioms'],'Private generic CI full type/Std3 differs')
        for key in ['typeRefs','valueRefs','allUsedConstants']:
            left={mapping.get(x,x) for x in a[key]};right=set(b[key]);source_only=sorted(left-right);generated_only=sorted(right-left)
            project=lambda x:x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x
            need({x for x in left if project(x)}=={x for x in right if project(x)},'Generic private project refs drift under exact actual mapping')
            if source_only or generated_only:
                expected=historical.get(n);need(key!='typeRefs' and expected is not None and source_only==expected['source_only'] and generated_only==expected['generated_only'] and all(not project(x) for x in source_only+generated_only),'Generic mirror has unrecorded external instance drift')
                observed.setdefault(n,{'source_only':source_only,'generated_only':generated_only,'fields':[]})['fields'].append(key)
        for x in b['allUsedConstants']:
            if x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x:need(x in generated_refs or x in boundary,'Generic mirror project dependency lacks closed provenance')
    for row in pairs:need(generated_refs[row['actualName']]['owner']==row['owner'],'Private generic proof owner differs from exact resolver')
    return {'schema_version':1,'artifact_kind':'ap17-generic-private-lower-child-probe-v3-validation','source_commit':parent.COMMIT,'source_name':parent.TARGET,'platform_module':stage.MODULE,'public_platform_boundary_names':[parent.TARGET],'actual_private_helper_mappings':pairs,'private_helper_count':21,'actual_owned_public_names':public,'actual_owned_auxiliary_data_equations':auxiliary,'all_project_references_exact_under_actual_private_mapping':True,'source_and_generated_types_equal':True,'source_and_generated_actual_proof_references_paired':True,'all_original_proof_suffixes_unchanged':True,'historical_source_certificate_sha256':sha(stage.PARENT_CERTIFICATE),'accepted_parent_Proved':True,'accepted_evidence_sha256':sha(ACCEPTED),'accepted_theorem_id':accepted['theorem_id'],'accepted_proof_id':accepted['last_verify_verdict']['body']['id'],'platform_boundary_certification_pending':False,'published_wire_unchanged':True,'provider_source_sha256':sha(stage.EMITTER_STAGE/stage.OUTPUT),'provider_olean':rel(olean),'provider_olean_sha256':sha(olean),'preparation_sha256':sha(stage.STAGE/'preparation.json'),'reused_emitter_root':rel(stage.EMITTER_STAGE),'reused_emitter_preflight_sha256':p['reused_emitter_preflight_sha256'],'failed_original_probe_preflight_sha256':p['failed_original_probe_preflight_sha256'],'exact_v4_provenance_block_sha256':p['inserted_exact_provenance_block_sha256'],'exact_six_AP9_complete_Def_witnesses_added':True,'actual_certified_primary_Def_domain_size':23,'early_owned_inventory_export_full_CI_verified':True,'failed_v2_probe_preflight_sha256':p['failed_v2_probe_preflight_sha256'],'proof_source_and_OLean_unchanged':True,'preflights':records,'actual_external_instance_reference_differences':observed,'historical_external_instance_difference_contract':historical,'generated_json_sha256':{f:sha(stage.STAGE/f) for f in [stage.TYPE_JSON,stage.REFS_JSON,stage.MAPPING_JSON,stage.INVENTORY_JSON]},'implementation_hashes':{rel(f):sha(f) for f in [SELF,stage.SELF,stage.RUNNER,stage.LEGACY_RUNNER,stage.mechanism.SELF,Path(source_consumer.__file__),Path(pairing.__file__),Path(kernel.__file__),Path(context.__file__)]},'Std3_only':True,'max_file_seconds':max(r['data']['seconds'] for r in records.values()),'validated':True,'submission_ready':False,'Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    for flag in ['check-candidate','bind-accepted','certify-existing','check-only']:g.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    if a.check_candidate:print(json.dumps(stage.check_candidate(),indent=2));return
    if a.bind_accepted:print(json.dumps(bind_accepted(),indent=2));return
    report=validate();path=stage.STAGE/stage.CERTIFICATE;raw=stage.encode(report)
    if path.exists():need(path.read_bytes()==raw,'Existing immutable generic child certificate differs')
    elif a.certify_existing:path.write_bytes(raw)
    else:need(False,'Check-only requires existing actual generic child certificate')
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path),'validated':True,'Std3_only':True,'max_file_seconds':report['max_file_seconds'],'Lean_started':False,'API_used':False},indent=2))
if __name__=='__main__':main()
