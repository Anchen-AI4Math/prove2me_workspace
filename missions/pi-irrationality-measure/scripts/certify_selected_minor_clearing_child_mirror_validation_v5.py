"""Derived v5 private clearing-mirror certification from unchanged actual v4 contexts; never Lean/API.

Actual certification is unavailable until the parent actual certificate,
Accepted publication and final two bounded compiler contexts are pinned.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_clearing_child_mirror_probe_v4 as stage
import stage_selected_minor_clearing_child_mirror_validation_v5 as derived
import certify_selected_minor_clearing_bound_node as old
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context
SELF=Path(__file__).resolve();ACCEPTED=stage.ACCEPTED;STD3={'propext','Classical.choice','Quot.sound'}
DERIVED_STAGE=stage.V/'ap16/clearing-child-mirror-validation-v5'
LEDGER=DERIVED_STAGE/'derivation-ledger.json'
FROZEN_V4_CONSUMER=stage.TASK/'scripts/certify_selected_minor_clearing_child_mirror_probe_v4.py'
AUTO_HELPER='OAI.PiExponent.InterpolationMatrix.matrix._proof_1'
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel

def equation_pairs(records, source, generated, source_refs, generated_refs):
    pairs = []
    for index, name in enumerate(stage.parent.EQUATIONS, 1):
        docs = []
        for side, types, refs in [('source', source, source_refs),
                                  ('generated', generated, generated_refs)]:
            primary, module, filename = stage.parent.equation_specs(side)[index - 1]
            pf = records[stage.parent.SOURCE_SNAPSHOT if side == 'source' else stage.parent.GENERATED_SNAPSHOT]
            d = old.written((stage.parent.STAGE if side == 'source' else stage.STAGE) / filename, pf)
            need(set(d) == {'side', 'expectedModule', 'primaryBinding',
                 'getEqnsForReturnedSome', 'actualEquationNames', 'equations',
                 'unfolding', 'probeMainModule', 'theoremProofValuesExported'}
                 and d['side'] == side and d['expectedModule'] == module
                 and d['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
                 and d['getEqnsForReturnedSome'] is True
                 and d['actualEquationNames'] == [name]
                 and d['theoremProofValuesExported'] is False
                 and len(d['equations']) == 1,
                 'Official equation API result differs: ' + name)
            pr = d['primaryBinding']
            need(set(pr) == {'actualName', 'userName', 'levelParams', 'kind',
                 'type', 'value', 'owner', 'axioms'}
                 and pr['actualName'] == pr['userName'] == primary
                 and pr['kind'] == 'def' and pr['value'] is not None
                 and set(pr['owner']) == {'kind', 'index', 'module'}
                 and pr['owner']['kind'] == 'ImportedModule'
                 and pr['owner']['module'] == module
                 and type(pr['owner']['index']) is int and pr['owner']['index'] >= 0,
                 'Official equation primary full Def/owner differs')
            kernel.checked_expr(pr['type'], set(pr['levelParams']))
            kernel.checked_expr(pr['value'], set(pr['levelParams']))
            need(len(pr['axioms']) == len(set(pr['axioms']))
                 and set(pr['axioms']) <= STD3,
                 'Primary Def axioms exceed Std3')
            eq = d['equations'][0]
            need(set(eq) == {'getter', 'inversePrimary', 'CI'}
                 and eq['getter'] == 'Lean.Meta.getEqnsFor?'
                 and eq['inversePrimary'] == primary,
                 'Official equation inverse primary differs')
            ci = eq['CI']
            need(set(ci) == set(pr) and ci['actualName'] == ci['userName'] == name
                 and ci['kind'] == 'theorem' and ci['value'] is None
                 and sorted(ci['axioms']) == refs[name]['axioms']
                 and kernel.normalized_type(ci) == kernel.normalized_type(types[name]),
                 'Official equation CI type/Std3 differs')
            ro = refs[name]['owner']
            need(ci['owner']['kind'] == ro['kind']
                 and ci['owner']['module'] == ro['module'],
                 'Official equation CI actual owner differs')
            if d['unfolding'] is not None:
                u = d['unfolding']
                need(set(u) == {'getter', 'CI'}
                     and u['getter'] == 'Lean.Meta.getUnfoldEqnFor?',
                     'Unexpected unfolding equation getter')
                uc = u['CI']
                need(set(uc) == set(pr) and uc['kind'] == 'theorem'
                     and uc['actualName'] == uc['userName'] and uc['value'] is None
                     and set(uc['axioms']) <= STD3
                     and uc['owner']['module'] in [module, d['probeMainModule']],
                     'Actual unfolding equation CI differs')
                kernel.checked_expr(uc['type'], set(uc['levelParams']))
            docs.append(d)
        a, b = docs
        pa, pb = a['primaryBinding'], b['primaryBinding']
        need(pa['levelParams'] == pb['levelParams']
             and pa['type'] == pb['type'] and pa['value'] == pb['value']
             and sorted(pa['axioms']) == sorted(pb['axioms']),
             'Original/generated primary complete Def type/value/Std3 differs')
        need((a['unfolding'] is None) == (b['unfolding'] is None),
             'Official unfolding API result differs')
        if a['unfolding'] is not None:
            ua, ub = a['unfolding']['CI'], b['unfolding']['CI']
            need(ua['actualName'] == ub['actualName']
                 and kernel.normalized_type(ua) == kernel.normalized_type(ub)
                 and sorted(ua['axioms']) == sorted(ub['axioms']),
                 'Official unfolding CI type/Std3 differs')
        pairs.append({'primary': pa['actualName'], 'equation': name,
                      'getter': 'Lean.Meta.getEqnsFor?',
                      'inverse_getter': 'Lean.Meta.isEqnThm?',
                      'actual_primary_definition_values_equal': True,
                      'equation_types_and_Std3_equal': True,
                      'source_owner': source_refs[name]['owner'],
                      'generated_owner': generated_refs[name]['owner'],
                      'json_sha256': {side + '-equation-' + str(index) + '.json':
                                      sha((stage.parent.STAGE if side == 'source' else stage.STAGE) / (side + '-equation-' + str(index) + '.json'))
                                      for side in ['source', 'generated']}})
    return pairs

def accepted_record(record):
    parent=stage.parent;body=record.get('target_readback',{}).get('body',{});verdict=record.get('last_verify_verdict',{}).get('body',{})
    need(record.get('confirmed_proved') is True and verdict.get('status')=='ACCEPTED' and body.get('status')=='Proved','Private mirror final boundary requires a real Accepted proof and exact Proved readback')
    need(record.get('theorem_name')==parent.TARGET and body.get('theorem_name')==parent.TARGET and isinstance(record.get('theorem_id'),str) and record['theorem_id'] and body.get('theorem_id')==record['theorem_id'] and verdict.get('theorem_id')==record['theorem_id'] and isinstance(verdict.get('id'),str) and verdict['id'],'Actual Accepted parent identity differs')
    need(record['target_readback']['http_status']==200 and record['last_verify_verdict']['http_status']==200 and (body['preamble']+body['formal_statement']).encode()==(parent.STAGE/parent.TARGET_OUTPUT).read_bytes(),'Accepted parent exact platform wire differs')
    need(record['preparation']['validation_sha256']==sha(parent.STAGE/parent.CERTIFICATE) and record['preparation']['solution_sha256']==sha(parent.STAGE/parent.SOLUTION_OUTPUT),'Actual accepted submission does not bind certified original proof')
    return record

def bind_accepted():
    parent=stage.parent;matches=[]
    for p in parent.STAGE.glob('publication*/publication.json'):
        record=read(p)
        if record.get('confirmed_proved') is True and record.get('last_verify_verdict',{}).get('body',{}).get('status')=='ACCEPTED':matches.append((p,accepted_record(record)))
    need(len(matches)==1,'Await exactly one genuine Accepted/Proved parent publication record')
    p,r=matches[0];raw=p.read_bytes()
    if ACCEPTED.exists():need(ACCEPTED.read_bytes()==raw,'Immutable accepted-boundary evidence differs')
    else:ACCEPTED.write_bytes(raw)
    return {'bound_actual_Accepted':True,'accepted_evidence':rel(ACCEPTED),'accepted_evidence_sha256':sha(ACCEPTED),'theorem_id':r['theorem_id'],'proof_id':r['last_verify_verdict']['body']['id'],'Lean_started':False,'API_used':False}

def certified_auto_helper(mapping_doc, preparation, previous, records):
    """Bind the one observed closed AP10 automatic CI from both actual environments."""
    parent=stage.parent
    source_roots=read(parent.STAGE/'preparation.json')['source_type_only_names']
    source_pf=previous['preflights'][parent.SOURCE_SNAPSHOT]
    boundary=set(preparation['provider_subtracted_names'])
    source=old.proof_rows(parent.SOURCE_REFS_JSON,source_pf,'source',source_roots,
                          list(parent.HELPER_NAMES)+['SourceSnapshot'],boundary)
    helper_map={r['sourceName']:r['actualName'] for r in mapping_doc['mapping']}
    generated_roots=[helper_map[n] for n in read(parent.STAGE/'preparation.json')['inline_helper_names']]+[parent.TARGET]+parent.EQUATIONS
    saved=old.STAGE
    try:
        old.STAGE=stage.STAGE
        modules=[stage.MODULE,parent.scales.PLATFORM_MODULE,parent.child.MODULE]+[parent.base.ap10.config(k)['platform_module'] for k in parent.base.ap10.CONFIGS]+['GeneratedSnapshot']
        generated=old.proof_rows(stage.REFS_JSON,records[stage.SNAPSHOT],
                                 'generated',generated_roots,modules,boundary)
    finally:
        old.STAGE=saved
    need(AUTO_HELPER in source and AUTO_HELPER in generated
         and AUTO_HELPER not in source_roots and AUTO_HELPER not in generated_roots,
         'Actual automatic AP10 helper is absent or falsely a public root')
    a,b=source[AUTO_HELPER],generated[AUTO_HELPER]
    expected_source=parent.INTERPOLATION
    expected_generated=parent.base.ap10.config('interpolation')['platform_module']
    need(a['owner']['module']==expected_source and b['owner']['module']==expected_generated
         and kernel.normalized_type(a)==kernel.normalized_type(b)
         and a['axioms']==b['axioms']==['propext']
         and all(a[f]==b[f] for f in ['typeRefs','valueRefs','allUsedConstants'])
         and not any(x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x
                     for x in a['allUsedConstants']),
         'Actual source/Published AP10 automatic helper full type, closed refs, owner or Std3 differs')
    primary_evidence,_=stage.primary_evidence()
    matrix=next((r for r in primary_evidence if r['name']==
                 'OAI.PiExponent.InterpolationMatrix.matrix'),None)
    need(matrix is not None and matrix['module']==expected_generated,
         'Actual matrix full-Def primary lacks published AP10 evidence')
    unknown=[]
    names={r['actualName'] for r in mapping_doc['ownedDataEquations']}
    known=set(preparation['provider_subtracted_names'])|set(parent.EQUATIONS)|names|{r['name'] for r in primary_evidence}
    for row in mapping_doc['ownedDataEquations']:
        for name in row['closedEquationProofReferences']['allUsedConstants']:
            if (name.startswith('OAI.') or name.startswith('_private.') and '.OAI.' in name) and name not in known:
                unknown.append((row['actualName'],name))
    need(unknown==[('OAI.PiExponent.InterpolationMatrix.matrix.eq_1',AUTO_HELPER)],
         'The complete actual auxiliary data-CI project-reference exception domain differs')
    return {'name':AUTO_HELPER,'source_owner':a['owner'],'generated_owner':b['owner'],
            'source_full_type_sha256':stage.sha_bytes(stage.encode(kernel.normalized_type(a))),
            'generated_full_type_sha256':stage.sha_bytes(stage.encode(kernel.normalized_type(b))),
            'source_complete_CI_sha256':stage.sha_bytes(stage.encode(a)),
            'generated_complete_CI_sha256':stage.sha_bytes(stage.encode(b)),
            'typeRefs':a['typeRefs'],'valueRefs':a['valueRefs'],
            'allUsedConstants':a['allUsedConstants'],'axioms':a['axioms'],
            'full_type_and_all_actual_refs_equal':True,'closed_source_and_generated_proof_values':True,
            'only_referenced_by_actual_matrix_equation_outside_original_boundary':True,
            'AP10_matrix_primary_certificate_sha256':matrix['certificate_sha256'],
            'AP10_matrix_primary_publication_sha256':matrix['publication_sha256'],
            'source_refs_json_sha256':sha(parent.STAGE/parent.SOURCE_REFS_JSON),
            'generated_refs_json_sha256':sha(stage.STAGE/stage.REFS_JSON)}

def owned_data_equations(mapping_doc, preparation, auto_helper):
    allowed,paths=stage.primary_evidence()
    need(allowed==preparation['certified_auxiliary_primary_definitions'],'Exact Published primary evidence domain differs')
    by_name={r['name']:r for r in allowed};rows=mapping_doc['ownedDataEquations'];names=[r['actualName'] for r in rows]
    public=mapping_doc['actualOwnedPublicNames']
    need(names==sorted(set(names)) and set(names)==set(public)-set([stage.parent.TARGET]+stage.parent.EQUATIONS),'Actual public auxiliary CI inventory is not complete or exact')
    result=[]
    for row in rows:
        need(set(row)=={'actualName','primaryName','primaryExpectedModule','inverseGetter','inversePrimary','getter','actualEquationNames','unfoldingGetter','actualUnfoldingName','candidateBasis','provenanceRoute','kernelEqualityProbe','primaryBinding','equation','closedEquationProofReferences'},'Auxiliary data-equation provenance shape differs')
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
        for n in proof['allUsedConstants']:
            if n.startswith('OAI.') or n.startswith('_private.') and '.OAI.' in n:
                need(n in by_name or n in names or n in stage.parent.EQUATIONS or n in preparation['provider_subtracted_names'] or n==auto_helper['name'],'Auxiliary data equation uses an uncertified project constant')
        result.append({'actual_name':name,'primary_name':primary,'official_getter_and_nullable_inverse_results_recorded':True,'inverse_primary':row['inversePrimary'],'actual_equation_names':equations,'actual_unfolding_name':unfolding,'provenance_route':route,'kernel_no_approximation_definitional_equality_verified':True,'full_primary_definition_equals_original_and_Published':True,'equation_full_type_closed_proof_and_Std3_verified':True,'equation_owner':eq['owner'],'primary_owner':pr['owner'],'primary_certificate_sha256':binding['certificate_sha256'],'primary_publication_sha256':binding['publication_sha256'],'exact_additional_project_ref_boundary_from_historical_source_certificate':preparation['provider_subtracted_names'],'data_equation_not_an_additional_platform_theorem_interface':True})
    return result

def validate():
    derived.check_only();stage.check_only();parent=stage.parent
    previous=old.validate();need(parent.encode(previous)==(parent.STAGE/parent.CERTIFICATE).read_bytes(),'Historical clearing source certificate does not replay exactly')
    p=read(stage.STAGE/'preparation.json');records={}
    need(p['platform_boundary_certification_pending'] is True and p['real_Accepted_Proved_readback_required_for_final_certificate'] is True and p['private_helper_count']==18 and p['public_platform_boundary_names']==[parent.TARGET],'Frozen kernel/private source boundary preparation differs')
    need(ACCEPTED.is_file(),'Await bound genuine Accepted/Proved readback; kernel compilation alone cannot certify platform boundary')
    accepted=accepted_record(read(ACCEPTED))
    for i,(f,mode,module) in enumerate([(stage.OUTPUT,'emit-olean',stage.MODULE),(stage.SNAPSHOT,'modecheck','GeneratedSnapshot')],1):
        actual_root=stage.EMITTER_STAGE if mode=='emit-olean' else stage.STAGE
        r=context.record(actual_root/f,actual_root/f'c{i}.json',mode,module,actual_root);d=r['data']
        need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300 and d['timeout_seconds']==300 and d['mode']==mode and 'emit_olean' not in d,'Actual bounded mirror compiler failed')
        if mode=='modecheck':
            need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Snapshot emitted OLean')
            need(d.get('runner')==rel(stage.RUNNER) and d.get('runner_sha256')==sha(stage.RUNNER) and d.get('legacy_runner_sha256')==sha(stage.LEGACY_RUNNER) and d.get('cleanup_completed') is True,'Actual snapshot did not use the exact bounded runner')
        records[f]=r
    olean=parent.base.runner.STAGED_LIB/Path(stage.OUTPUT).with_suffix('.olean');e=records[stage.OUTPUT]['data'];need(e['output_olean']==rel(olean) and e['output_olean_sha256']==sha(olean),'Actual private mirror OLean differs')
    dep=kernel.imported_dep(records[stage.SNAPSHOT],stage.MODULE);need(Path(dep['path']).resolve()==olean.resolve() and dep['sha256_before']==sha(olean),'Snapshot imported a different mirror OLean')
    mapping_doc=old.written(stage.STAGE/stage.MAPPING_JSON,records[stage.SNAPSHOT])
    need(set(mapping_doc)=={'schemaVersion','probeMainModule','mirrorModule','mapping','publicTarget','actualOwnedPublicNames','officialDataEquationCandidates','ownedDataEquations'} and mapping_doc['schemaVersion']==1 and mapping_doc['probeMainModule']=='GeneratedSnapshot' and mapping_doc['mirrorModule']==stage.MODULE and mapping_doc['publicTarget']==parent.TARGET and mapping_doc['officialDataEquationCandidates']==parent.EQUATIONS,'Actual exact private-name mapping envelope differs')
    helpers=read(parent.STAGE/'preparation.json')['inline_helper_names'];pairs=mapping_doc['mapping'];need(len(pairs)==18 and [r['sourceName'] for r in pairs]==helpers and len({r['actualName'] for r in pairs})==18,'Actual private-name finite domain differs')
    mapping={}
    for row in pairs:
        need(set(row)=={'sourceName','actualName','privateUserName','owner'} and row['privateUserName']==row['sourceName'] and row['actualName']!=row['sourceName'],'Actual private identity mapping differs')
        kernel.imported_owner(row,stage.MODULE);mapping[row['sourceName']]=row['actualName']
    public=mapping_doc['actualOwnedPublicNames'];need(public==sorted(set(public)) and parent.TARGET in public and not set(helpers)&set(public),'Mirror exports an unintended public source helper')
    auto_helper=certified_auto_helper(mapping_doc,p,previous,records)
    auxiliary_data_equations=owned_data_equations(mapping_doc,p,auto_helper)
    source_names=helpers+[parent.TARGET]+parent.EQUATIONS;generated_names=[mapping[n] for n in helpers]+[parent.TARGET]+parent.EQUATIONS
    source_pf=previous['preflights'][parent.SOURCE_SNAPSHOT];source=old.type_rows(parent.SOURCE_TYPE_JSON,source_pf,source_names);boundary=set(p['provider_subtracted_names'])
    source_refs=old.proof_rows(parent.SOURCE_REFS_JSON,source_pf,'source',source_names,list(parent.HELPER_NAMES)+['SourceSnapshot'],boundary)
    saved=old.STAGE
    try:
        old.STAGE=stage.STAGE
        generated=old.type_rows(stage.TYPE_JSON,records[stage.SNAPSHOT],generated_names)
        modules=[stage.MODULE,parent.scales.PLATFORM_MODULE,parent.child.MODULE]+[parent.base.ap10.config(k)['platform_module'] for k in parent.base.ap10.CONFIGS]+['GeneratedSnapshot']
        generated_refs=old.proof_rows(stage.REFS_JSON,records[stage.SNAPSHOT],'generated',generated_names,modules,boundary)
    finally:old.STAGE=saved
    mapping.update({n:n for n in [parent.TARGET]+parent.EQUATIONS});roots_map=dict(mapping)
    extras=old.pair_extra({n:r for n,r in source_refs.items() if n not in roots_map},{n:r for n,r in generated_refs.items() if n not in roots_map.values()},roots_map);mapping=extras
    for n,m in roots_map.items():
        a,b=source[n],generated[m];need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1],'Original/private helper full type differs')
    actual_external_deltas={}
    historical_deltas=previous['actual_external_instance_reference_differences']
    need(set(historical_deltas)==set(old.EXTERNAL_INSTANCE_DELTAS) and all(historical_deltas[n]==old.EXTERNAL_INSTANCE_DELTAS[n]|{'fields':['valueRefs','allUsedConstants']} for n in historical_deltas),'Exact historical external-instance difference contract does not replay')
    for n,m in mapping.items():
        a,b=source_refs[n],generated_refs[m];need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1] and a['axioms']==b['axioms'],'Actual private CI type/Std3 differs')
        for f in ['typeRefs','valueRefs','allUsedConstants']:
            left={mapping.get(x,x) for x in a[f]};right=set(b[f]);source_only=sorted(left-right);generated_only=sorted(right-left)
            project=lambda x:x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x or x in source_refs or x in generated_refs
            need({x for x in left if project(x)}=={x for x in right if project(x)},'Actual private project constants differ under exact kernel-name mapping: '+n+':'+f)
            if f=='typeRefs':need(not source_only and not generated_only,'Actual private complete type references differ: '+n)
            elif source_only or generated_only:
                expected=old.EXTERNAL_INSTANCE_DELTAS.get(n)
                need(expected is not None and source_only==expected['source_only'] and generated_only==expected['generated_only'] and all(not project(x) for x in source_only+generated_only),'Private mirror has an unrecorded external instance-reference difference: '+n+':'+f)
                actual_external_deltas.setdefault(n,{'source_only':source_only,'generated_only':generated_only,'fields':[]})['fields'].append(f)
        for x in b['allUsedConstants']:
            if x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x:need(x in generated_refs or x in boundary,'Actual private mirror project dependency lacks closed provenance')
    need(set(actual_external_deltas)<=set(historical_deltas) and all(v['fields']==['valueRefs','allUsedConstants'] for v in actual_external_deltas.values()),'Actual finite mirror instance difference fields/domain differ')
    for row in pairs:need(generated_refs[row['actualName']]['owner']==row['owner'],'Actual private proof owner differs from exact resolver evidence')
    equations=equation_pairs({parent.SOURCE_SNAPSHOT:source_pf,parent.GENERATED_SNAPSHOT:records[stage.SNAPSHOT]},source,generated,source_refs,generated_refs)
    prior={}
    for key,w in previous['actual_provider_bindings'].items():
        module=w['module'];cached=stage.TASK/w['olean'];d=kernel.imported_dep(records[stage.OUTPUT],module);need(Path(d['path']).resolve()==cached.resolve() and d['sha256_before']==sha(cached)==w['olean_sha256'],'Private mirror prerequisite OLean differs');prior[key]=w
    return {'schema_version':1,'artifact_kind':'ap16-private-clearing-child-mirror-probe-v4-validation','source_commit':parent.COMMIT,'source_name':parent.TARGET,'platform_module':stage.MODULE,'public_platform_boundary_names':[parent.TARGET],'platform_boundary_certification_pending':False,'accepted_parent_Proved':True,'accepted_evidence_sha256':sha(ACCEPTED),'accepted_theorem_id':accepted['theorem_id'],'accepted_proof_id':accepted['last_verify_verdict']['body']['id'],'published_wire_unchanged':True,'private_helper_count':18,'actual_private_helper_mappings':pairs,'actual_owned_public_names':public,'actual_owned_auxiliary_data_equations':auxiliary_data_equations,'raw_owned_public_inventory_includes_compiler_data_equations':True,'public_platform_boundary_remains_original_target_only':True,'actual_automatic_CI_pairs':[[n,m] for n,m in mapping.items() if n not in roots_map],'provider_source_sha256':sha(stage.EMITTER_STAGE/stage.OUTPUT),'provider_olean':rel(olean),'provider_olean_sha256':sha(olean),'preparation_sha256':sha(stage.STAGE/'preparation.json'),'historical_source_certificate_sha256':sha(parent.STAGE/parent.CERTIFICATE),'preflights':records,'source_and_generated_types_equal':True,'source_and_generated_actual_proof_references_paired':True,'all_original_proof_suffixes_unchanged':True,'official_equation_pairs':equations,'actual_prior_provider_bindings':prior,'actual_external_instance_reference_differences':actual_external_deltas,'allowed_external_instance_difference_contract':old.EXTERNAL_INSTANCE_DELTAS,'historical_external_instance_difference_contract_sha256':stage.sha_bytes(stage.encode(historical_deltas)),'all_project_references_exact_under_actual_private_mapping':True,'Std3_only':True,'max_file_seconds':max(r['data']['seconds'] for r in records.values()),'implementation_hashes':{rel(f):sha(f) for f in [SELF,stage.SELF,stage.RUNNER,stage.LEGACY_RUNNER,stage.original.SELF,Path(old.__file__),Path(kernel.__file__),Path(context.__file__)]},'generated_json_sha256':{f:sha(stage.STAGE/f) for f in [stage.TYPE_JSON,stage.REFS_JSON,stage.MAPPING_JSON]},'reused_genuine_emitter_root':rel(stage.EMITTER_STAGE),'failed_v1_probe_record_sha256':sha(stage.EMITTER_STAGE/'interrupted-probe-record.json'),'failed_v2_probe_record_sha256':sha((stage.previous.previous.STAGE/stage.SNAPSHOT).with_suffix('.lean.preflight.json')),'failed_v3_probe_record_sha256':sha((stage.previous.STAGE/stage.SNAPSHOT).with_suffix('.lean.preflight.json')),'bounded_runner_sha256':sha(stage.RUNNER),'legacy_runner_sha256':sha(stage.LEGACY_RUNNER),'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

_validate_reused_v4_contexts = validate

def validate():
    result = _validate_reused_v4_contexts()
    ledger = read(LEDGER)
    need(ledger['input_hashes'][rel(FROZEN_V4_CONSUMER)] == sha(FROZEN_V4_CONSUMER)
         and ledger['exact_automatic_helper_name'] == AUTO_HELPER
         and result['provider_olean_sha256'] == ledger['v4_actual_emitter_olean_sha256'],
         'Derived v5 ledger does not bind the exact failed v4 consumer/helper/OLean')
    result['artifact_kind'] = 'ap16-private-clearing-child-mirror-validation-v5'
    result['derived_ledger'] = rel(LEDGER)
    result['derived_ledger_sha256'] = sha(LEDGER)
    result['frozen_v4_consumer_sha256'] = sha(FROZEN_V4_CONSUMER)
    result['actual_closed_automatic_data_helper_pair'] = {
        'name': AUTO_HELPER,
        'source_owner': ledger['source_helper_owner'],
        'generated_owner': ledger['generated_helper_owner'],
        'source_complete_CI_sha256': ledger['source_helper_CI_sha256'],
        'generated_complete_CI_sha256': ledger['generated_helper_CI_sha256'],
        'full_type_axioms_and_all_actual_refs_equal': True,
        'closed_source_and_generated_proof_values': True,
        'only_actual_auxiliary_project_ref_exception': True,
        'original_AP10_matrix_complete_Def_certificate_sha256':
            ledger['original_AP10_matrix_complete_Def_certificate_sha256'],
        'published_AP10_matrix_definition_sha256':
            ledger['published_AP10_matrix_definition_sha256']}
    result['implementation_hashes'][rel(derived.SELF)] = sha(derived.SELF)
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--bind-accepted',action='store_true');g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.bind_accepted:print(json.dumps(bind_accepted(),ensure_ascii=False,indent=2));return
    r=validate();path=DERIVED_STAGE/derived.CERTIFICATE;raw=stage.encode(r)
    if path.exists():need(path.read_bytes()==raw,'Existing private mirror certificate differs')
    elif a.certify_existing:
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(raw)
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path) if path.exists() else None,'validated':True,'Std3_only':True,'max_file_seconds':r['max_file_seconds'],'Lean_started_by_consumer':False,'API_used':False},indent=2))
if __name__=='__main__':main()
