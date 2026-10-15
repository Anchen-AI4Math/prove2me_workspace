"""Strict bounded type/ref certification of two source-faithful Open analytic sketches."""
from __future__ import annotations
import argparse,json
from datetime import datetime
from pathlib import Path
import finalize_analytic_translated_two_layer_reduction as stage
import validate_namespace_context_providers as context
from certify_full_row_minor_node import normalized_type,imported_dep
from validate_formal_log_node import checked_expr

SELF=Path(__file__).resolve();STD3={'propext','Classical.choice','Quot.sound'}
need,read,sha,encode,rel=stage.need,stage.read,stage.sha,stage.encode,stage.rel
ROW_KEYS={'name','levelParams','type','value','closedType','closedValue','isProp','actualOwner','axioms','typeRefs','valueRefs','Open_sketch_type_check'}

def written(file,pf):
    p=stage.STAGE/file;d=pf['data'];end=datetime.fromisoformat(d['at_utc']).timestamp()
    need(end-d['seconds']-2<=p.stat().st_mtime<=end+2,'Metadata outside actual compiler interval: '+file)
    return read(p)

def row_checked(r,name,owner,opened):
    need(set(r)==ROW_KEYS and r['name']==name and r['actualOwner']==owner and r['value'] is None
         and r['closedType'] is True and r['closedValue'] is True and r['isProp'] is True and r['Open_sketch_type_check'] is opened,
         'Actual full theorem type/closedness/owner differs: '+name)
    checked_expr(r['type'],set(r['levelParams']))
    for k in ['axioms','typeRefs','valueRefs']:need(r[k]==sorted(set(r[k])),'Actual CI reference/axiom domain differs')
    need(set(r['axioms'])<=(STD3|({'sorryAx'} if opened else set())) and ('sorryAx' in r['axioms']) is opened,'Unexpected original/sketch axiom domain')
    return r

def replace_constants(x,mapping):
    if isinstance(x,list):
        if len(x)==3 and x[0]=='const':return ['const',mapping.get(x[1],x[1]),x[2]]
        return [replace_constants(v,mapping) for v in x]
    if isinstance(x,dict):
        result={k:replace_constants(v,mapping) for k,v in x.items()}
        if result.get('tag')=='const':result['name']=mapping.get(result['name'],result['name'])
        return result
    return x

def project(refs):return sorted(n for n in refs if n.startswith('OAI.') or '.OAI.' in n)

def source_auxiliary(pf):
    doc=written(stage.SOURCE_AUX_JSON,pf)
    need(set(doc)=={'schemaVersion','probeMainModule','roots','actualAuxiliaryCIs'} and doc['schemaVersion']==1
         and doc['probeMainModule']=='SourceTypeAndRefsSnapshot' and doc['roots']==stage.INTERFACE_NAMES,'Actual source auxiliary envelope differs')
    rows=doc['actualAuxiliaryCIs'];need(len({r['name'] for r in rows})==len(rows),'Duplicate actual source auxiliary CI')
    fields={'name','actualOwner','privateUserName','kind','levelParams','type','value','closedType','closedValue','isProp','typeRefs','valueRefs','axioms'}
    for r in rows:
        need(set(r)==fields and r['kind']=='theorem' and r['value'] is None and r['closedType'] is True and r['closedValue'] is True
             and r['isProp'] is True and r['axioms']==sorted(set(r['axioms'])) and set(r['axioms'])<=STD3,'Source auxiliary not an actual closed Std3 theorem')
        checked_expr(r['type'],set(r['levelParams']))
    return {r['name']:r for r in rows}

def validate():
    stage.check_only();p=read(stage.STAGE/'preparation.json');u=stage.units()
    need(p['new_analytic_name_count']==11 and p['new_analytic_names']==stage.NEW_NAMES and p['parent_wire_unchanged']
         and p['parent_existing_wire_sha256']==sha(stage.STAGE/'parent-existing-wire.lean') and not p['closed_proof']
         and not p['generated_Std3_only'] and p['local_placeholder_sorryAx_expected'],'Final sketch semantics/domain differ')
    preflights={};oleans={}
    for f,r in p['files'].items():
        module='.'.join(Path(f).with_suffix('').parts);pf=context.record(stage.STAGE/f,stage.STAGE/r['manifest'],r['mode'],module,stage.STAGE);d=pf['data']
        need(d['success'] and d['exit_code']==0 and not d['timed_out'] and 0<d['seconds']<=300 and d['timeout_seconds']==300
             and d['mode']==r['mode'] and 'emit_olean' not in d and d.get('runner_sha256')==sha(stage.RUNNER)
             and d.get('cleanup_completed') is True,'Actual bounded context failed/differed: '+f)
        preflights[f]=pf
        if r['mode']=='emit-olean':
            path=stage.V/'staged-build/lib/lean'/Path(f).with_suffix('.olean')
            need(context.file(d['output_olean'])==path.resolve() and d['output_olean_sha256']==sha(path),'Actual emitted OLean differs')
            oleans[module]={'path':rel(path),'sha256':sha(path)}
        else:need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Metadata emitted OLean')
    source_pf=preflights[stage.SOURCE_SNAPSHOT];source=written(stage.SOURCE_JSON,source_pf)
    need(isinstance(source,list) and len(source)==14,'Actual source14 CI domain differs')
    left={n:row_checked(r,n,u[n]['source_module'],False) for n,r in zip(stage.INTERFACE_NAMES,source,strict=True)}
    aux=source_auxiliary(source_pf);boundary=p['boundary'];base_mapping={r['source_name']:r['generated_name'] for r in boundary['exact_observed_data_closed_Prop_pairs']}
    pair=boundary['CoreData_certified_closed_Prop_pair'];base_mapping[pair['source_name']]=pair['generated_name']
    reports={};inventories={};aux_pairs=[];unused=[]
    for parent in [stage.NORM,stage.ACTUAL]:
        mapping=dict(base_mapping)
        f=stage.GENERATED_SNAPSHOTS[parent];pf=preflights[f];doc=written(stage.GENERATED_JSON[parent],pf)
        names=stage.INTERFACE_NAMES+['solution'];need(isinstance(doc,list) and len(doc)==15,'Actual generated15 CI domain differs')
        right={n:row_checked(r,n,stage.theorem_module(n) if n!='solution' else stage.SOLUTION_MODULES[parent],True) for n,r in zip(names,doc,strict=True)}
        for n in stage.INTERFACE_NAMES:need(normalized_type(left[n])==normalized_type(right[n]),'Original/generated complete interface type differs: '+n)
        need(normalized_type(left[parent])==normalized_type(right['solution']),'Original parent/global solution fulltype differs')
        for module in [stage.theorem_module(n) for n in stage.INTERFACE_NAMES]+[stage.SOLUTION_MODULES[parent]]:
            dep=imported_dep(pf,module);expected=oleans.get(module,boundary['existing_actual_parent_olean'] if module==stage.theorem_module(stage.ACTUAL) else None)
            need(expected is not None and dep['sha256_before']==expected['sha256'] and context.file(expected['path'])==Path(dep['path']).resolve(),'Generated snapshot imported a different actual theorem/solution OLean')
        inv=written(stage.OWNED_JSON[parent],pf)
        expected_owners=[stage.theorem_module(n) for n in stage.INTERFACE_NAMES]+[stage.SOLUTION_MODULES[parent]]
        need(set(inv)=={'schemaVersion','probeMainModule','ownerModules','inventorySelection','rawOwnedCIs'} and inv['schemaVersion']==1
             and inv['probeMainModule']==Path(f).stem and inv['ownerModules']==expected_owners
             and inv['inventorySelection']=='all constants, imported ModuleIdx first','Actual complete-owner inventory envelope differs')
        raw=inv['rawOwnedCIs'];raw_names=[r['name'] for r in raw]
        need(raw_names==sorted(set(raw_names)) and set(names)<=set(raw_names),'Raw inventory is not the exact complete domain')
        raw_by={r['name']:r for r in raw};all_refs=set(n for r in raw for n in r['typeRefs']+r['valueRefs'])
        for r in raw:
            need(r['actualOwner'] in expected_owners and r['kind']=='theorem' and r['closedType'] is True and r['closedValue'] is True and r['isProp'] is True
                 and r['value'] is None and set(r['axioms'])<=STD3|{'sorryAx'},'Unexpected raw owned CI kind/closure/axioms')
            checked_expr(r['type'],set(r['levelParams']))
            if r['name'] in right:
                need(r['privateUserName'] is None and all(r[k]==right[r['name']][k] for k in ['levelParams','type','typeRefs','valueRefs','axioms','actualOwner']),'Raw owned primary differs')
                continue
            need('sorryAx' not in r['axioms'],'Auxiliary CI is an uncertified Open interface')
            matches=[]
            needed_source_aux=set(left[parent]['typeRefs']+left[parent]['valueRefs'])
            for name,s in aux.items():
                if name not in needed_source_aux:continue
                normalized=dict(s,type=replace_constants(s['type'],mapping))
                if normalized_type(normalized)==normalized_type(r) and sorted(mapping.get(n,n) for n in s['typeRefs'])==r['typeRefs'] and s['axioms']==r['axioms']:matches.append(name)
            if len(matches)==1:
                source_name=matches[0];mapping[source_name]=r['name']
                aux_pairs.append({'parent':parent,'source_name':source_name,'generated_name':r['name'],'source_owner':aux[source_name]['actualOwner'],
                  'generated_owner':r['actualOwner'],'full_type_equal':True,'actual_closed_Prop':True,'axioms':r['axioms'],
                  'source_typeRefs':aux[source_name]['typeRefs'],'generated_typeRefs':r['typeRefs'],'source_valueRefs':aux[source_name]['valueRefs'],'generated_valueRefs':r['valueRefs']})
            else:
                need(r['name'] not in all_refs and not project(r['typeRefs']+r['valueRefs']),'Unpaired auxiliary is not an unused external-only closed Prop cache; actual inventory preserved: '+r['name'])
                unused.append({'parent':parent,'name':r['name'],'actualOwner':r['actualOwner'],'type':r['type'],'levelParams':r['levelParams'],
                  'typeRefs':r['typeRefs'],'valueRefs':r['valueRefs'],'axioms':r['axioms'],'actual_closed_Prop':True,
                  'unused_by_all_raw_owned_CIs':True,'paired_source':False,'role':'unused internal Std3 Prop cache, no platform interface'})
        sp=project(left[parent]['valueRefs']);gp=project(right['solution']['valueRefs'])
        need(sorted(set(mapping.get(n,n) for n in sp))==gp,'Parent project proof references differ beyond exact typed actual cache map')
        required=stage.CHILDREN[parent]+[stage.route.TRANSLATED if parent==stage.NORM else stage.route.LOGSUM]
        need(all(n in gp for n in required),'Global sketch did not actually use every immediate public child')
        solution_pf=preflights[stage.solution_file(parent)]
        for n in required:
            dep=imported_dep(solution_pf,stage.theorem_module(n));need(dep['sha256_before']==oleans[stage.theorem_module(n)]['sha256'],'Solution imported a different immediate child OLean')
        reports[parent]={'source_project_valueRefs':sp,'generated_solution_project_valueRefs':gp,'project_refs_equal_after_actual_typed_cache_map':True,
          'source_Std3_only':True,'generated_axioms':right['solution']['axioms'],'generated_Std3_only':False,'local_sorryAx_expected':True,
          'expected_public_children':required,'original_proof_suffix_sha256':p['original_parent_proof_suffix_sha256'][parent],
          'source_external_valueRefs':sorted(set(left[parent]['valueRefs'])-set(sp)),'generated_external_valueRefs':sorted(set(right['solution']['valueRefs'])-set(gp)),
          'source_generated_complete_type_equal':True,'closed_proof':False}
        inventories[parent]=raw_names
    json_files=[stage.SOURCE_JSON,stage.SOURCE_AUX_JSON]+list(stage.GENERATED_JSON.values())+list(stage.OWNED_JSON.values())
    return {'schema_version':1,'artifact_kind':'ap20-analytic-translated-two-layer-actual-Open-sketch-validation','validated':True,
      'Open_sketch_only':True,'closed_proof':False,'source_Std3_only':True,'generated_Std3_only':False,'local_placeholder_sorryAx_expected':True,
      'existing_actual_parent_id':stage.ACTUAL_ID,'existing_actual_parent_wire_sha256':p['parent_existing_wire_sha256'],'new_analytic_names':stage.NEW_NAMES,
      'new_analytic_name_count':11,'server_Proved_children':p['server_Proved_children'],'local_accepted_leaf_role':p['local_accepted_leaf_role'],
      'expected_graph_edges':{parent:r['expected_public_children'] for parent,r in reports.items()},'parent_reports':reports,
      'actual_typed_auxiliary_Prop_pairs':aux_pairs,'actual_unused_external_only_Prop_CIs':unused,'actual_owned_CI_names':inventories,
      'all_source_generated_full_kernel_interface_types_equal':True,'boundary':boundary,'preparation_sha256':sha(stage.STAGE/'preparation.json'),
      'preflights':preflights,'emitted_oleans':oleans,'output_json_sha256':{rel(stage.STAGE/n):sha(stage.STAGE/n) for n in json_files},
      'implementation_hashes':{rel(x):sha(x) for x in [SELF,stage.SELF,stage.SOURCE_CORE,stage.RUNNER,Path(stage.data.__file__),Path(stage.data_consumer.__file__),Path(stage.source_root.__file__)]},
      'max_file_seconds':max(r['data']['seconds'] for r in preflights.values()),'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();result=validate();raw=encode(result)
    if stage.CERTIFICATE.exists():need(stage.CERTIFICATE.read_bytes()==raw,'Refusing changed sketch certificate')
    elif a.certify_existing:stage.CERTIFICATE.write_bytes(raw)
    else:need(False,'Check-only requires actual existing sketch certificate')
    print(json.dumps({'certificate':rel(stage.CERTIFICATE),'certificate_sha256':sha(stage.CERTIFICATE),'validated':True,'closed_proof':False,
      'Open_sketch_only':True,'max_file_seconds':result['max_file_seconds']},indent=2))
if __name__=='__main__':main()
