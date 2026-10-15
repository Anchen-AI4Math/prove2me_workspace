"""Strict read-only consumer of four actual AP21 contexts, including one reused emitter."""
from __future__ import annotations
import argparse,json
from datetime import datetime
from pathlib import Path
import stage_index_weight_nonneg_node as stage
import certify_full_row_minor_node as kernel
from validate_formal_log_node import checked_expr
SELF=Path(__file__).resolve();STD3={'propext','Classical.choice','Quot.sound'}
FIELDS={'name','actualOwner','privateUserName','kind','levelParams','type','value','closedType','closedValue','isProp','typeRefs','valueRefs','allUsedConstants','axioms'}

def project(names):return sorted(n for n in names if n.startswith('OAI.') or '.OAI.' in n)
def row_checked(r,theorem=True):
    stage.need(set(r)==FIELDS and r['closedType'] and r['closedValue'] and set(r['axioms'])<=STD3,'Actual CI field/closedness/Std3 domain differs')
    checked_expr(r['type'],set(r['levelParams']))
    if r['value'] is not None:checked_expr(r['value'],set(r['levelParams']))
    if theorem:stage.need(r['kind']=='theorem' and r['isProp'] and r['value'] is None,'Proof row is not an actual closed Prop theorem with value null')
    for f in ['axioms','typeRefs','valueRefs','allUsedConstants']:stage.need(r[f]==sorted(set(r[f])),'Actual reference domain not exact sorted set')
    stage.need(r['allUsedConstants']==sorted(set(r['typeRefs']+r['valueRefs'])),'Actual allUsedConstants union differs')
    return r

def normalized(r,mapping):
    n,t=kernel.normalized_type(r);return n,kernel.rename_expr(t,mapping)

def pair_equal(a,b,mapping):
    return (normalized(a,mapping)==kernel.normalized_type(b) and a['axioms']==b['axioms']
      and all(sorted(set(mapping.get(n,n) for n in a[f]))==b[f] for f in ['typeRefs','valueRefs','allUsedConstants']))

def written(filename,pf):
    p=stage.STAGE/filename;d=pf['data'];end=datetime.fromisoformat(d['at_utc']).timestamp()
    stage.need(end-d['seconds']-2<=p.stat().st_mtime<=end+2,'Snapshot output outside genuine compiler interval')
    return stage.read(p)

def validate():
    stage.check_only();prep=stage.read(stage.STAGE/'preparation.json')
    stage.need(prep['source_commit']==stage.COMMIT and prep['original_AST_count']==3 and prep['original_source_lines']==12
      and prep['private_visibility_prefix_only'] and prep['target_binding_only_solution_rename'] and not prep['finite_port_adaptations']
      and prep['theorem_id']==stage.THEOREM_ID and prep['public_wire_sha256']==stage.sha(stage.STAGE/stage.TARGET_OUTPUT)
      and prep['total_actual_context_count']==4 and prep['new_bounded_context_count']==3 and prep['reused_actual_context_count']==1
      and prep['finite_metadata_maxRecDepth']==100000,'Frozen AST/public target/bounded context contract differs')
    records={};emitted={}
    for i,(f,mode) in enumerate(zip(stage.FILES,stage.MODES,strict=True),1):
        if i==2:
            r=prep['historical_comparator_context'];pf=stage.context.record(stage.TASK/r['source'],stage.TASK/r['manifest'],mode,stage.MODULE,stage.TASK/r['root'])
            stage.need(pf==r['preflight'] and (stage.TASK/r['source']).read_bytes()==(stage.STAGE/f).read_bytes(),'Reused actual comparator witness differs')
        else:pf=stage.context.record(stage.STAGE/f,stage.STAGE/f'c{i}.json',mode,'.'.join(Path(f).with_suffix('').parts),stage.STAGE)
        d=pf['data'];stage.need(d['success'] and d['exit_code']==0 and not d['timed_out'] and 0<d['seconds']<=300 and d['timeout_seconds']==300 and d['mode']==mode and 'emit_olean' not in d and d.get('cleanup_completed') is True,'Actual bounded preflight did not PASS')
        records[f]=pf
        if mode=='emit-olean':
            p=stage.context.file(d['output_olean']);stage.need(stage.sha(p)==d['output_olean_sha256'],'Actual emitted OLean changed')
            emitted['.'.join(Path(f).with_suffix('').parts)]={'path':stage.rel(p),'sha256':stage.sha(p)}
        else:stage.need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Metadata probe unexpectedly emitted OLean')
    src=written(stage.SOURCE_JSON,records[stage.SOURCE_SNAPSHOT]);gen=written(stage.GENERATED_JSON,records[stage.GENERATED_SNAPSHOT])
    stage.need(set(src)=={'schemaVersion','side','probeMainModule','rootNames','boundaryNames','rows'} and src['schemaVersion']==1 and src['side']=='source' and src['probeMainModule']=='SourceTypeAndRefsSnapshot' and src['rootNames']==stage.NAMES and src['boundaryNames']==prep['source_and_generated_data_boundary_names'],'Source actual proof closure envelope differs')
    stage.need(set(gen)=={'schemaVersion','side','probeMainModule','rootNames','boundaryNames','sourceHelperNames','rows','comparatorCI'} and gen['schemaVersion']==1 and gen['side']=='generated' and gen['probeMainModule']=='GeneratedSnapshot' and gen['sourceHelperNames']==stage.HELPERS and gen['rootNames'][-1]=='solution' and gen['boundaryNames']==src['boundaryNames'],'Generated actual proof closure envelope differs')
    source={r['name']:row_checked(r) for r in src['rows']};generated={r['name']:row_checked(r) for r in gen['rows']}
    stage.need(len(source)==len(src['rows']) and len(generated)==len(gen['rows']) and set(stage.NAMES)<=set(source),'Duplicate/missing actual proof CI')
    inventories={}
    for side,filename,anchors,pf in [('source',stage.SOURCE_INVENTORY,stage.NAMES,records[stage.SOURCE_SNAPSHOT]),('generated',stage.GENERATED_INVENTORY,['solution'],records[stage.GENERATED_SNAPSHOT])]:
        inv=written(filename,pf)
        stage.need(set(inv)=={'schemaVersion','probeMainModule','inventorySelection','anchorNames','rawOwnedNames','rawOwnedCIs'} and inv['schemaVersion']==1 and inv['anchorNames']==anchors and inv['inventorySelection']=='all constants, imported ModuleIdx first','Complete raw actual owned inventory envelope differs')
        names=inv['rawOwnedNames'];stage.need(names==sorted(set(names)) and names==[r['name'] for r in inv['rawOwnedCIs']],'Complete raw actual CI domain differs')
        inventories[side]={r['name']:row_checked(r,r['kind']=='theorem') for r in inv['rawOwnedCIs']}
    raw=inventories['generated'];private=gen['rootNames'][:-1];mapping=dict(zip(stage.HELPERS,private,strict=True));mapping[stage.TARGET]='solution'
    for n,a in mapping.items():
        r=generated[a];stage.need(a in raw and raw[a]==r and r['actualOwner']==stage.SOLUTION_MODULE and r['privateUserName']==(n if n in stage.HELPERS else None),'Actual private helper/solution owner mapping differs')
    source_modules={u['name']:u['source_module'] for u in prep['source_units']}
    for n in stage.NAMES:stage.need(source[n]['actualOwner']==source_modules[n] and source[n]['privateUserName'] is None and inventories['source'][n]==source[n],'Actual original source CI ownership differs')
    extras=[];pending=set(source)-set(mapping);available=set(generated)-set(mapping.values())
    while pending:
        progressed=False
        for n in sorted(pending):
            candidates=[g for g in sorted(available) if pair_equal(source[n],generated[g],mapping)]
            if n in candidates:candidates=[n]
            if len(candidates)!=1:continue
            g=candidates[0];mapping[n]=g;pending.remove(n);available.remove(g);progressed=True
            extras.append({'sourceName':n,'generatedName':g,'sourceOwner':source[n]['actualOwner'],'generatedOwner':generated[g]['actualOwner'],'source_CI':source[n],'generated_CI':generated[g],'full_type_direct_refs_Std3_equal':True,'actual_closed_Prop':True})
        stage.need(progressed,'Unpaired actual source/generated proof CI; complete snapshots retained: '+repr(sorted(pending)))
    stage.need(not available,'Generated closed proof uses an unpaired imported/automatic theorem: '+repr(sorted(available)))
    pairs=[]
    for n,g in mapping.items():
        stage.need(pair_equal(source[n],generated[g],mapping),'Source/generated full type/direct refs/Std3 differ: '+n)
        pairs.append({'sourceName':n,'generatedName':g,'full_type_equal':True,'typeRefs_equal_after_actual_mapping':True,'valueRefs_equal_after_actual_mapping':True,'Std3_equal':True})
    # All project constants must be actual published data or actual paired proof CIs.
    coverage=stage.read(stage.STAGE/'actual-Published32-coverage.json');allowed=set(coverage['provided_source_graph_names'])|set(mapping.values())
    for r in generated.values():stage.need(set(project(r['allUsedConstants']))<=allowed,'Proof references an uncertified project CI')
    unused=[];additional=[]
    refs={n for r in raw.values() for n in r['allUsedConstants']}
    src_owned=inventories['source']
    for n,r in raw.items():
        if n in generated:continue
        stage.need(r['kind']=='theorem' and r['isProp'],'Unknown owned non-theorem CI; actual inventory preserved')
        candidates=[s for s,x in src_owned.items() if x['kind']=='theorem' and pair_equal(x,r,mapping)]
        if n in candidates:candidates=[n]
        if len(candidates)==1:
            s=candidates[0];additional.append({'sourceName':s,'generatedName':n,'source_CI':src_owned[s],'generated_CI':r,'full_type_direct_refs_Std3_equal':True,'platform_interface':False})
        else:
            stage.need(n not in refs and not project(r['allUsedConstants']),'Unpaired owned CI is not an unused external-only closed Prop cache')
            unused.append({'CI':r,'unused_by_all_raw_owned_CIs':True,'paired_source':False,'platform_interface':False})
    comparator=dict(gen['comparatorCI']);stage.need(comparator['name']==stage.TARGET and comparator['actualOwner']==stage.MODULE and comparator['value'] is None and comparator['closedType'] and comparator['isProp'] and set(comparator['axioms'])<=STD3|{'sorryAx'} and 'sorryAx' in comparator['axioms'],'Comparator is not the exact imported historical Open placeholder')
    stage.need(kernel.normalized_type(comparator)==kernel.normalized_type(generated['solution']),'Public target/completed solution full type differs')
    gp=records[stage.GENERATED_SNAPSHOT]
    data_dep=kernel.imported_dep(records[stage.SOLUTION_OUTPUT],stage.DATA_MODULE)
    stage.need(data_dep['sha256_before']==data_dep['sha256_after']==prep['data_provider_olean_sha256'] and Path(data_dep['path']).resolve()==(stage.TASK/prep['data_provider_olean']).resolve(),'Compiled solution did not import the actual certified Published InterfaceData OLean')
    for module in [stage.MODULE,stage.SOLUTION_MODULE]:
        dep=kernel.imported_dep(gp,module);stage.need(dep['sha256_before']==emitted[module]['sha256'] and Path(dep['path']).resolve()==(stage.TASK/emitted[module]['path']).resolve(),'Metadata imported the wrong actual target/solution OLean')
    outputs=[stage.SOURCE_JSON,stage.GENERATED_JSON,stage.SOURCE_INVENTORY,stage.GENERATED_INVENTORY]
    return {'schema_version':1,'artifact_kind':'ap21-indexWeight-nonneg-actual-closed-node-validation','validated':True,'Std3_only':True,'source_commit':stage.COMMIT,'theorem_id':stage.THEOREM_ID,'target':stage.TARGET,'original_AST_count':3,'original_source_lines':12,'source_and_generated_full_types_equal':True,'actual_proof_references_paired':True,'actual_proof_references_bitwise_equal_after_private_CI_mapping':True,'actual_private_helper_mappings':[{'sourceName':n,'actualName':mapping[n],'actualOwner':generated[mapping[n]]['actualOwner']} for n in stage.HELPERS],
      'actual_CI_pairs':pairs,'actual_automatic_CI_pairs':extras,'additional_source_paired_owned_CIs':additional,'unused_internal_Prop_CIs':unused,'complete_raw_owned_inventory_exact':True,'raw_owned_CI_names':sorted(raw),'public_platform_solution_boundary':['solution'],'closed_proof':True,'local_target_comparator_sorry_is_not_a_proof':True,'contains_unProved_theorem_boundary':False,'actual_Published_definition_count':32,
      'preflights':records,'emitted_oleans':emitted,'actual_solution_data_import_binding':data_dep,'source_and_generated_same_published_data_boundaries':src['boundaryNames'],'published_data_values_certified_and_not_retraversed':True,'total_actual_context_count':4,'new_actual_context_count':3,'reused_actual_context_count':1,'data_certificate_sha256':prep['data_certificate_sha256'],'data_provider_olean':prep['data_provider_olean'],'data_provider_olean_sha256':prep['data_provider_olean_sha256'],'public_wire_sha256':prep['public_wire_sha256'],'preparation_sha256':stage.sha(stage.STAGE/'preparation.json'),'output_json_sha256':{stage.rel(stage.STAGE/f):stage.sha(stage.STAGE/f) for f in outputs},'implementation_hashes':{stage.rel(p):stage.sha(p) for p in [SELF,stage.SELF,stage.CORE,stage.RUNNER,stage.LEGACY_RUNNER]},'max_file_seconds':max(r['data']['seconds'] for r in records.values()),'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();report=validate();raw=stage.encode(report)
    if stage.CERTIFICATE.exists():stage.need(stage.CERTIFICATE.read_bytes()==raw,'Refusing changed actual certificate')
    elif a.certify_existing:stage.CERTIFICATE.write_bytes(raw)
    else:stage.need(False,'Check-only requires genuine certificate')
    print(json.dumps({'certificate':stage.rel(stage.CERTIFICATE),'certificate_sha256':stage.sha(stage.CERTIFICATE),'validated':True,'Std3_only':True,'max_file_seconds':report['max_file_seconds'],'new_contexts':3,'reused_contexts':1},indent=2))
if __name__=='__main__':main()
