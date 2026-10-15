"""Strict actual AP20 seventeen full Def CIs and finite observed closed-Prop caches."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_literal_analytic_interface_data_provider as prep
import certify_analytic_remainder_data_existing as common
import validate_namespace_context_providers as context
from certify_command_emission_probe import checked_expr
from certify_full_row_minor_node import refs,imported_dep

SELF=Path(__file__).resolve();STD3=common.STD3
need=prep.need

def ci_checked(r):
    need(r['kind']=='theorem' and r['closedType'] is True and r['closedValue'] is True and r['isProp'] is True
         and r['value'] is not None and r['axioms']==sorted(set(r['axioms'])) and set(r['axioms'])<=STD3,'Actual proof CI is not a closed Std3 Prop')
    need(r['typeRefs']==refs(r['type']) and r['valueRefs']==refs(r['value']),'Actual proof CI direct references differ')
    checked_expr(r['type'],set(r['levelParams']));checked_expr(r['value'],set(r['levelParams']))

def proof_ledger(filename,pf,generated):
    p=prep.STAGE/filename;doc=prep.read(p)
    from datetime import datetime
    end=datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(end-pf['data']['seconds']-2<=p.stat().st_mtime<=end+2,'Proof-CI inventory outside actual compiler interval')
    need(set(doc)=={'schemaVersion','probeMainModule','roots','allowedOwners','actualUsedProofCIs'} and doc['schemaVersion']==1
         and doc['probeMainModule']==('GeneratedSnapshot' if generated else 'SourceSnapshot')
         and doc['roots']==prep.NAMES and doc['allowedOwners']==prep.allowed_modules(generated),'Actual used proof CI envelope differs')
    rows=doc['actualUsedProofCIs'];need(len({r['name'] for r in rows})==len(rows),'Duplicate actual proof CI')
    fields={'name','owner','privateUserName','kind','levelParams','closedType','closedValue','isProp','type','value','typeRefs','valueRefs','axioms'}
    for r in rows:
        need(set(r)==fields and r['owner'] in doc['allowedOwners'],'Actual proof CI owner/fields differ');ci_checked(r)
    return {r['name']:r for r in rows}

def structural_pair(left,right,source,generated,mapping,pairs):
    """Every differing leaf must be an actual typed closed-Prop CI, never a name guess."""
    if left==right:return
    if isinstance(left,list) and isinstance(right,list) and len(left)==len(right):
        if len(left)==3 and left[0]==right[0]=='const' and left[1]!=right[1]:
            a,b=left[1],right[1]
            need(left[2]==right[2] and a in source and b in generated,'Uncertified mathematical constant difference: '+str((a,b)))
            l,r=source[a],generated[b];ci_checked(l);ci_checked(r)
            need(all(l[k]==r[k] for k in ['levelParams','type','value','typeRefs','valueRefs','axioms']), 'Observed closed-Prop CIs do not have identical complete kernel evidence: '+str((a,b)))
            need(a not in mapping or mapping[a]==b,'Inconsistent actual proof-cache map');mapping[a]=b
            pairs[(a,b)]={'source_name':a,'generated_name':b,'source_owner':l['owner'],'generated_owner':r['owner'],
                'levelParams':l['levelParams'],'full_type_sha256':prep.sha_bytes(prep.encode(l['type'])),
                'full_proof_value_sha256':prep.sha_bytes(prep.encode(l['value'])),'typeRefs':l['typeRefs'],'valueRefs':l['valueRefs'],
                'axioms':l['axioms'],'actual_kernel_isProp':True,'closedType':True,'closedValue':True}
            return
        for l,r in zip(left,right,strict=True):structural_pair(l,r,source,generated,mapping,pairs)
        return
    need(False,'Source/generated full kernel expression differs outside an actual certified Prop constant')

def rename(x,mapping):
    if isinstance(x,list):
        if len(x)==3 and x[0]=='const':return [x[0],mapping.get(x[1],x[1]),x[2]]
        return [rename(v,mapping) for v in x]
    return x

def owned_inventory(pf,generated,source_proofs,generated_proofs,mapping,pairs):
    from datetime import datetime
    path=prep.STAGE/prep.INVENTORY_JSON;d=prep.read(path);end=datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(end-pf['data']['seconds']-2<=path.stat().st_mtime<=end+2,'Raw owner inventory outside actual compiler interval')
    need(set(d)=={'schemaVersion','probeMainModule','providerModule','anchor','providerModuleIndex','inventorySelection','rawOwnedCIs'}
         and d['schemaVersion']==1 and d['probeMainModule']=='GeneratedSnapshot' and d['providerModule']==prep.PLATFORM_MODULE
         and d['anchor']==prep.NAMES[-1] and isinstance(d['providerModuleIndex'],int)
         and d['inventorySelection']=='all constants, exact imported owner index before name conversion','Actual owner-index-first inventory envelope differs')
    rows=d['rawOwnedCIs'];names=[r['name'] for r in rows]
    need(names==sorted(set(names)) and set(prep.NAMES)<=set(names),'Raw owner inventory does not contain all17 actual Def CIs')
    by={r['resolvedName']:r for r in generated};auto=[]
    fields={'name','owner','ownerModuleIndex','privateUserName','kind','levelParams','closedType','closedValue','isProp','type','value','typeRefs','valueRefs','axioms'}
    for r in rows:
        need(set(r)==fields and r['owner']==prep.PLATFORM_MODULE and r['ownerModuleIndex']==d['providerModuleIndex'],'Raw owner inventory ownership/fields differ')
        if r['name'] in by:
            primary=by[r['name']]
            need(r['privateUserName'] is None and r['kind']=='def' and r['isProp'] is False and r['closedType'] is True and r['closedValue'] is True
                 and all(r[k]==primary[k] for k in ['levelParams','type','value','axioms'])
                 and r['typeRefs']==refs(r['type']) and r['valueRefs']==refs(r['value']),'Owned primary Def differs from complete kernel snapshot')
            continue
        ci_checked(r)
        need(r['name'] in generated_proofs and all(r[k]==generated_proofs[r['name']][k] for k in generated_proofs[r['name']]),
             'Extra owned CI is not an actually used closed-Prop CI; early raw inventory preserved for exact audit')
        source_names=[a for a,b in mapping.items() if b==r['name']]
        if not source_names and r['name'] in source_proofs:
            source_names=[r['name']]
        need(len(source_names)==1,'Owned automatic CI lacks a unique actual source pairing')
        l=source_proofs[source_names[0]]
        need(all(l[k]==r[k] for k in ['levelParams','type','value','typeRefs','valueRefs','axioms']),'Owned automatic CI complete source/generated evidence differs')
        auto.append({'source_name':source_names[0],'generated_name':r['name'],'source_owner':l['owner'],'generated_owner':r['owner'],
          'full_type_sha256':prep.sha_bytes(prep.encode(r['type'])),'full_proof_value_sha256':prep.sha_bytes(prep.encode(r['value'])),
          'typeRefs':r['typeRefs'],'valueRefs':r['valueRefs'],'axioms':r['axioms'],'actual_kernel_isProp':True,'closedType':True,'closedValue':True})
    return d,auto

def validate(key='interface'):
    prep.check_only(key);c=prep.config(key);p=prep.read(prep.STAGE/'preparation.json');units=prep.authority()
    need(p['validated'] is False and p['submission_ready'] is False and p['proposal_status']=='Draft','Preparation flags differ')
    records={}
    for i,(f,mode,module) in enumerate([(prep.PROVIDER_FILE,'emit-olean',prep.PLATFORM_MODULE),(prep.SOURCE_SNAPSHOT,'modecheck','SourceSnapshot'),(prep.GENERATED_SNAPSHOT,'modecheck','GeneratedSnapshot')],1):
        record=context.record(prep.STAGE/f,prep.STAGE/f'c{i}.json',mode,module,prep.STAGE);d=record['data']
        need(d['success'] and d['exit_code']==0 and not d['timed_out'] and 0<d['seconds']<=300 and d['timeout_seconds']==300
             and d['mode']==mode and 'emit_olean' not in d and d.get('runner')==prep.rel(prep.RUNNER)
             and d.get('runner_sha256')==prep.sha(prep.RUNNER) and d.get('legacy_runner_sha256')==prep.sha(prep.base.base.PREFLIGHT)
             and d.get('cleanup_completed') is True,'Actual bounded compiler witness differs')
        records[f]=record
    emitter=records[prep.PROVIDER_FILE]['data'];expected=prep.TASK/p['expected_provider_olean']
    need(emitter['output_olean']==prep.rel(expected) and emitter['output_olean_sha256']==prep.sha(expected),'Actual emitted provider OLean differs')
    for f in [prep.SOURCE_SNAPSHOT,prep.GENERATED_SNAPSHOT]:need(records[f]['data']['output_olean'] is None and records[f]['data']['output_olean_sha256'] is None,'Metadata probe emitted OLean')
    dep=imported_dep(records[prep.GENERATED_SNAPSHOT],prep.PLATFORM_MODULE)
    need(Path(dep['path']).resolve()==expected.resolve() and dep['sha256_before']==prep.sha(expected),'Generated actual probe imported a different OLean')
    for module,certpath,okey,hkey in [(prep.base.PLATFORM_MODULE,prep.REMAINDER_CERT,'original_emitted_provider_olean','original_emitted_provider_olean_sha256'),(prep.ROW_MODULE,prep.ROW_CERT,'provider_olean','provider_olean_sha256')]:
        cert=prep.read(certpath);dep=imported_dep(records[prep.PROVIDER_FILE],module)
        need(Path(dep['path']).resolve()==context.file(cert[okey]).resolve() and dep['sha256_before']==cert[hkey],'Emitter imported a different actual Published prerequisite')
    source=common.rows(prep.STAGE/prep.SOURCE_JSON,records[prep.SOURCE_SNAPSHOT],17)
    generated=common.rows(prep.STAGE/prep.GENERATED_JSON,records[prep.GENERATED_SNAPSHOT],17)
    source_proofs=proof_ledger(prep.SOURCE_CACHES,records[prep.SOURCE_SNAPSHOT],False)
    generated_proofs=proof_ledger(prep.GENERATED_CACHES,records[prep.GENERATED_SNAPSHOT],True)
    inherited,_,_=prep.inherited_binding();mapping={};pairs={};differences=[];axioms={};owners={'source':{},'generated':{}}
    for unit,left,right in zip(units,source,generated,strict=True):
        name=unit['name'];o=unit['owner']
        for side,row,module in [('source',left,unit['source_module']),('generated',right,prep.PLATFORM_MODULE)]:
            need(set(row)==common.ROW_FIELDS and row['schemaVersion']==2 and row['kernelMetadataSchema']=='lean-4.33.1-ConstantInfo-complete-v1'
                 and row['sourceName']==row['resolvedName']==name and row['sourceModule']==module and row['graphKind']==row['envKind']=='def'
                 and row['declGraphSha256']==o['decl_graph_sha256'] and row['declGraphRowSha256']==o['decl_graph_row_sha256']
                 and row['ownerKind']==o['owner_kind'] and row['ownerId']==o['owner_id'] and row['commandUnit']==o['command_unit']
                 and row['familyRoot']==name and row['closedType'] is True and row['closedValue'] is True and row['value'] is not None
                 and row['kindMetadata']=={'valueExported':True,'safety':'Lean.DefinitionSafety.safe'}
                 and row['familyReferences']==[] and row['transitiveNames']==[],'Exact full Def CI/type/value/owner differs: '+side+':'+name)
            levels=row['levelParams'];need(isinstance(levels,list) and len(set(levels))==len(levels) and all(isinstance(x,str) for x in levels),'Universe domain invalid')
            checked_expr(row['type'],set(levels));checked_expr(row['value'],set(levels))
            need(row['axioms']==sorted(set(row['axioms'])) and set(row['axioms'])<=STD3,'Nonstandard Def axioms')
            axioms[side+':'+name]=row['axioms'];owners[side][name]=module
        need(left['levelParams']==right['levelParams'] and left['type']==right['type'] and left['axioms']==right['axioms'],'Source/generated complete Def type/levels/Std3 differs: '+name)
        if left['value']!=right['value']:
            structural_pair(left['value'],right['value'],source_proofs,generated_proofs,mapping,pairs)
            need(rename(left['value'],mapping)==right['value'],'Complete Def value did not match after exact observed proof-CI map')
            differences.append({'name':name,'source_value_sha256':prep.sha_bytes(prep.encode(left['value'])),
              'generated_value_sha256':prep.sha_bytes(prep.encode(right['value'])),'actual_source_to_generated_Prop_CI_pairs':
              sorted([a,b] for a,b in mapping.items() if a in refs(left['value']))})
    inventory,auto=owned_inventory(records[prep.GENERATED_SNAPSHOT],generated,source_proofs,generated_proofs,mapping,pairs)
    output_files=[prep.SOURCE_JSON,prep.GENERATED_JSON,prep.INVENTORY_JSON,prep.SOURCE_CACHES,prep.GENERATED_CACHES]
    return {'schema_version':1,'artifact_kind':'ap20-literal-interface-seventeen-Def-actual-provider-validation','source_commit':prep.COMMIT,
      'source_modules':prep.SOURCE_MODULES,'source_module_by_name':{u['name']:u['source_module'] for u in units},'platform_module':prep.PLATFORM_MODULE,'provided_names':prep.NAMES,
      'provider_source_sha256':prep.sha(prep.STAGE/prep.PROVIDER_FILE),'provider_olean':prep.rel(expected),'provider_olean_sha256':prep.sha(expected),
      'preparation_sha256':prep.sha(prep.STAGE/'preparation.json'),'compiler_manifest_sha256':{f'c{i}.json':prep.sha(prep.STAGE/f'c{i}.json') for i in range(1,4)},
      'preflights':records,'source_and_generated_types_equal':True,'definition_values_equal_and_exported':not differences,'raw_definition_values_equal':not differences,
      'raw_equal_definition_count':17-len(differences),'definition_values_equal_after_exact_observed_closed_Prop_substitution':True,
      'actual_definition_value_proof_cache_differences':differences,'actual_source_generated_closed_Prop_CI_pairs':list(pairs.values()),
      'actual_source_generated_owned_automatic_CI_pairs':auto,'actual_owned_CI_names':[r['name'] for r in inventory['rawOwnedCIs']],
      'actual_owned_public_names':[r['name'] for r in inventory['rawOwnedCIs'] if r['privateUserName'] is None],
      'raw_owned_CI_inventory_exact':True,'complete_environment_owner_index_first':True,'contains_theorems':False,'own_structures_constructors_recursors':[],
      'inherited_provider_binding':inherited,'actual_owners':owners,'axioms':axioms,'Std3_only':True,
      'output_json_sha256':{prep.rel(prep.STAGE/x):prep.sha(prep.STAGE/x) for x in output_files},
      'implementation_hashes':{prep.rel(x):prep.sha(x) for x in [SELF,prep.SELF,prep.CORE,prep.INVENTORY,prep.RUNNER,prep.base.base.PREFLIGHT,prep.base.base.CONTEXT,Path(common.__file__),Path(checked_expr.__code__.co_filename)]},
      'max_file_seconds':max(r['data']['seconds'] for r in records.values()),'validated':True,'Lean_started_by_consumer':False,'API_used':False,'submission_ready':False,'proposal_status':'Draft'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--provider',choices=prep.CONFIGS,required=True);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();result=validate(a.provider);raw=prep.encode(result)
    if prep.CERTIFICATE.exists():need(prep.CERTIFICATE.read_bytes()==raw,'Refusing changed existing certificate')
    elif a.certify_existing:prep.CERTIFICATE.write_bytes(raw)
    else:need(False,'Check-only requires actual existing certificate')
    print(json.dumps({'certificate':prep.rel(prep.CERTIFICATE),'certificate_sha256':prep.sha(prep.CERTIFICATE),'validated':True,'Std3_only':True,
      'raw_equal_definition_count':result['raw_equal_definition_count'],'owned_CI_count':len(result['actual_owned_CI_names']),'max_file_seconds':result['max_file_seconds']},indent=2))
if __name__=='__main__':main()
