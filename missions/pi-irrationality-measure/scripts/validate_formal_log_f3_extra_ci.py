"""Readonly certification of actual f3 equation/helper CI companions."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import stage_formal_log_f3_extra_ci as gen
import stage_formal_log_f3_extra_ci_compatible as compatible
import validate_formal_log_truncation_provider as formalci
import validate_formal_log_successor_node as nodes
import validate_namespace_context_providers as context
import formal_log_node_refs as refs

TASK,ROOT,V,STAGE=gen.TASK,gen.ROOT,gen.V,gen.STAGE
SELF=Path(__file__).resolve()
PRODUCER_SHA='2ea870cb464716e6457027d44524bbdc616e28589a7ab2bc811df4032e7be805'
COMPATIBLE_SHA='deb480e256234f105a0c79895bac5ced608f29610f5536c3cfc57278f4a9c19f'
CERT_NAME='extra-ci-validation.json'
read,sha,rel,fail=context.read,context.sha,context.rel,context.fail

def source_equal(a,b,kind='theorem'):
    nodes.base.same_type({'name':a['actualName'],'levelParams':a['levelParams'],'type':a['type']},
                         {'name':b['actualName'],'levelParams':b['levelParams'],'type':b['type']})
    fail(a['actualName']!=b['actualName'] or set(a['axioms'])!=set(b['axioms']), 'Paired CI identity/Std3 differs')
    if kind=='def':
        fail(len(a['levelParams'])!=len(b['levelParams']) or
            nodes.base.normalized(a['value'],{p:i for i,p in enumerate(a['levelParams'])},{}) !=
            nodes.base.normalized(b['value'],{p:i for i,p in enumerate(b['levelParams'])},{}),'Paired complete primary values differ')

def primary_matches(ci,row,module,main):
    formalci.checked_api_ci(ci,'def',row['resolvedName'],module,main)
    fail(row['envKind']!='def' or row['closedType'] is not True or row['closedValue'] is not True
         or row['kindMetadata']!={'safety':'Lean.DefinitionSafety.safe','valueExported':True},'Primary snapshot is not safe complete Def CI')
    for field in ['levelParams','type','value']:
        fail(ci[field]!=row[field], 'Actual API primary differs from certified same-side fullvalue: '+field)
    fail(set(ci['axioms'])!=set(row['axioms']),'Actual primary axiom domain differs from certified CI')

def equation_output(side,i,pf,safe):
    path=STAGE/f'{side}-eq{i}.json';formalci.written_during(path,pf);d=read(path)
    fail(set(d)!={'side','expectedModule','primaryBinding','getEqnsForReturnedSome','actualEquationNames',
        'equations','unfolding','probeMainModule','theoremProofValuesExported'},'Equation API output schema differs')
    module=(gen.SOURCE_MODULES if side=='original' else gen.GEN_MODULES)[i];main=pf['data']['actual_module_identity']
    fail(d['side']!=side or d['expectedModule']!=module or d['probeMainModule']!=main
         or d['getEqnsForReturnedSome'] is not True or d['theoremProofValuesExported'] is not False,'Actual equation side/getter metadata differs')
    primary_matches(d['primaryBinding'],safe[gen.PRIMARY[i]],module,main)
    names=d['actualEquationNames']
    fail(not isinstance(names,list) or any(not isinstance(n,str) for n in names) or len(set(names))!=len(names)
         or gen.REQUIRED[i] not in names or len(d['equations'])!=len(names),'Required exact equation absent from actual getter')
    for name,e in zip(names,d['equations'],strict=True):
        fail(set(e)!={'getter','inversePrimary','CI'} or e['getter']!='Lean.Meta.getEqnsFor?'
             or e['inversePrimary']!=gen.PRIMARY[i],'Actual getEqnsFor?/isEqnThm? exact inverse differs')
        formalci.checked_api_ci(e['CI'],'theorem',name,module,main)
    if d['unfolding'] is not None:
        u=d['unfolding'];fail(set(u)!={'getter','CI'} or u['getter']!='Lean.Meta.getUnfoldEqnFor?','Unfolding API evidence differs')
        formalci.checked_api_ci(u['CI'],'theorem',u['CI']['actualName'],module,main)
    return d,path

def auxiliary_output(side,pf,safe):
    path=STAGE/f'{side}-aux.json';formalci.written_during(path,pf);d=read(path)
    fail(set(d)!={'schemaVersion','side','probeMainModule','getter','primaryValueRefs','primaryBinding','helper','theoremProofValuesExported'}
         or d['schemaVersion']!=1 or d['side']!=side or d['getter']!='Lean.Expr.getUsedConstants'
         or d['theoremProofValuesExported'] is not False or d['probeMainModule']!=pf['data']['actual_module_identity'],'Auxiliary primitive output schema differs')
    module=(gen.SOURCE_MODULES if side=='original' else gen.GEN_MODULES)[1]
    primary_matches(d['primaryBinding'],safe[gen.AUX_PRIMARY],module,d['probeMainModule'])
    names=d['primaryValueRefs']
    fail(not isinstance(names,list) or any(not isinstance(n,str) for n in names) or names!=sorted(set(names))
         or set(names)!=refs.kernel_refs(safe[gen.AUX_PRIMARY]['value']) or gen.AUX not in names,
         'Helper is not exact actual literal occurrence in certified primary complete value')
    formalci.checked_api_ci(d['helper'],'theorem',gen.AUX,module,d['probeMainModule'])
    fail(d['helper']['owner']['kind']!='ImportedModule','Definition-generated auxiliary must actually belong to imported certified module')
    return d,path

def certify(definitions=None):
    fail(sha(Path(gen.__file__))!=PRODUCER_SHA,'Frozen extra-CI producer changed')
    fail(sha(Path(compatible.__file__))!=COMPATIBLE_SHA,'Frozen compatible producer changed')
    p=compatible.plan();fail(read(STAGE/'preparation2.json')!=p,'Exact compatible companion preparation changed')
    for path,h in p['input_hashes'].items():fail(sha(context.file(path))!=h,'Companion input changed: '+path)
    for entry in p['external_lean_api_sources']:
        fail(sha(Path(entry['path']))!=entry['sha256'],'Fixed typed Lean API source changed: '+entry['lean_source_suffix'])
    m=read(V/'flp3/f3/manifest.json')
    if definitions is None:definitions,_=nodes.base.definition_interfaces(m)
    expected=[next(d for d in definitions if d['source_module']==module) for module in gen.SOURCE_MODULES]
    fail(expected!=p['definition_certificates'],'Actual current primary Definition certificates differ')
    ms=compatible.manifests(p);preflights={};results={};outputs={}
    for name,f in p['files'].items():
        source=TASK/f['source'];raw,_=gen.render(f['side'])
        fail(source.read_bytes()!=raw or sha(source)!=f['source_sha256'],'Exact frozen companion source differs')
        manifest=TASK/f['manifest'];fail(read(manifest)!=ms[name],'Exact companion compile manifest differs')
        pf=context.record(source,manifest,'modecheck',name,STAGE);preflights[f['side']]=pf
        if f['side']=='generated':
            for interface in expected:
                dep=next(d for d in pf['data']['dependency_oleans'] if d['module']==interface['platform_module'])
                fail(dep['sha256_before']!=interface['output_lean_sha256'],'Probe imported Definition OLean differs from actual certificate')
        safe=gen.rows(f['side']);equations=[]
        for i in range(2):
            d,path=equation_output(f['side'],i,pf,safe);equations.append(d);outputs[rel(path)]=sha(path)
        auxiliary,path=auxiliary_output(f['side'],pf,safe);outputs[rel(path)]=sha(path)
        results[f['side']]={'equations':equations,'auxiliary':auxiliary}
    old,new=results['original'],results['generated'];comparisons=[]
    for i,(a,b) in enumerate(zip(old['equations'],new['equations'],strict=True)):
        source_equal(a['primaryBinding'],b['primaryBinding'],'def')
        fail(a['actualEquationNames']!=b['actualEquationNames'],'Source/generated actual API equation domains differ')
        for x,y in zip(a['equations'],b['equations'],strict=True):source_equal(x['CI'],y['CI'])
        fail((a['unfolding'] is None)!=(b['unfolding'] is None),'Actual unfolding domains differ')
        if a['unfolding'] is not None:source_equal(a['unfolding']['CI'],b['unfolding']['CI'])
        comparisons.append({'name':gen.REQUIRED[i],'primary':gen.PRIMARY[i],'type_equal':True,'primary_full_value_equal':True,
            'exact_getter_inverse_relation':True,'source_owner':a['equations'][a['actualEquationNames'].index(gen.REQUIRED[i])]['CI']['owner'],
            'generated_owner':b['equations'][b['actualEquationNames'].index(gen.REQUIRED[i])]['CI']['owner']})
    source_equal(old['auxiliary']['primaryBinding'],new['auxiliary']['primaryBinding'],'def')
    source_equal(old['auxiliary']['helper'],new['auxiliary']['helper'])
    comparisons.append({'name':gen.AUX,'primary':gen.AUX_PRIMARY,'type_equal':True,'primary_full_value_equal':True,
        'literal_primary_full_value_reference':True,'source_owner':old['auxiliary']['helper']['owner'],'generated_owner':new['auxiliary']['helper']['owner']})
    return {'schema_version':1,'artifact_kind':'formal-log-f3-extra-ci-kernel-certificate','validated':True,
        'provided_names':gen.REQUIRED+[gen.AUX],'comparisons':comparisons,'definition_certificates':expected,
        'preparation':rel(STAGE/'preparation2.json'),'preparation_sha256':sha(STAGE/'preparation2.json'),
        'retained_original_preparation':p['retained_original_preparation'],'external_lean_api_sources':p['external_lean_api_sources'],
        'input_hashes':p['input_hashes'],'implementation_hashes':{rel(SELF):sha(SELF),rel(Path(gen.__file__)):sha(Path(gen.__file__)),rel(Path(compatible.__file__)):sha(Path(compatible.__file__)),rel(Path(formalci.__file__)):sha(Path(formalci.__file__))},
        'preflights':preflights,'output_json_sha256':outputs,'max_file_seconds':max(pf['data']['seconds'] for pf in preflights.values()),
        'Std3_only':True,'closed_types':True,'full_def_values_equal':True,'theorem_values_null':True,
        'name_prefix_inference_used':False,'source_scope_partial':True,'server_parent_pending':True,'submission_ready':False}

def validate_extra_ci(definitions=None):
    c=certify(definitions);p=STAGE/CERT_NAME
    fail(not p.is_file() or read(p)!=c,'Extra CI certificate missing/stale after readonly replay')
    return {'path':rel(p),'sha256':sha(p),'data':c}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--validate-only',action='store_true');a=p.parse_args()
    try:
        if a.certify_existing:
            c=certify();path=STAGE/CERT_NAME;context.write_exact(path,c);r={'path':rel(path),'sha256':sha(path),'data':c}
        else:r=validate_extra_ci()
        print(json.dumps({'validated':True,'certificate':r['path'],'sha256':r['sha256'],'provided_names':r['data']['provided_names'],'max_file_seconds':r['data']['max_file_seconds'],'submission_ready':False},indent=2))
    except (ValueError,KeyError,StopIteration,FileNotFoundError,TypeError) as e:
        print(json.dumps({'validated':False,'error':str(e)}));raise SystemExit(2)

if __name__=='__main__':main()
