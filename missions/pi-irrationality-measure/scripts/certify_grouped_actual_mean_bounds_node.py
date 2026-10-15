"""Strict pure replay of four actual grouped actualMean_bounds preflights."""
from __future__ import annotations
import argparse
from datetime import datetime
from itertools import permutations
import json
from pathlib import Path
import stage_grouped_actual_mean_bounds_node as stage
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context

SELF=Path(__file__).resolve()
STD3={'propext','Classical.choice','Quot.sound'}
TASK,V,STAGE=stage.TASK,stage.V,stage.STAGE
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel

def written(path,pf):
    end=datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(path.is_file() and end-pf['data']['seconds']-2<=path.stat().st_mtime<=end+2,'Actual snapshot was not written during its compiler interval')
    return read(path)

def preflight(filename,p):
    spec=p['files'][filename];module=filename[:-5].replace('/','.')
    r=context.record(STAGE/filename,STAGE/spec['manifest'],spec['mode'],module,STAGE);d=r['data']
    need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300 and d['timeout_seconds']==300 and d['mode']==spec['mode'] and 'emit_olean' not in d,'Bounded actual compiler record differs')
    if spec['mode']=='emit-olean':
        path=stage.base.runner.STAGED_LIB/Path(filename).with_suffix('.olean')
        need(d['output_olean']==rel(path) and d['output_olean_sha256']==sha(path),'Actual emitted Solution OLean differs')
    else:need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Nonemitter created OLean')
    return r

def type_rows(filename,pf,names):
    rows=written(STAGE/filename,pf);need(isinstance(rows,list) and len(rows)==len(names),'TypeOnly domain differs');result={}
    for row,name in zip(rows,names,strict=True):
        need(set(row)=={'name','levelParams','type','value','prettyType'} and row['name']==name and row['value'] is None and isinstance(row['prettyType'],str) and row['prettyType'],'Expected exact TypeOnly theorem row')
        kernel.checked_expr(row['type'],set(row['levelParams']));kernel.normalized_type(row);result[name]=row
    return result

def proof_rows(filename,pf,side,roots,modules,boundary):
    doc=written(STAGE/filename,pf)
    need(set(doc)=={'schemaVersion','side','probeMainModule','rootNames','boundaryNames','rows'} and doc['schemaVersion']==1 and doc['side']==side and doc['probeMainModule']==('SourceSnapshot' if side=='source' else 'GeneratedSnapshot') and doc['rootNames']==roots and doc['boundaryNames']==sorted(boundary),'Actual proof-reference domain differs')
    names=[r['name'] for r in doc['rows']];need(names==sorted(set(names)) and set(roots)<=set(names),'Actual CI domain missing/duplicate roots')
    rows={}
    for row in doc['rows']:
        owner=row['owner']['module'];need(owner in modules,'Actual source/helper owner outside exact module domain')
        rows[row['name']]=kernel.evidence_row(row,name=row['name'],module=owner,helper=True)
    return rows

def pair_extra(source,generated,public_map):
    need(len(source)==len(generated) and len(source)<=9,'Actual automatic CI domain differs or needs a bounded pairing probe')
    left=[source[n] for n in sorted(source)];right=[generated[n] for n in sorted(generated)];matches=[]
    for perm in permutations(right):
        mapping=public_map|{a['name']:b['name'] for a,b in zip(left,perm,strict=True)}
        if all(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1] for a,b in zip(left,perm,strict=True)):
            matches.append(mapping)
        need(len(matches)<=1,'Automatic CI types do not give a unique genuine pairing')
    need(len(matches)==1,'Automatic CI full types fail to pair');return matches[0]

def validate():
    stage.check_only();p=read(STAGE/'preparation.json')
    need(p['validated'] is False and p['submission_ready'] is False and p['proposal_status']=='Draft' and p['global_solution_preserves_literal_source_proof'] is True,'Preparation semantics differ')
    graph,closure,provided,units,_,_=stage.authority()
    records={f:preflight(f,p) for f in stage.FILES}
    source=type_rows(stage.SOURCE_TYPE_JSON,records[stage.SOURCE_SNAPSHOT],p['source_type_only_names'])
    generated=type_rows(stage.GENERATED_TYPE_JSON,records[stage.GENERATED_SNAPSHOT],p['generated_type_only_names'])
    source_proofs=proof_rows(stage.SOURCE_REFS_JSON,records[stage.SOURCE_SNAPSHOT],'source',p['source_type_only_names'],list(stage.HELPER_NAMES),set(p['provider_subtracted_names']))
    generated_proofs=proof_rows(stage.GENERATED_REFS_JSON,records[stage.GENERATED_SNAPSHOT],'generated',p['generated_type_only_names'],[stage.SOLUTION_MODULE],set(p['provider_subtracted_names']))
    owners={r['name']:r['module'] for r in units}|{stage.TARGET:stage.TARGET_MODULE}
    for name,module in owners.items():need(source_proofs[name]['owner']['module']==module,'Source public root owner differs: '+name)
    public_map={n:n for n in p['inline_helper_names']}|{stage.TARGET:'solution'}
    source_extra={n:r for n,r in source_proofs.items() if n not in public_map};generated_extra={n:r for n,r in generated_proofs.items() if n not in public_map.values()}
    need(all(n not in graph or graph[n]['isPrivate'] for n in source_extra),'A new public source dependency lacks AST provenance')
    mapping=pair_extra(source_extra,generated_extra,public_map)
    for n,m in public_map.items():
        a,b=source[n],generated[m]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1],'Exact original/generated theorem type differs: '+n)
    for n,m in mapping.items():
        a,b=source_proofs[n],generated_proofs[m]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1] and a['axioms']==b['axioms'],'Actual paired CI type/Std3 differs: '+n)
        for field in ['typeRefs','valueRefs','allUsedConstants']:
            need(sorted({mapping.get(x,x) for x in a[field]})==b[field],'Actual source/generated proof constants differ: '+n+':'+field)
    for rows,known in [(source_proofs,set(source_proofs)),(generated_proofs,set(generated_proofs))]:
        for row in rows.values():
            for n in row['allUsedConstants']:
                if n in graph or n.startswith('OAI.') or n.startswith('_private.OAI.'):
                    need(n in known or n in p['provider_subtracted_names'],'Uncovered actual project proof dependency: '+n)
    providers={}
    for key in stage.base.ap10.CONFIGS:
        c=stage.base.ap10.config(key);cert=c['stage']/('actual-provider-validation-helper-v2.json' if key=='determinant' else 'actual-provider-validation.json');r=read(cert);olean=TASK/r['provider_olean']
        need(sha(olean)==r['provider_olean_sha256'] and r['validated'] is True and r['Std3_only'] is True,'Previously certified provider OLean changed')
        if key=='determinant':
            dep=kernel.imported_dep(records[stage.SOLUTION_OUTPUT],c['platform_module'])
            need(Path(dep['path']).resolve()==olean.resolve() and dep['sha256_before']==sha(olean),'Solution does not use the actual certified determinant provider')
        providers[key]={'certificate':rel(cert),'certificate_sha256':sha(cert),'olean':rel(olean),'olean_sha256':sha(olean)}
    target=(STAGE/stage.TARGET_OUTPUT).read_bytes()
    need(target==(p['preamble']+p['formal_statement']).encode() and target==(STAGE/'wire-theorem-source.lean').read_bytes(),'Target wire differs from compiled statement')
    solution=(STAGE/stage.SOLUTION_OUTPUT).read_bytes();need(b'theorem solution ' in solution and b'sorry' not in solution,'Global solution missing or contains sorry')
    return {'schema_version':1,'artifact_kind':'ap12-grouped-actual-mean-bounds-node-validation','source_commit':stage.COMMIT,'source_name':stage.TARGET,'platform_name':stage.PLATFORM_NAME,'source_module':stage.TARGET_MODULE,'source_byte_range':[4002,4395],'solution_module':stage.SOLUTION_MODULE,'solution_source_sha256':sha(STAGE/stage.SOLUTION_OUTPUT),'solution_olean':records[stage.SOLUTION_OUTPUT]['data']['output_olean'],'solution_olean_sha256':records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],'preparation_sha256':sha(STAGE/'preparation.json'),'target_wire_sha256':sha(STAGE/stage.TARGET_OUTPUT),'preflights':records,'actual_provider_bindings':providers,'source_and_generated_types_equal':True,'source_and_generated_theorem_values_null':True,'source_and_generated_actual_proof_references_paired':True,'actual_automatic_CI_pairs':[[n,m] for n,m in mapping.items() if n not in public_map],'graph_closure_names':sorted(closure),'inline_helper_names':p['inline_helper_names'],'axioms':{side:{n:r['axioms'] for n,r in rows.items()} for side,rows in [('source',source_proofs),('generated',generated_proofs)]},'Std3_only':True,'json_sha256':{f:sha(STAGE/f) for f in [stage.SOURCE_TYPE_JSON,stage.GENERATED_TYPE_JSON,stage.SOURCE_REFS_JSON,stage.GENERATED_REFS_JSON]},'implementation_hashes':{rel(f):sha(f) for f in [SELF,stage.SELF,Path(kernel.__file__),Path(context.__file__),Path(kernel.checked_expr.__code__.co_filename)]},'max_file_seconds':max(x['data']['seconds'] for x in records.values()),'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);m=p.add_mutually_exclusive_group(required=True);m.add_argument('--certify-existing',action='store_true');m.add_argument('--check-only',action='store_true');a=p.parse_args();r=validate();path=STAGE/stage.CERTIFICATE;raw=stage.encode(r)
    if path.exists():need(path.read_bytes()==raw,'Existing immutable certificate differs')
    elif a.certify_existing:path.write_bytes(raw)
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path) if path.exists() else None,'validated':True,'Std3_only':True,'max_file_seconds':r['max_file_seconds'],'Lean_started_by_consumer':False,'API_used':False},ensure_ascii=False,indent=2))
if __name__=='__main__':main()
