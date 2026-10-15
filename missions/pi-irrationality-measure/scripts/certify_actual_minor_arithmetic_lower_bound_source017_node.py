"""Strict pure replay of AP17 existing source017 target and three original source proofs."""
from __future__ import annotations
import argparse,json
from datetime import datetime
from pathlib import Path
import stage_actual_minor_arithmetic_lower_bound_source017_node as stage
import certify_selected_minor_lower_child_mirror_probe_v5 as child_consumer
import certify_selected_minor_clearing_bound_node as clearing_cert
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context
SELF=Path(__file__).resolve();TASK,STAGE=stage.TASK,stage.STAGE
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel

def written(path, pf):
    end = datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(path.is_file() and end - pf['data']['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Actual JSON was not written in this compiler interval: ' + rel(path))
    return read(path)


def preflight(filename, prep):
    spec = prep['files'][filename]
    module = filename[:-5].replace('/', '.')
    record = context.record(STAGE / filename, STAGE / spec['manifest'],
                            spec['mode'], module, STAGE)
    d = record['data']
    need(d['success'] is True and d['exit_code'] == 0 and d['timed_out'] is False
         and 0 < d['seconds'] <= 300 and d['timeout_seconds'] == 300
         and d['mode'] == spec['mode'] and 'emit_olean' not in d
         and d.get('runner') == rel(stage.RUNNER)
         and d.get('runner_sha256') == sha(stage.RUNNER)
         and d.get('legacy_runner_sha256') == sha(stage.LEGACY_RUNNER)
         and d.get('cleanup_completed') is True,
         'Bounded actual compiler context differs: ' + filename)
    if spec['mode'] == 'emit-olean':
        olean = stage.clearing.base.runner.STAGED_LIB / Path(filename).with_suffix('.olean')
        need(d['output_olean'] == rel(olean) and d['output_olean_sha256'] == sha(olean),
             'Actual solution OLean differs')
    else:
        need(d['output_olean'] is None and d['output_olean_sha256'] is None,
             'A non-emitter unexpectedly emitted OLean')
    return record


def types(filename, pf, names):
    rows = written(STAGE / filename, pf)
    need(isinstance(rows, list) and len(rows) == len(names),
         'TypeOnly CI domain differs')
    out = {}
    for row, name in zip(rows, names, strict=True):
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['name'] == name and row['value'] is None
             and isinstance(row['prettyType'], str) and bool(row['prettyType']),
             'Actual theorem TypeOnly CI differs: ' + name)
        kernel.checked_expr(row['type'], set(row['levelParams']))
        kernel.normalized_type(row)
        out[name] = row
    return out


def proofs(filename, pf, side, roots, modules, boundary):
    doc = written(STAGE / filename, pf)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
         'rootNames', 'boundaryNames', 'rows'} and doc['schemaVersion'] == 1
         and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == sorted(boundary),
         'Actual proof-reference envelope differs')
    names = [row['name'] for row in doc['rows']]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual proof CI domain omits or duplicates roots')
    out = {}
    for row in doc['rows']:
        owner = row['owner']['module']
        need(owner in modules, 'Proof CI owner outside actual source/generated modules: ' + owner)
        out[row['name']] = kernel.evidence_row(row, name=row['name'],
                                                module=owner, helper=True)
    return out


def validate():
    stage.check_only();prep=read(STAGE/'preparation.json')
    need(prep['validated'] is False and prep['submission_ready'] is False and prep['original_proof_AST_units']==3 and prep['original_source_lines']==17 and prep['all_original_proof_suffixes_unchanged'] is True and prep['only_target_binding_name_changed'] is True and prep['existing_port_adaptations']==[],'Literal source017 preparation differs')
    graph,closure,provided,rows,commands,_,renamed,actual,det=stage.route.source_units()
    records={f:preflight(f,prep) for f in stage.FILES};boundary=set(prep['provider_subtracted_names'])
    need(boundary==closure&provided and stage.route.GENERIC_LOWER in boundary,'Exact generic public theorem boundary differs')
    for r in records.values():
        d=r['data'];need(d.get('runner')==rel(stage.RUNNER) and d.get('runner_sha256')==sha(stage.RUNNER) and d.get('legacy_runner_sha256')==sha(stage.LEGACY_RUNNER) and d.get('cleanup_completed') is True,'Actual AP17 bounded runner provenance differs')
    source=types(stage.SOURCE_TYPE_JSON,records[stage.SOURCE_SNAPSHOT],prep['source_type_only_names'])
    generated=types(stage.GENERATED_TYPE_JSON,records[stage.GENERATED_SNAPSHOT],prep['generated_type_only_names'])
    source_refs=proofs(stage.SOURCE_REFS_JSON,records[stage.SOURCE_SNAPSHOT],'source',prep['source_type_only_names'],[stage.TARGET_MODULE,'SourceSnapshot'],boundary)
    generated_refs=proofs(stage.GENERATED_REFS_JSON,records[stage.GENERATED_SNAPSHOT],'generated',prep['generated_type_only_names'],[stage.SOLUTION_MODULE,stage.child.MODULE,'GeneratedSnapshot'],boundary)
    for row in rows:need(source_refs[row['name']]['owner']['module']==stage.TARGET_MODULE,'Original source017 source CI owner differs')
    for n in prep['generated_type_only_names']:need(generated_refs[n]['owner']['module']==stage.SOLUTION_MODULE,'AP17 literal theorem does not belong to actual global solution module')
    public_map={n:n for n in prep['inline_helper_names']};public_map[stage.TARGET]='solution'
    source_extra={n:r for n,r in source_refs.items() if n not in public_map};generated_extra={n:r for n,r in generated_refs.items() if n not in public_map.values()}
    need(all(n not in graph or graph[n]['isPrivate'] for n in source_extra),'Uncertified extra public source CI lacks original AST')
    mapping=clearing_cert.pair_extra(source_extra,generated_extra,public_map)
    for n,m in public_map.items():
        a,b=source[n],generated[m];need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1],'Original/generated source017 full theorem type differs')
    for n,m in mapping.items():
        a,b=source_refs[n],generated_refs[m];need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0] and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1] and a['axioms']==b['axioms'],'Actual source017 proof CI full type/Std3 differs')
        for key in ['typeRefs','valueRefs','allUsedConstants']:need(sorted(mapping.get(x,x) for x in a[key])==b[key],'Actual source017 direct proof references differ: '+n+':'+key)
        for x in b['allUsedConstants']:
            if x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x:need(x in generated_refs or x in boundary,'AP17 project dependency lacks certified source closure')
    mirror=child_consumer.validate();path=stage.MIRROR_STAGE/stage.mirror.CERTIFICATE
    need(stage.encode(mirror)==path.read_bytes() and mirror['validated'] is True and mirror['accepted_parent_Proved'] is True and mirror['public_platform_boundary_names']==[stage.route.GENERIC_LOWER],'Actual Accepted generic lower private mirror replay differs')
    forbidden={r['actualName'] for r in mirror['actual_private_helper_mappings']}
    for row in generated_refs.values():need(not forbidden&set(row['allUsedConstants']) and row['owner']['module']!=stage.child.MODULE,'AP17 borrows a private generic helper instead of only the public Accepted target')
    dep=kernel.imported_dep(records[stage.SOLUTION_OUTPUT],stage.child.MODULE);olean=TASK/mirror['provider_olean'];need(Path(dep['path']).resolve()==olean.resolve() and dep['sha256_before']==sha(olean)==mirror['provider_olean_sha256'],'AP17 imported a different actual generic lower OLean')
    wire=STAGE/stage.TARGET_OUTPUT;solution=STAGE/stage.SOLUTION_OUTPUT
    need(wire.read_bytes()==stage.route.OPEN_WIRE.read_bytes()==(prep['preamble']+prep['formal_statement']).encode()==(STAGE/'wire-theorem-source.lean').read_bytes(),'Existing source017 public wire bytes changed')
    raw=solution.read_bytes();need(raw.count(b'theorem solution ')==1 and b'sorry' not in raw and b'FixedDeterminantFamily' not in raw,'AP17 global source proof contains unsupported material')
    return {'schema_version':1,'artifact_kind':'ap17-actual-minor-arithmetic-lower-bound-source017-validation','source_commit':stage.COMMIT,'source_name':stage.TARGET,'platform_name':stage.PLATFORM_NAME,'platform_theorem_id':stage.TARGET_ID,'source_module':stage.TARGET_MODULE,'source_byte_range':stage.route.TARGET_RANGE,'solution_module':stage.SOLUTION_MODULE,'solution_source_sha256':sha(solution),'solution_olean':records[stage.SOLUTION_OUTPUT]['data']['output_olean'],'solution_olean_sha256':records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],'target_wire_sha256':sha(wire),'exact_existing_Open_wire_unchanged':True,'preparation_sha256':sha(STAGE/'preparation.json'),'preflights':records,'original_proof_AST_units':3,'original_source_lines':17,'all_original_proof_suffixes_unchanged':True,'only_target_binding_name_changed':True,'existing_port_adaptations':[],'inline_helper_names':prep['inline_helper_names'],'generic_lower_public_boundary_names':[stage.route.GENERIC_LOWER],'generic_lower_actual_Accepted_theorem_id':mirror['accepted_theorem_id'],'generic_lower_actual_Accepted_proof_id':mirror['accepted_proof_id'],'generic_lower_mirror_certificate_sha256':sha(path),'generic_lower_mirror_olean_sha256':sha(olean),'no_private_generic_helper_leakage':True,'source_and_generated_types_equal':True,'source_and_generated_theorem_values_null':True,'source_and_generated_actual_proof_references_equal':True,'actual_automatic_CI_pairs':[[n,m] for n,m in mapping.items() if n not in public_map],'graph_closure_names':sorted(closure),'axioms':{side:{n:r['axioms'] for n,r in refs.items()} for side,refs in [('source',source_refs),('generated',generated_refs)]},'json_sha256':{f:sha(STAGE/f) for f in [stage.SOURCE_TYPE_JSON,stage.GENERATED_TYPE_JSON,stage.SOURCE_REFS_JSON,stage.GENERATED_REFS_JSON]},'implementation_hashes':{rel(f):sha(f) for f in [SELF,stage.SELF,stage.route.SELF,stage.child.SELF,stage.mirror.SELF,Path(child_consumer.__file__),Path(clearing_cert.__file__),Path(kernel.__file__),Path(context.__file__),stage.RUNNER,stage.LEGACY_RUNNER]},'Std3_only':True,'max_file_seconds':max(r['data']['seconds'] for r in records.values()),'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    for flag in ['check-candidate','certify-existing','check-only']:g.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    if a.check_candidate:print(json.dumps(stage.check_candidate(),indent=2));return
    report=validate();path=STAGE/stage.CERTIFICATE;raw=stage.encode(report)
    if path.exists():need(path.read_bytes()==raw,'Existing AP17 certificate differs')
    elif a.certify_existing:path.write_bytes(raw)
    else:need(False,'Check-only requires an existing actual AP17 certificate')
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path),'validated':True,'Std3_only':True,'max_file_seconds':report['max_file_seconds'],'Lean_started':False,'API_used':False},indent=2))
if __name__=='__main__':main()
