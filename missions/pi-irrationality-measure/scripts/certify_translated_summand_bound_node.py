"""Strict pure AP18 six-proof CI pairing, full types, actual public-child boundary and Std3."""
from __future__ import annotations
import argparse,json
from datetime import datetime
from pathlib import Path
import stage_translated_summand_bound_node as stage
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing
import validate_namespace_context_providers as context
SELF=Path(__file__).resolve();TASK,STAGE=stage.TASK,stage.STAGE
read,sha,need,rel=stage.read,stage.sha,stage.need,stage.rel

def written(path,pf):
    end=datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(path.is_file() and end-pf['data']['seconds']-2<=path.stat().st_mtime<=end+2,
         'Actual JSON was not written during this exact compiler invocation: '+rel(path))
    return read(path)

def preflight(filename,prep):
    spec=prep['files'][filename];record=context.record(STAGE/filename,STAGE/spec['manifest'],spec['mode'],filename[:-5].replace('/','.'),STAGE)
    d=record['data']
    need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300
         and d['timeout_seconds']==300 and d['mode']==spec['mode'] and 'emit_olean' not in d
         and d.get('runner')==rel(stage.RUNNER) and d.get('runner_sha256')==sha(stage.RUNNER)
         and d.get('legacy_runner_sha256')==sha(stage.LEGACY_RUNNER) and d.get('cleanup_completed') is True,
         'Actual bounded compiler witness differs: '+filename)
    if spec['mode']=='emit-olean':
        path=stage.route.data.ap9.runner.STAGED_LIB/Path(filename).with_suffix('.olean')
        need(d['output_olean']==rel(path) and d['output_olean_sha256']==sha(path),'Actual solution OLean differs')
    else:need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Non-emitter emitted an OLean')
    return record

def type_rows(filename,pf,names):
    rows=written(STAGE/filename,pf);need(isinstance(rows,list) and len(rows)==len(names),'TypeOnly full CI domain differs')
    out={}
    for row,name in zip(rows,names,strict=True):
        need(set(row)=={'name','levelParams','type','value','prettyType'} and row['name']==name
             and row['value'] is None and isinstance(row['prettyType'],str) and bool(row['prettyType']),
             'Actual TypeOnly CI schema or theorem proof value differs: '+name)
        kernel.checked_expr(row['type'],set(row['levelParams']));kernel.normalized_type(row);out[name]=row
    return out

def proof_rows(filename,pf,side,roots,modules,boundary):
    doc=written(STAGE/filename,pf)
    need(set(doc)=={'schemaVersion','side','probeMainModule','rootNames','boundaryNames','rows'}
         and doc['schemaVersion']==1 and doc['side']==side
         and doc['probeMainModule']==('SourceSnapshot' if side=='source' else 'GeneratedSnapshot')
         and doc['rootNames']==roots and doc['boundaryNames']==sorted(boundary),'Actual proof reference envelope differs')
    names=[r['name'] for r in doc['rows']]
    need(names==sorted(set(names)) and set(roots)<=set(names),'Actual closed proof CI roots/domain differ')
    out={}
    for row in doc['rows']:
        owner=row['owner']['module'];need(owner in modules,'Uncertified proof CI owner: '+owner)
        out[row['name']]=kernel.evidence_row(row,name=row['name'],module=owner,helper=True)
    return out

def validate():
    stage.check_only();prep=read(STAGE/'preparation.json')
    need(prep['validated'] is False and prep['submission_ready'] is False and prep['proposal_status']=='Draft'
         and prep['original_proof_AST_units']==6 and prep['original_source_lines']==110
         and prep['all_original_proof_suffixes_unchanged'] is True and prep['only_target_binding_name_changed'] is True
         and prep['existing_port_adaptations']==[] and prep['multiplicity_Published_and_fullDef_certificate_pending'] is False
         and prep['sum_weight_Accepted_closed_child_pending'] is False,'Literal AP18 source/preparation or actual prerequisite gate differs')
    units,closure,_,_,_=stage.route.source_units();boundary={stage.route.PARENT,stage.route.data.NAMES[0]}
    need(set(prep['provider_subtracted_names'])==boundary and set(prep['graph_closure_names'])==closure,'Exact eight-CI source/public boundary differs')
    records={f:preflight(f,prep) for f in stage.FILES}
    source=type_rows(stage.SOURCE_TYPE_JSON,records[stage.SOURCE_SNAPSHOT],prep['source_type_only_names'])
    generated=type_rows(stage.GENERATED_TYPE_JSON,records[stage.GENERATED_SNAPSHOT],prep['generated_type_only_names'])
    modules=sorted({u['module'] for u in units})
    left=proof_rows(stage.SOURCE_REFS_JSON,records[stage.SOURCE_SNAPSHOT],'source',prep['source_type_only_names'],modules+['SourceSnapshot'],boundary)
    right=proof_rows(stage.GENERATED_REFS_JSON,records[stage.GENERATED_SNAPSHOT],'generated',prep['generated_type_only_names'],
        [stage.SOLUTION_MODULE,stage.route.data.PLATFORM_MODULE,stage.CHILD_MODULE,'GeneratedSnapshot'],boundary)
    for u in units:need(left[u['name']]['owner']['module']==u['module'],'Original six-proof source CI owner differs')
    for n in prep['generated_type_only_names']:need(right[n]['owner']['module']==stage.SOLUTION_MODULE,'Generated literal proof is not owned by actual solution emitter')
    public_map={n:n for n in prep['inline_helper_names']};public_map[stage.TARGET]='solution'
    graph={r['name']:r for r in map(json.loads,stage.route.data.ap9.GRAPH.read_text(encoding='utf-8').splitlines())}
    extra_source={n:r for n,r in left.items() if n not in public_map}
    extra_generated={n:r for n,r in right.items() if n not in public_map.values()}
    need(all(n not in graph or graph[n]['isPrivate'] for n in extra_source),'Extra public source CI lacks original AST authority')
    mapping=pairing.pair_extra(extra_source,extra_generated,public_map)
    for n,m in public_map.items():
        a,b=source[n],generated[m]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1],
             'Original/generated full theorem type differs: '+n)
    for n,m in mapping.items():
        a,b=left[n],right[m]
        need(kernel.normalized_type(a)[0]==kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1],mapping)==kernel.normalized_type(b)[1]
             and a['axioms']==b['axioms'],'Actual closed CI full type/Std3 differs: '+n)
        for key in ['typeRefs','valueRefs','allUsedConstants']:
            need(sorted(mapping.get(x,x) for x in a[key])==b[key],'Actual source/generated direct references differ: '+n+':'+key)
        for x in b['allUsedConstants']:
            if x.startswith('OAI.') or x.startswith('_private.') and '.OAI.' in x:
                need(x in right or x in boundary,'Project reference lacks an exact original source/public boundary: '+x)
    # Same-process repeated access hash-gates the identical certificates and all
    # sidecars/kernel outputs/imported OLeans. It never omits the first replay.
    reports,pins=stage.boundary_evidence();child=reports['sum_weight'];data=reports['multiplicity']
    forbidden={r['actualName'] for r in child['actual_private_helper_mappings']}
    for row in right.values():
        need(row['owner']['module']!=stage.CHILD_MODULE and not forbidden&set(row['allUsedConstants']),
             'AP18 borrows a private sum-weight helper instead of its actual public target')
    for cert,module in [(data,stage.route.data.PLATFORM_MODULE),(child,stage.CHILD_MODULE)]:
        dep=kernel.imported_dep(records[stage.SOLUTION_OUTPUT],module);path=TASK/cert['provider_olean']
        need(Path(dep['path']).resolve()==path.resolve() and dep['sha256_before']==sha(path)==cert['provider_olean_sha256'],
             'Actual solution imported a different prerequisite OLean: '+module)
    data_dep=kernel.imported_dep(records[stage.TARGET_OUTPUT],stage.route.data.PLATFORM_MODULE)
    need(data_dep['sha256_before']==data['provider_olean_sha256'],'Comparator used a different Published full-Def provider')
    sol_dep=kernel.imported_dep(records[stage.GENERATED_SNAPSHOT],stage.SOLUTION_MODULE)
    need(sol_dep['sha256_before']==records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],'Generated snapshot imports a different genuine solution OLean')
    source_dep=kernel.imported_dep(records[stage.SOURCE_SNAPSHOT],stage.TARGET_MODULE)
    wire=STAGE/stage.TARGET_OUTPUT;solution=STAGE/stage.SOLUTION_OUTPUT
    need(wire.read_bytes()==(prep['preamble']+prep['formal_statement']).encode()==(STAGE/'wire-theorem-source.lean').read_bytes(),
         'Exact wire preamble+formal differs from compiled comparator bytes')
    need(solution.read_bytes().count(b'theorem solution')==1 and b'sorry' not in solution.read_bytes(),
         'Literal global solution contains missing proof material')
    return {'schema_version':1,'artifact_kind':'ap18-translated-summand-bound-node-validation',
      'source_commit':stage.COMMIT,'source_name':stage.TARGET,'platform_name':stage.PLATFORM_NAME,'source_module':stage.TARGET_MODULE,
      'source_byte_range':[4397,5770],'solution_module':stage.SOLUTION_MODULE,
      'solution_source_sha256':sha(solution),'solution_olean':records[stage.SOLUTION_OUTPUT]['data']['output_olean'],
      'solution_olean_sha256':records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],
      'target_wire_sha256':sha(wire),'preparation_sha256':sha(STAGE/'preparation.json'),'preflights':records,
      'original_proof_AST_units':6,'original_source_lines':110,'all_original_proof_suffixes_unchanged':True,
      'only_target_binding_name_changed':True,'existing_port_adaptations':[],
      'inline_helper_names':prep['inline_helper_names'],'graph_closure_names':sorted(closure),
      'public_parent_boundary_names':sorted(boundary),'no_private_sum_weight_helper_leakage':True,
      'sum_weight_actual_Accepted_theorem_id':child['accepted_theorem_id'],
      'sum_weight_actual_Accepted_proof_id':child['accepted_proof_id'],
      'sum_weight_mirror_certificate_sha256':sha(stage.CHILD_CERTIFICATE),'sum_weight_mirror_olean_sha256':child['provider_olean_sha256'],
      'multiplicity_actual_Published_definition_id':read(stage.PUBLISHED)['definition_id'],
      'multiplicity_fullDef_certificate_sha256':sha(stage.route.data.STAGE/'actual-provider-validation.json'),
      'multiplicity_Published_record_sha256':sha(stage.PUBLISHED),'multiplicity_olean_sha256':data['provider_olean_sha256'],
      'actual_original_source_olean':source_dep['path'],'actual_original_source_olean_sha256':source_dep['sha256_before'],
      'source_and_generated_types_equal':True,'source_and_generated_theorem_values_null':True,
      'source_and_generated_actual_proof_references_equal':True,
      'actual_automatic_CI_pairs':[[n,m] for n,m in mapping.items() if n not in public_map],
      'axioms':{side:{n:r['axioms'] for n,r in rows.items()} for side,rows in [('source',left),('generated',right)]},
      'json_sha256':{f:sha(STAGE/f) for f in [stage.SOURCE_TYPE_JSON,stage.GENERATED_TYPE_JSON,stage.SOURCE_REFS_JSON,stage.GENERATED_REFS_JSON]},
      'implementation_hashes':{rel(p):sha(p) for p in [SELF,stage.SELF,stage.route.SELF,stage.CHILD_PRODUCER,stage.CHILD_CONSUMER,
          Path(stage.data_consumer.__file__),Path(kernel.__file__),Path(pairing.__file__),Path(context.__file__),stage.RUNNER,stage.LEGACY_RUNNER]},
      'same_process_fixed_boundary_replay_cache':True,'first_full_boundary_mathematical_replays_required':True,
      'fixed_boundary_input_hashes':pins,'Std3_only':True,'max_file_seconds':max(r['data']['seconds'] for r in records.values()),
      'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    for flag in ['check-candidate','certify-existing','check-only']:g.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    if a.check_candidate:print(json.dumps(stage.check_candidate(),indent=2));return
    report=validate();path=STAGE/stage.CERTIFICATE;raw=stage.encode(report)
    if path.exists():need(path.read_bytes()==raw,'Immutable AP18 node certificate differs')
    elif a.certify_existing:path.write_bytes(raw)
    else:need(False,'Check-only requires a genuine existing AP18 certificate')
    print(json.dumps({'certificate':rel(path),'certificate_sha256':sha(path),'validated':True,'Std3_only':True,
      'max_file_seconds':report['max_file_seconds'],'Lean_started':False,'API_used':False},indent=2))
if __name__=='__main__':main()
