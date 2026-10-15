"""Read-only certification of the six actual source-root sketch compiler witnesses."""
from __future__ import annotations
import argparse
from datetime import datetime
import json
from pathlib import Path
import stage_source_root_graph as prep
import validate_namespace_context_providers as context
from certify_command_emission_probe import checked_expr

SELF=Path(__file__).resolve()
STD3={'propext','Classical.choice','Quot.sound'}
ROW_FIELDS={'name','levelParams','type','value','closedType','closedValue','isProp','actualOwner','axioms','typeRefs','valueRefs','Open_sketch_type_check'}

def need(ok,message): prep.need(ok,message)

def snapshot(filename, record, names, owners, is_open):
    path=prep.STAGE/filename
    rows=prep.read(path)
    need(isinstance(rows,list) and len(rows)==len(names),'Actual snapshot domain differs')
    end=datetime.fromisoformat(record['data']['at_utc']).timestamp()
    need(end-record['data']['seconds']-2 <= path.stat().st_mtime <= end+2,'Snapshot did not originate during the actual compiler interval')
    for row,name,owner in zip(rows,names,owners,strict=True):
        need(set(row)==ROW_FIELDS and row['name']==name and row['actualOwner']==owner,'Actual snapshot name/owner/schema differs')
        need(row['closedType'] is True and row['closedValue'] is True and row['isProp'] is True and row['value'] is None,'Expected closed theorem CI, Prop type, and null proof value')
        levels=row['levelParams']
        need(isinstance(levels,list) and all(isinstance(x,str) for x in levels) and len(levels)==len(set(levels)),'Invalid universe parameter domain')
        checked_expr(row['type'],set(levels))
        for field in ['typeRefs','valueRefs','axioms']:
            refs=row[field]
            need(isinstance(refs,list) and all(isinstance(x,str) for x in refs) and refs==sorted(set(refs)),'Reference/axiom domain differs')
        need(row['Open_sketch_type_check'] is is_open,'Snapshot semantic flag differs')
        need(set(row['axioms']) <= STD3|({'sorryAx'} if is_open else set()),'Unexpected axiom')
        need(('sorryAx' in row['axioms']) is is_open,'Open snapshot must carry sorryAx; source proof must be Std3 only')
    return rows

def validate():
    prep.check_only()
    p=prep.read(prep.STAGE/'preparation.json')
    need(p['validated'] is False and p['submission_ready'] is False and p['closed_proof'] is False and p['proposal_status']=='Draft','Preparation semantics differs')
    records={}
    for filename,item in p['files'].items():
        record=context.record(prep.STAGE/filename,prep.STAGE/item['manifest'],item['mode'],item['module'],prep.STAGE)
        d=record['data']
        need(d['mode']==item['mode'] and d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300 and d['timeout_seconds']==300 and 'emit_olean' not in d,'Bounded compiler witness failed or has wrong mode')
        if item['mode']=='emit-olean':
            expected=prep.runner.STAGED_LIB/Path(filename).with_suffix('.olean')
            need(d['output_olean']==prep.rel(expected) and d['output_olean_sha256']==prep.sha(expected),'Actual reference OLean differs')
        else:
            need(d['output_olean'] is None and d['output_olean_sha256'] is None,'Comparator or snapshot unexpectedly emitted OLean')
        records[filename]=record
    source=snapshot(prep.SOURCE_JSON,records[prep.SOURCE_SNAPSHOT],prep.NAMES+[prep.ROOT_NAME],[c['source_module'] for c in prep.CONFIGS]+['OAI.NumberTheory.PiExponent.Main'],False)
    generated=snapshot(prep.GENERATED_JSON,records[prep.GENERATED_SNAPSHOT],prep.NAMES+['solution'],[c['module'] for c in prep.CONFIGS]+['GeneratedSnapshot'],True)
    for left,right in zip(source,generated,strict=True):
        need(left['type']==right['type'] and left['levelParams']==right['levelParams'] and left['typeRefs']==right['typeRefs'],'Source/generated exact complete kernel type differs: '+left['name'])
    need(generated[3]['valueRefs']==sorted(prep.NAMES),'Root reduction does not use exactly the three original source parents')
    wire=(prep.STAGE/prep.SOLUTION_FILE).read_bytes()
    need(wire==(p['root_preamble']+p['root_solution']).encode() and wire==(prep.STAGE/'root-sketch-wire.lean').read_bytes(),'Root wire is not exact independently compiled submission source')
    need(b'theorem solution : PiEventualLowerBound' in wire and b'sorry' not in wire and b'namespace' not in wire,'Root must be sorry-free global literal solution')
    need(p['root_solution'].encode() in (prep.STAGE/prep.GENERATED_SNAPSHOT).read_bytes(),'Generated snapshot is not inspecting the identical root reduction body')
    for c,parent in zip(prep.CONFIGS,p['parents'],strict=True):
        raw=(prep.STAGE/c['file']).read_bytes()
        need(raw==(parent['preamble']+parent['formal_statement']).encode() and raw==(prep.STAGE/('parents/'+c['key']+'/wire-theorem-source.lean')).read_bytes(),'Parent wire differs from compiled declaration')
        need(parent['status']=='Open' and parent['name']==c['name'],'Parent changed source identity or Open status')
    return {'schema_version':1,'artifact_kind':'source-root-three-parent-open-sketch-validation','source_commit':prep.COMMIT,'root_id':prep.ROOT_ID,'root_name':prep.ROOT_NAME,'parent_names':prep.NAMES,'parent_status':'Open','Open_sketch':True,'closed_proof':False,'source_and_generated_parent_types_equal':True,'source_main_and_global_solution_types_equal':True,'actual_root_value_references':generated[3]['valueRefs'],'source_proofs_Std3_only':True,'generated_axioms':{x['name']:x['axioms'] for x in generated},'sorryAx_expected_only_from_Open_parents':True,'actual_owners':{'source':{x['name']:x['actualOwner'] for x in source},'generated':{x['name']:x['actualOwner'] for x in generated}},'reference_oleans':{c['name']:{'path':records[c['file']]['data']['output_olean'],'sha256':records[c['file']]['data']['output_olean_sha256']} for c in prep.CONFIGS},'root_sketch_file':prep.rel(prep.STAGE/prep.SOLUTION_FILE),'root_sketch_source_sha256':prep.sha(prep.STAGE/prep.SOLUTION_FILE),'preparation_sha256':prep.sha(prep.STAGE/'preparation.json'),'parent_wire_sha256':{c['name']:prep.sha(prep.STAGE/c['file']) for c in prep.CONFIGS},'snapshot_json_sha256':{x:prep.sha(prep.STAGE/x) for x in [prep.SOURCE_JSON,prep.GENERATED_JSON]},'preflights':records,'implementation_hashes':{prep.rel(x):prep.sha(x) for x in [SELF,prep.SELF,prep.CONTEXT,Path(prep.runner.__file__),Path(checked_expr.__code__.co_filename)]},'max_file_seconds':max(r['data']['seconds'] for r in records.values()),'validated':True,'submission_ready':False,'proposal_status':'Draft','Lean_started_by_consumer':False,'API_used':False}

def main():
    parser=argparse.ArgumentParser(description=__doc__);m=parser.add_mutually_exclusive_group(required=True);m.add_argument('--certify-existing',action='store_true');m.add_argument('--check-only',action='store_true');args=parser.parse_args()
    result=validate(); path=prep.STAGE/prep.CERTIFICATE; raw=prep.encode(result)
    if path.exists():need(path.read_bytes()==raw,'Immutable existing certificate differs')
    elif args.certify_existing:path.write_bytes(raw)
    print(json.dumps({'certificate':prep.rel(path),'certificate_sha256':prep.sha(path) if path.exists() else None,'validated':True,'Open_sketch':True,'closed_proof':False,'parent_names':prep.NAMES,'root_id':prep.ROOT_ID,'max_file_seconds':result['max_file_seconds'],'Lean_started_by_consumer':False,'API_used':False},ensure_ascii=False,indent=2))
if __name__=='__main__':main()
