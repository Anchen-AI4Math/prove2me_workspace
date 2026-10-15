"""Pure AP18 source-faithful multiplicity definition, with three full-CI witnesses."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_weighted_simplex_domains_providers as ap9
TASK,ROOT,V=ap9.TASK,ap9.ROOT,ap9.V;SELF=Path(__file__).resolve()
STAGE=V/'ap18/multiplicity';COMMIT=ap9.COMMIT
SOURCE_MODULE='OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics'
PLATFORM_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity'
PROVIDER_FILE=PLATFORM_MODULE.replace('.','/')+'.lean'
SOURCE=TASK/('port/lean/'+SOURCE_MODULE.replace('.','/')+'.lean');ORIGINAL=TASK/('source/lean/'+SOURCE_MODULE.replace('.','/')+'.lean')
CORE=ap9.CORE;COVERAGE=STAGE/'published29-coverage.json'
IMPORTS=['Mathlib.Data.Finset.Card','Mathlib.Algebra.BigOperators.Group.Finset.Defs']
NAMES=['OAI.PiExponent.Collision.multiplicity'];SPECS=[(NAMES[0],1120,1274,34,36)]
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT=ap9.SOURCE_SNAPSHOT,ap9.GENERATED_SNAPSHOT
SOURCE_JSON,GENERATED_JSON=ap9.SOURCE_JSON,ap9.GENERATED_JSON;CONFIGS=['multiplicity']
RUNNER=TASK/'scripts/preflight_staged_module_windows_bounded.py';CONSUMER=TASK/'scripts/certify_collision_multiplicity_existing.py'
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
read,encode,sha,sha_bytes,need,rel,workspace_rel=ap9.read,ap9.encode,ap9.sha,ap9.sha_bytes,ap9.need,ap9.rel,ap9.workspace_rel

def config(key='multiplicity'):
    need(key=='multiplicity','Unknown provider key')
    return {'stage':STAGE,'source_module':SOURCE_MODULE,'platform_module':PLATFORM_MODULE,'provider_file':PROVIDER_FILE,'names':NAMES,'source':SOURCE,'original':ORIGINAL,'imports':IMPORTS}

def actual_coverage():
    progress=read(V/'verified-stage-progress.json');need(progress['definition_count']==29,'Expected actual Published29 baseline')
    rows=[]
    for r in progress['definitions']:
        path=TASK/r['publication_record'];p=read(path);need(sha(path)==r['publication_record_sha256'],'Actual Published record differs')
        wire=p['publish_intent']['payload']['definition'];body=p['target_readback']['body']
        need(body['definition']==wire and body['status']=='Definition' and sha_bytes(wire.encode())==r['source_sha256'],'Actual Published literal source/readback differs')
        # None of the literal bodies even mentions this identifier, hence none
        # can declare the selected source CI. Never infer coverage from labels.
        need('multiplicity' not in wire,'Published identifier occurrence needs a direct namespace/CI audit')
        rows.append({'definition_id':r['definition_id'],'definition_name':r['definition_name'],'publication_record':r['publication_record'],'publication_record_sha256':sha(path),'literal_definition_sha256':sha_bytes(wire.encode()),'mentions_multiplicity':False})
    return {'schema_version':1,'artifact_kind':'ap18-exact-Published29-multiplicity-coverage','audited_definition_count':29,'queried_names':NAMES,'none_provided':True,'records':rows,'Lean_started':False,'API_used':False}

def authority(c=None):
    raw=SOURCE.read_bytes();orig=ORIGINAL.read_bytes().replace(b'\r\n',b'\n')
    am=next(m for m in read(ap9.AST)['modules'] if m['module']==SOURCE_MODULE);sm=next(m for m in read(ap9.SCOPES)['modules'] if m['source']==SOURCE_MODULE.replace('.','/')+'.lean')
    need(am['source_sha256']==sm['source_sha256']==sha(SOURCE),'Original AST/scope source binding differs')
    owners={r['source_name']:r for r in read(ap9.OWNERS)['owners'] if r['source_name'] in NAMES};graph={r['name']:r for r in map(json.loads,ap9.GRAPH.read_text(encoding='utf-8').splitlines())};rows=[]
    for name,a,b,first,last in SPECS:
        u=next(u for u in am['units'] if name in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==name);o=owners[name];command=raw[a:b];contexts=[raw[x['range']['start']['offset']:x['range']['end']['offset']].decode() for x in s['context_commands']]
        need(u['start']['offset']==a and u['end']['offset']==b and [u['start']['line'],u['end']['line']]==[first,last] and u['graph_names']==[name] and u['graph_kinds']==['def'] and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance'],'Exact source Def AST differs')
        need(s['namespace']=='OAI.PiExponent.Collision' and all(x['kind']=='namespace' for x in s['scope_stack']) and contexts==['open scoped BigOperators'],'Actual universe/section/instance context differs')
        need(o['source_module']==SOURCE_MODULE and o['source_sha256']==sha(SOURCE) and o['command_unit']==SOURCE_MODULE+':'+str(a) and o['unit_start_offset']==a and o['unit_end_offset']==b and o['graph_kind']=='def' and not o['source_private'],'Actual source CI owner differs')
        need(orig.count(command.replace(b'\r\n',b'\n'))==1 and graph[name]['typeDeps']==graph[name]['valueDeps']==[],'Original literal Def or project closure differs')
        rows.append({'name':name,'start':a,'end':b,'source_lines':[first,last],'sha256':sha_bytes(command),'bytes':command,'ast':u,'scope':s,'owner':o,'graph':graph[name],'contexts':contexts})
    return rows

def stage_files(key='multiplicity'):
    c=config(key);units=authority(c);coverage=read(COVERAGE)
    need(coverage['audited_definition_count']==29 and coverage['none_provided'] is True and coverage['queried_names']==NAMES,'Frozen Published29 coverage differs')
    for r in coverage['records']:need(sha(TASK/r['publication_record'])==r['publication_record_sha256'],'Frozen actual Published record changed')
    body=(''.join('import '+m+'\n' for m in IMPORTS)+'\nnamespace OAI.PiExponent.Collision\n\nopen scoped BigOperators\n\n').encode()+units[0]['bytes']+b'\n\nend OAI.PiExponent.Collision\n'
    need(b'theorem ' not in body and b'sorry' not in body,'Definition provider contains proof material')
    outputs={PROVIDER_FILE:body,SOURCE_SNAPSHOT:ap9.snapshot(c,units,False),GENERATED_SNAPSHOT:ap9.snapshot(c,units,True)}
    paths=[SELF,CONSUMER,Path(ap9.__file__),SOURCE,ORIGINAL,ap9.AST,ap9.SCOPES,ap9.GRAPH,ap9.OWNERS,CORE,ap9.RUNTIME,ap9.PREFLIGHT,ap9.CONTEXT,COVERAGE,RUNNER]
    inputs={rel(p):sha(p) for p in paths};inputs.update({r['publication_record']:r['publication_record_sha256'] for r in coverage['records']})
    plans=[(PROVIDER_FILE,IMPORTS,'emit-olean'),(SOURCE_SNAPSHOT,['Lean',SOURCE_MODULE],'modecheck'),(GENERATED_SNAPSHOT,['Lean',PLATFORM_MODULE],'modecheck')];commands=[]
    for i,(f,imports,mode) in enumerate(plans,1):
        outputs[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap18-multiplicity-Def-bounded-manifest','output':workspace_rel(STAGE/f),'output_sha256':sha_bytes(outputs[f]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(ap9.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(ap9.PREFLIGHT),'validated':False,'submission_ready':False})
        commands.append('& '+repr(PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap18/multiplicity/'+f+' --root ap18/multiplicity --imports-manifest ap18/multiplicity/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    metadata={'definition_title':'Multiplicity of a group in a finite row set','natural_language_statement':r'Let $\iota$ and $\kappa$ be types, let $s\subset\iota$ be finite, and let $g:\iota\to\kappa$. For $a\in\kappa$, define'+'\n\n'+r'$$m_s(g,a)=\#\{i\in s:g(i)=a\}. $$'+'\n\n'+r'The definition assumes decidable equality on $\kappa$. It counts how many rows occupy each group and provides the original data for collision bounds. No finiteness assumption on either ambient type is required.','source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean#L34-L36','tags':['combinatorics','number-theory','openai-pi-exponent-017']}
    outputs['academic-metadata.json']=encode(metadata)
    outputs['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap18-collision-multiplicity-data-preparation','source_commit':COMMIT,'source_module':SOURCE_MODULE,'platform_module':PLATFORM_MODULE,'provided_names':NAMES,'provider_file':PROVIDER_FILE,'imports':IMPORTS,'exact_source_units':[{k:v for k,v in r.items() if k!='bytes'} for r in units],'source_context_commands':['open scoped BigOperators'],'contains_theorems':False,'own_structures_constructors_recursors':[],'published_coverage':rel(COVERAGE),'published_coverage_sha256':sha(COVERAGE),'source_path':rel(SOURCE),'source_sha256':sha(SOURCE),'original_source_path':rel(ORIGINAL),'original_source_sha256':sha(ORIGINAL),'original_port_definitions_equal_modulo_line_endings':True,'input_hashes':inputs,'expected_provider_olean':rel(V/'staged-build/lib/lean'/Path(PROVIDER_FILE).with_suffix('.olean')),'commands':commands,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    outputs['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return outputs

def check_only(key='multiplicity'):
    outputs=stage_files(key)
    for name,raw in outputs.items():need((STAGE/name).read_bytes()==raw,'Immutable provider differs: '+name)
    for i,f in enumerate([PROVIDER_FILE,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):m=read(STAGE/f'c{i}.json');ap9.runner.verify_manifest_inputs(m);ap9.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(outputs),'provided_names':NAMES,'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        if not COVERAGE.exists():COVERAGE.parent.mkdir(parents=True,exist_ok=True);COVERAGE.write_bytes(encode(actual_coverage()))
        for name,raw in stage_files().items():
            path=STAGE/name
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+name)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
