"""Pure AP15 staging of five original MatrixArithmetic scales/costs definitions."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_weighted_simplex_domains_providers as ap9
import stage_core_parent_data_providers as ap10
TASK,ROOT,V=ap9.TASK,ap9.ROOT,ap9.V;SELF=Path(__file__).resolve();STAGE=V/'ap15/scales-costs';COMMIT=ap9.COMMIT
SOURCE_MODULE='OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic'
PLATFORM_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts'
PROVIDER_FILE=PLATFORM_MODULE.replace('.','/')+'.lean'
SOURCE=TASK/('port/lean/'+SOURCE_MODULE.replace('.','/')+'.lean');ORIGINAL=TASK/('source/lean/'+SOURCE_MODULE.replace('.','/')+'.lean')
CORE=ap9.CORE;COVERAGE=V/'ap15/published28-scales-costs-coverage.json';PRIOR=ap10.config('arithmetic');IMPORTS=[PRIOR['platform_module']]
NAMES=['OAI.PiExponent.MatrixArithmetic.'+n for n in ['columnScale','rowScale','denominator','rowCost','columnCost']]
SPECS=[(NAMES[0],6054,6170,135,136),(NAMES[1],6174,6285,138,139),(NAMES[2],6289,6453,141,142),(NAMES[3],8932,9148,199,202),(NAMES[4],9152,9510,204,209)]
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT=ap9.SOURCE_SNAPSHOT,ap9.GENERATED_SNAPSHOT;SOURCE_JSON,GENERATED_JSON=ap9.SOURCE_JSON,ap9.GENERATED_JSON;CONFIGS=['scalescosts']
read,encode,sha,sha_bytes,need,rel,workspace_rel=ap9.read,ap9.encode,ap9.sha,ap9.sha_bytes,ap9.need,ap9.rel,ap9.workspace_rel

def config(key='scalescosts'):
    need(key=='scalescosts','Unknown provider key');return {'stage':STAGE,'source_module':SOURCE_MODULE,'platform_module':PLATFORM_MODULE,'provider_file':PROVIDER_FILE,'names':NAMES,'source':SOURCE,'original':ORIGINAL,'imports':IMPORTS}

def bindings():
    provided=set();pins={};witnesses=[]
    for c in [PRIOR,ap9.config('simplex'),ap9.config('domains')]:
        root=c['stage'];cert=root/'actual-provider-validation.json';pub=root/'publication/publication.json';r=read(cert);record=read(pub);body=root/c['provider_file']
        need(r['validated'] is True and r['Std3_only'] is True and r['provided_names']==c['names'] and r['source_and_generated_types_equal'] is True and r['definition_values_equal_and_exported'] is True and r['provider_source_sha256']==sha(body),'Actual prior full Def certificate differs')
        need(record['last_publish_verdict']['body']['status']=='PUBLISHED' and record['target_readback']['body']['status']=='Definition' and record['target_readback']['body']['definition']==record['publish_intent']['payload']['definition'] and record['target_readback']['body']['definition'].encode()==body.read_bytes(),'Actual Published prior source body differs')
        provided.update(c['names'])
        for p in [root/'preparation.json',body,cert,pub]:pins[rel(p)]=sha(p)
        witnesses.append({'module':c['platform_module'],'provided_names':c['names'],'certificate':rel(cert),'certificate_sha256':sha(cert),'publication':rel(pub),'publication_sha256':sha(pub),'provider_source':rel(body),'provider_source_sha256':sha(body),'provider_olean':r['provider_olean'],'provider_olean_sha256':r['provider_olean_sha256']})
    return provided,pins,witnesses

def authority(c=None):
    raw=SOURCE.read_bytes();orig=ORIGINAL.read_bytes().replace(b'\r\n',b'\n');am=next(m for m in read(ap9.AST)['modules'] if m['module']==SOURCE_MODULE);sm=next(m for m in read(ap9.SCOPES)['modules'] if m['source']==SOURCE_MODULE.replace('.','/')+'.lean')
    need(am['source_sha256']==sm['source_sha256']==sha(SOURCE)=='fb2547fa5e853f3f9962729dc5f0e5f39d034f13307212886ddd9ae9541ecb66','Original source AST/scope binding differs')
    owners={o['source_name']:o for o in read(ap9.OWNERS)['owners'] if o['source_name'] in NAMES};graph={r['name']:r for r in map(json.loads,ap9.GRAPH.read_text(encoding='utf-8').splitlines())};provided,_,_=bindings();rows=[]
    for name,a,b,first,last in SPECS:
        u=next(u for u in am['units'] if name in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==name);o=owners[name];command=raw[a:b];contexts=[raw[x['range']['start']['offset']:x['range']['end']['offset']].decode() for x in s['context_commands']]
        need(u['start']['offset']==a and u['end']['offset']==b and [u['start']['line'],u['end']['line']]==[first,last] and u['graph_names']==[name] and u['graph_kinds']==['def'] and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance'],'Exact original public Def AST differs')
        need(s['namespace']=='OAI.PiExponent.MatrixArithmetic' and [x['name'] for x in s['scope_stack']]==['OAI','PiExponent','MatrixArithmetic'] and all(x['kind']=='namespace' for x in s['scope_stack']) and contexts==['open scoped BigOperators'],'Original Def namespace or section/instance context differs')
        need(o['source_module']==SOURCE_MODULE and o['source_sha256']==sha(SOURCE) and o['command_unit']==SOURCE_MODULE+':'+str(a) and o['unit_start_offset']==a and o['unit_end_offset']==b and o['graph_kind']=='def' and not o['source_private'],'Original actual CI owner differs')
        need(orig.count(command.replace(b'\r\n',b'\n'))==1 and set(graph[name]['typeDeps']+graph[name]['valueDeps'])<=set(NAMES)|provided,'Original data value/type closure incomplete')
        rows.append({'name':name,'start':a,'end':b,'source_lines':[first,last],'sha256':sha_bytes(command),'bytes':command,'ast':u,'scope':s,'owner':o,'graph':graph[name],'contexts':contexts})
    return rows

def stage_files(key='scalescosts'):
    c=config(key);units=authority(c);provided,pins,witnesses=bindings();coverage=read(COVERAGE)
    need(coverage['audited_definition_count']==28 and coverage['no_requested_definition_CI_provided'] is True and coverage['missing_names']==NAMES,'Frozen actual Published coverage differs')
    for r in coverage['records']:need(sha(TASK/r['publication_record'])==r['publication_record_sha256'],'Actual Published coverage evidence changed')
    body=(''.join('import '+m+'\n' for m in IMPORTS)+'\nnamespace OAI.PiExponent.MatrixArithmetic\n\nopen scoped BigOperators\n\n').encode()+b'\n\n'.join(u['bytes'] for u in units)+b'\n\nend OAI.PiExponent.MatrixArithmetic\n'
    need(b'theorem ' not in body and b'sorry' not in body,'Provider contains proof material')
    outputs={PROVIDER_FILE:body,SOURCE_SNAPSHOT:ap9.snapshot(c,units,False),GENERATED_SNAPSHOT:ap9.snapshot(c,units,True)}
    inputs={rel(p):sha(p) for p in [SELF,Path(ap9.__file__),Path(ap10.__file__),SOURCE,ORIGINAL,ap9.AST,ap9.SCOPES,ap9.GRAPH,ap9.OWNERS,CORE,ap9.RUNTIME,ap9.PREFLIGHT,ap9.CONTEXT,COVERAGE]};inputs.update(pins);inputs.update({r['publication_record']:r['publication_record_sha256'] for r in coverage['records']})
    plans=[(PROVIDER_FILE,IMPORTS,'emit-olean'),(SOURCE_SNAPSHOT,['Lean',SOURCE_MODULE],'modecheck'),(GENERATED_SNAPSHOT,['Lean',PLATFORM_MODULE],'modecheck')];commands=[]
    for i,(f,imports,mode) in enumerate(plans,1):
        outputs[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap15-scales-costs-data-bounded-compiler-manifest','output':workspace_rel(STAGE/f),'output_sha256':sha_bytes(outputs[f]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(ap9.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        commands.append('python scripts/preflight_staged_module.py ap15/scales-costs/'+f+' --root ap15/scales-costs --imports-manifest ap15/scales-costs/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    metadata={'definition_title':'Column and row scales, clearing denominator and logarithmic costs','natural_language_statement':r'Let $q_i$ be natural denominators and let $a,b$ be natural exponent vectors on $m$ coordinates. Put $w_i=\lceil\log q_i\rceil_+$, where the ceiling is natural. Define the column scale, inverse row scale, and common denominator at real height $H$ and natural truncation orders $T_i$ by'+'\n\n'+r'$$C_q(a)=\prod_i q_i^{a_i},\qquad R_q(b)=C_q(b)^{-1},\qquad D(q,T,H)=\prod_i\operatorname{lcm}(1,\ldots,T_i)^{\lfloor H/w_i\rfloor_+}.$$'+'\n\n'+r'For the original finite row domain $\mathcal R=\mathrm{Row}(K,v_0,\theta,w,H)$ and a column selection $\kappa:\mathcal R\to\mathrm{Column}(w_0,w,H)$, define the logarithmic costs'+'\n\n'+r'$$B=\sum_{\rho\in\mathcal R}\sum_i b_{\rho,i}\log q_i,\qquad A_\kappa=\sum_{\rho\in\mathcal R}\sum_i a_{\kappa(\rho),i}\log q_i.$$'+'\n\n'+r'Here $K$ is natural and $w_0,v_0,\theta,H$ are real domain parameters; $b_{\rho,i}$ and $a_{\kappa(\rho),i}$ are the nonconstant coordinates of the row and selected column exponent vectors. All five quantities are real and are defined without positivity assumptions, using the original finite domains. They provide the scaling and cost data for determinant denominator clearing.','source':'OpenAI math, commit '+COMMIT+': https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L135-L209','source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L135-L209','tags':['number-theory','linear-algebra','openai-pi-exponent-017']}
    outputs['academic-metadata.json']=encode(metadata)
    outputs['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap15-scales-costs-data-provider-preparation','source_commit':COMMIT,'source_module':SOURCE_MODULE,'platform_module':PLATFORM_MODULE,'source_path':rel(SOURCE),'source_sha256':sha(SOURCE),'original_source_path':rel(ORIGINAL),'original_source_sha256':sha(ORIGINAL),'provided_names':NAMES,'provider_file':PROVIDER_FILE,'imports':IMPORTS,'exact_source_units':[{k:v for k,v in u.items() if k!='bytes'} for u in units],'source_context_commands':['open scoped BigOperators'],'original_port_definitions_equal_modulo_line_endings':True,'contains_theorems':False,'own_structures_constructors_recursors':[],'snapshot_schema':'lean-4.33.1-ConstantInfo-complete-v1; complete closed Def types/values; no owned Ind/Ctor/Rec declarations','actual_prior_providers':witnesses,'actual_type_value_dependency_boundary_names':sorted(provided),'published_coverage':rel(COVERAGE),'published_coverage_sha256':sha(COVERAGE),'input_hashes':inputs,'order':[x[0] for x in plans],'commands':commands,'expected_provider_olean':rel(V/'staged-build/lib/lean'/Path(PROVIDER_FILE).with_suffix('.olean')),'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False,'proposal_status':'Draft'})
    outputs['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return outputs

def check_only(key='scalescosts'):
    outputs=stage_files(key)
    for f,raw in outputs.items():need((STAGE/f).is_file() and (STAGE/f).read_bytes()==raw,'Immutable new provider changed: '+f)
    for i,f in enumerate([PROVIDER_FILE,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):m=read(STAGE/f'c{i}.json');ap9.runner.verify_manifest_inputs(m);ap9.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(outputs),'provided_names':NAMES,'all_hashes_match':True,'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for f,raw in stage_files().items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
