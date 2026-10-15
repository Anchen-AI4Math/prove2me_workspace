"""Pure AP14 staging of three original RowTranslation data definitions."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import stage_weighted_simplex_domains_providers as ap9

TASK,ROOT,V=ap9.TASK,ap9.ROOT,ap9.V
SELF=Path(__file__).resolve()
STAGE=V/'ap14/row-data'
COMMIT=ap9.COMMIT
SOURCE_MODULE='OAI.NumberTheory.PiExponent.Approximation.RowTranslation'
PLATFORM_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData'
PROVIDER_FILE=PLATFORM_MODULE.replace('.','/')+'.lean'
SOURCE=TASK/('port/lean/'+SOURCE_MODULE.replace('.','/')+'.lean')
ORIGINAL=TASK/('source/lean/'+SOURCE_MODULE.replace('.','/')+'.lean')
CORE=ap9.CORE
COVERAGE=V/'ap14/published27-row-translation-coverage.json'
IMPORTS=['Mathlib.Algebra.MvPolynomial.Eval','Mathlib.Algebra.Order.Antidiag.FinsuppEquiv']
NAMES=['OAI.PiExponent.RowTranslation.shift','OAI.PiExponent.RowTranslation.shiftCoefficient','OAI.PiExponent.RowTranslation.multiIndex']
SPECS=[(NAMES[0],222,348,13,14),(NAMES[1],1019,1135,33,34),(NAMES[2],2296,2392,68,68)]
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT=ap9.SOURCE_SNAPSHOT,ap9.GENERATED_SNAPSHOT
SOURCE_JSON,GENERATED_JSON=ap9.SOURCE_JSON,ap9.GENERATED_JSON
CONFIGS=['rowtranslation']
read,encode,sha,sha_bytes,need,rel,workspace_rel=ap9.read,ap9.encode,ap9.sha,ap9.sha_bytes,ap9.need,ap9.rel,ap9.workspace_rel

def config(key='rowtranslation'):
    need(key=='rowtranslation','Unknown provider key')
    return {'stage':STAGE,'source_module':SOURCE_MODULE,'platform_module':PLATFORM_MODULE,'provider_file':PROVIDER_FILE,'names':NAMES,'source':SOURCE,'original':ORIGINAL,'imports':IMPORTS}

def authority(c=None):
    raw=SOURCE.read_bytes();original=ORIGINAL.read_bytes().replace(b'\r\n',b'\n')
    am=next(x for x in read(ap9.AST)['modules'] if x['module']==SOURCE_MODULE);sm=next(x for x in read(ap9.SCOPES)['modules'] if x['source']==SOURCE_MODULE.replace('.','/')+'.lean')
    need(am['source_sha256']==sm['source_sha256']==sha(SOURCE),'Actual source AST/scope hashes differ')
    owners={x['source_name']:x for x in read(ap9.OWNERS)['owners'] if x['source_name'] in NAMES};graph={x['name']:x for x in map(json.loads,ap9.GRAPH.read_text(encoding='utf-8').splitlines())};units=[]
    for name,a,b,first,last in SPECS:
        u=next(u for u in am['units'] if name in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==name);o=owners[name];command=raw[a:b];contexts=[raw[x['range']['start']['offset']:x['range']['end']['offset']].decode() for x in s['context_commands']]
        section='FiniteExpansion' if name==NAMES[2] else 'PolynomialShift';var='variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]' if name==NAMES[2] else 'variable {σ R : Type*} [CommSemiring R]'
        need(u['start']['offset']==a and u['end']['offset']==b and u['start']['line']==first and u['end']['line']==last and u['graph_names']==[name] and u['graph_kinds']==['def'] and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance'],'Exact source data AST differs')
        need(s['namespace']=='OAI.PiExponent.RowTranslation' and [x['kind'] for x in s['scope_stack']]==['namespace','namespace','namespace','section'] and s['scope_stack'][-1]['name']==section and contexts==['open scoped BigOperators','open MvPolynomial',var],'Original generic section/instance context differs')
        need(o['source_module']==SOURCE_MODULE and o['source_sha256']==sha(SOURCE) and o['command_unit']==SOURCE_MODULE+':'+str(a) and o['unit_start_offset']==a and o['unit_end_offset']==b and o['graph_kind']=='def' and not o['source_private'],'Complete original CI owner differs')
        need(original.count(command.replace(b'\r\n',b'\n'))==1 and graph[name]['typeDeps']==[] and set(graph[name]['valueDeps'])<=set(NAMES),'Original data body or dependency closure differs')
        units.append({'name':name,'start':a,'end':b,'source_lines':[first,last],'sha256':sha_bytes(command),'bytes':command,'ast':u,'scope':s,'owner':o,'graph':graph[name],'contexts':contexts})
    return units

def stage_files(key='rowtranslation'):
    c=config(key);units=authority(c);coverage=read(COVERAGE)
    need(coverage['audited_definition_count']==27 and coverage['none_provided'] is True and not any(x['mentions_RowTranslation'] for x in coverage['records']),'Actual Published27 coverage changed')
    for r in coverage['records']:need(sha(TASK/r['publication_record'])==r['publication_record_sha256'],'Published body evidence changed')
    body=(''.join('import '+m+'\n' for m in IMPORTS)+'\nnamespace OAI\n\nnamespace PiExponent.RowTranslation\n\nopen scoped BigOperators\nopen MvPolynomial\n\nsection PolynomialShift\nvariable {σ R : Type*} [CommSemiring R]\n\n').encode()+units[0]['bytes']+b'\n\n'+units[1]['bytes']+'\n\nend PolynomialShift\n\nsection FiniteExpansion\nvariable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]\n\n'.encode()+units[2]['bytes']+b'\n\nend FiniteExpansion\n\nend PiExponent.RowTranslation\n\nend OAI\n'
    need(b'theorem ' not in body and b'sorry' not in body,'Provider contains a proof lemma or sorry')
    outputs={PROVIDER_FILE:body,SOURCE_SNAPSHOT:ap9.snapshot(c,units,False),GENERATED_SNAPSHOT:ap9.snapshot(c,units,True)}
    inputs={rel(p):sha(p) for p in [SELF,Path(ap9.__file__),SOURCE,ORIGINAL,ap9.AST,ap9.SCOPES,ap9.GRAPH,ap9.OWNERS,CORE,ap9.RUNTIME,ap9.PREFLIGHT,ap9.CONTEXT,COVERAGE]};inputs.update({r['publication_record']:r['publication_record_sha256'] for r in coverage['records']})
    plans=[(PROVIDER_FILE,IMPORTS,'emit-olean'),(SOURCE_SNAPSHOT,['Lean',SOURCE_MODULE],'modecheck'),(GENERATED_SNAPSHOT,['Lean',PLATFORM_MODULE],'modecheck')];commands=[]
    for i,(f,imports,mode) in enumerate(plans,1):
        outputs[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap14-row-translation-data-bounded-compiler-manifest','output':workspace_rel(STAGE/f),'output_sha256':sha_bytes(outputs[f]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(ap9.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        commands.append('python scripts/preflight_staged_module.py ap14/row-data/'+f+' --root ap14/row-data --imports-manifest ap14/row-data/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    metadata={'definition_title':'Polynomial translation and finite multi-index data','natural_language_statement':r'Let $R$ be a commutative semiring and $\sigma$ an index type. For $c:\sigma\to R$, define the polynomial translation homomorphism and its monomial coefficient by'+'\n\n'+r'$$\tau_c(X_i)=X_i+c_i,\qquad S_c(\beta,a)=[X^\beta]\tau_c(X^a).$$'+'\n\n'+r'Here $a,\beta:\sigma\to_0\mathbb N$ are finitely supported exponent vectors. When $\sigma$ is finite, the finite multi-index map converts $a:\sigma\to\mathbb N$ to the same vector viewed as a finitely supported function. These are the original data used to expand shifted interpolation polynomials.','source':'OpenAI math, commit '+COMMIT+': https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/RowTranslation.lean#L13-L68','source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/RowTranslation.lean#L13-L68','tags':['polynomial','linear-algebra','number-theory','openai-pi-exponent-017']}
    outputs['academic-metadata.json']=encode(metadata)
    outputs['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap14-row-translation-data-provider-preparation','source_commit':COMMIT,'source_module':SOURCE_MODULE,'platform_module':PLATFORM_MODULE,'source_path':rel(SOURCE),'source_sha256':sha(SOURCE),'original_source_path':rel(ORIGINAL),'original_source_sha256':sha(ORIGINAL),'provided_names':NAMES,'provider_file':PROVIDER_FILE,'imports':IMPORTS,'exact_source_units':[{k:v for k,v in u.items() if k!='bytes'} for u in units],'source_context_commands':['open scoped BigOperators','open MvPolynomial','section PolynomialShift; variable {σ R : Type*} [CommSemiring R]','section FiniteExpansion; variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]'],'section_instances_restored_exactly':True,'contains_theorems':False,'own_structures_constructors_recursors':[],'snapshot_schema':'lean-4.33.1-ConstantInfo-complete-v1; complete closed Def types/values; no owned Ind/Ctor/Rec declarations','published_coverage':rel(COVERAGE),'published_coverage_sha256':sha(COVERAGE),'input_hashes':inputs,'order':[x[0] for x in plans],'commands':commands,'expected_provider_olean':rel(ap9.V/'staged-build/lib/lean'/Path(PROVIDER_FILE).with_suffix('.olean')),'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False,'proposal_status':'Draft'})
    outputs['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return outputs

def check_only(key='rowtranslation'):
    outputs=stage_files(key)
    for f,raw in outputs.items():need((STAGE/f).is_file() and (STAGE/f).read_bytes()==raw,'Immutable provider changed: '+f)
    for i,f in enumerate([PROVIDER_FILE,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):
        m=read(STAGE/f'c{i}.json');import preflight_staged_module as runner;runner.verify_manifest_inputs(m);runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(outputs),'provided_names':NAMES,'all_hashes_match':True,'Lean_started':False,'API_used':False,'validated':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);m=p.add_mutually_exclusive_group(required=True);m.add_argument('--prepare',action='store_true');m.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for f,raw in stage_files().items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
