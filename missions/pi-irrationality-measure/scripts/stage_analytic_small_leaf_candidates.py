"""Pure source-only four small analytic leaf closures; no final compiler/API evidence claimed."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_literal_analytic_interface_data_provider as data
import stage_analytic_translated_graph_route as route

TASK,V,SELF=data.TASK,data.V,Path(__file__).resolve()
STAGE=V/'ap20/analytic-small-leaf-candidates'
TARGETS=[route.LITERAL+n for n in ['indexWeight_nonneg','actualRowCount_pos','sum_rowWeight_eq','card_choiceFamily_le']]
PUB=data.STAGE/'publication/publication.json'
ADAPTED={route.LITERAL+'card_choiceFamily_le','OAI.PiExponent.RowTranslation.card_bounded_indices_le'}
read,sha,digest,encode,need,rel=data.read,data.sha,data.sha_bytes,data.encode,data.need,data.rel

def outputs():
    route_report=read(route.STAGE/'report.json');cert=read(data.CERTIFICATE);pub=read(PUB);body=pub['target_readback']['body']
    need(cert['validated'] and cert['Std3_only'] and body['status']=='Definition'
         and pub['definition_id']==body['theorem_id']==pub['last_publish_verdict']['body']['theorem_id']=='20a36293-ad9b-41de-b2a1-463e0f7f0094'
         and body['definition'].encode()==(data.STAGE/data.PROVIDER_FILE).read_bytes(),'Genuine17Def Published gate differs')
    graph={r['name']:r for r in map(json.loads,data.base.base.GRAPH.read_text(encoding='utf-8').splitlines())}
    ast=read(data.base.base.AST);scopes=read(data.base.base.SCOPES);provided=set(data.NAMES)
    pins={rel(p):sha(p) for p in [SELF,route.STAGE/'report.json',route.BASELINE,data.CERTIFICATE,PUB,data.STAGE/data.PROVIDER_FILE,data.base.base.GRAPH,data.base.base.AST,data.base.base.SCOPES,data.base.base.OWNERS]}
    for r in route_report['actual_Published31_coverage']:
        need(sha(TASK/r['publication_record'])==r['publication_record_sha256'],'Actual prior31 record changed')
        pins[r['publication_record']]=r['publication_record_sha256'];provided.update(r['actual_source_graph_names'])
    result={};reports=[]
    for target in TARGETS:
        todo=[target];reached=set()
        while todo:
            n=todo.pop()
            if n in reached or n in provided:continue
            reached.add(n);todo+=graph[n]['typeDeps']+graph[n]['valueDeps']
        need(all(graph[n]['kind']=='theorem' for n in reached),'Unexpected missing data closure')
        ordered=[];pending=set(reached)
        while pending:
            ready=sorted(n for n in pending if not(set(graph[n]['typeDeps']+graph[n]['valueDeps'])&pending));need(ready,'Unexpected recursive leaf proof closure')
            ordered+=ready;pending-=set(ready)
        need(ordered[-1]==target,'Leaf was not closure terminal')
        units=[];folder=target.rsplit('.',1)[1]
        for n in ordered:
            m=next(m for m in ast['modules'] if m['module']==graph[n]['module']);u=next(u for u in m['units'] if n in u['graph_names'])
            path=TASK/('port/lean/'+m['module'].replace('.','/')+'.lean');orig=TASK/('source/lean/'+m['module'].replace('.','/')+'.lean')
            raw=path.read_bytes();a,b=u['start']['offset'],u['end']['offset'];command=raw[a:b];normalized=command.replace(b'\r\n',b'\n');adaptation=None
            if n in ADAPTED:
                need(normalized.count(b"Finset.prod_le_prod'")==1,'Expected exact finite product adapter differs')
                normalized=normalized.replace(b"Finset.prod_le_prod'",b'Finset.prod_le_prod')
                adaptation={'original':'Finset.prod_le_prod','port':"Finset.prod_le_prod'",'count':1}
            sm=next(s for s in scopes['modules'] if s['source']==m['module'].replace('.','/')+'.lean');scope=next(s for s in sm['declarations'] if s['verified_name']==n)
            need(sha(path)==m['source_sha256']==sm['source_sha256'] and u['graph_names']==[n] and u['graph_kinds']==['theorem']
                 and u['privateTok'] is None and orig.read_bytes().replace(b'\r\n',b'\n').count(normalized)==1,'Exact original source theorem AST differs: '+n)
            contexts=[raw[c['range']['start']['offset']:c['range']['end']['offset']].decode() for c in scope['context_commands']]
            row={'name':n,'source_module':m['module'],'source':rel(path),'source_sha256':sha(path),'original':rel(orig),'original_sha256':sha(orig),
              'start':a,'end':b,'source_lines':[u['start']['line'],u['end']['line']],'command_sha256':digest(command),
              'original_normalized_command_sha256':digest(normalized),'ast':u,'scope':scope,'contexts':contexts,'graph':graph[n],
              'finite_source_port_version_adaptation':adaptation,'command':command}
            units.append(row);pins[rel(path)]=sha(path);pins[rel(orig)]=sha(orig)
            result[folder+'/port-source-units/'+n.replace('.','_')+'.lean.txt']=command
            result[folder+'/original-source-units/'+n.replace('.','_')+'.lean.txt']=normalized
        imports=[data.PLATFORM_MODULE]
        preamble=(''.join('import '+m+'\n' for m in imports)+'\nopen scoped BigOperators Topology\nopen Filter\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic\n\n').encode()
        sol=preamble
        for r in units[:-1]:
            ns=r['scope']['namespace'];sol+=('\nnamespace '+ns+'\n\n'+'\n'.join(r['contexts'])+'\n\n').encode()+r['command']+('\n\nend '+ns+'\n').encode()
        r=units[-1];a=r['ast']['nameRange']['start']['offset']-r['start'];b=r['ast']['nameRange']['end']['offset']-r['start'];v=r['ast']['valueStart']['offset']-r['start']
        renamed=r['command'][:a]+b'solution'+r['command'][b:]
        need(renamed[renamed.index(b':='):]==r['command'][v:],'Target source proof suffix changed beyond binding name')
        sol+=renamed+b'\n';formal=r['command'][:a]+target.encode()+r['command'][b:v]+b':= by\n  sorry\n'
        result[folder+'/candidate/Solutions/Sol_'+target.replace('.','_')+'_small_leaf_ap20.lean']=sol
        result[folder+'/candidate/'+route.module(target).replace('.','/')+'.lean']=preamble+formal
        report={'target':target,'proof_AST_count':len(units),'source_line_count':sum(r['source_lines'][1]-r['source_lines'][0]+1 for r in units),
          'helper_names':ordered[:-1],'closure_order':ordered,'missing_data_names':[],'uses_unProved_platform_boundaries':False,
          'imports':imports,'all_helpers_original_AST_inline':True,'target_source_proof_suffix_unchanged_except_solution_name':True,
          'source_units':[{k:v for k,v in r.items() if k!='command'} for r in units],
          'finite_port_adaptations':[{'name':r['name'],**r['finite_source_port_version_adaptation']} for r in units if r['finite_source_port_version_adaptation']],
          'pending_gate':'Actual two-layer graph publication exact target ID/wire; then source/gen fulltypes/refs/Std3 and four bounded contexts',
          'candidate_comparator_is_not_published_wire':True,'validated':False,'closed_proof_verified':False,'Lean_started':False,'API_used':False}
        result[folder+'/source-route.json']=encode(report);reports.append(report)
    result['report.json']=encode({'schema_version':1,'artifact_kind':'ap20-four-small-analytic-leaf-source-only-candidates','source_commit':data.COMMIT,
      'data_definition_id':pub['definition_id'],'data_certificate_sha256':sha(data.CERTIFICATE),'data_publication_sha256':sha(PUB),
      'data_coverage':'literal actual Published31 source-name coverage plus genuine new17Def source names',
      'prioritized_targets':TARGETS,'routes':reports,'input_hashes':pins,'validated':False,'Lean_started':False,'API_used':False})
    result['report.md']=('# Four small original analytic leaf candidates\n\n'+
      '\n'.join('- `'+r['target']+'`: '+str(r['proof_AST_count'])+' original proof ASTs / '+str(r['source_line_count'])+' lines; no missing data and no unProved theorem boundary.' for r in reports)+
      '\n\nStart with indexWeight_nonneg (3 ASTs / 12 lines), then actualRowCount_pos (7 / 53). Sum-row-weight can reuse a future certified public actual-row-count theorem to shorten its proof closure. Card-choice needs 16 / 138 and has two exact existing product API adaptations, on card_choiceFamily_le and RowTranslation.card_bounded_indices_le. All original and port commands, scopes, hashes and source commit are recorded.\n\nThese are source-only candidates. The candidate comparator preamble is not asserted equal to a published wire. Final standalone nodes wait for actual graph publication/readback, then require real bounded compilation and source/generated kernel type/ref/Std3 certification.\n').encode()
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();files=outputs()
    for f,raw in files.items():
        path=STAGE/f
        if path.exists():need(path.read_bytes()==raw,'Refusing changed pure candidate: '+f)
        elif a.prepare:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        else:need(False,'Missing pure candidate: '+f)
    print(json.dumps({'files':len(files),'routes':4,'validated':False,'Lean_started':False,'API_used':False},indent=2))
if __name__=='__main__':main()
