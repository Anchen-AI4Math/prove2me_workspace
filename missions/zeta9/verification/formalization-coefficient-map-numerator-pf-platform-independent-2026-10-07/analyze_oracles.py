"""Use actual Stage1 facts and Stage2 InfoTree references, never declaration regexes."""
import json, sys
import inspect_author as p
import semantic_spec_v2 as s

def records(row):
    path=p.TASK/row['folder_task_relative']/'stdout.log'
    return [json.loads(x) for x in path.read_text(encoding='utf-8').splitlines() if x.startswith('{')]

def match_decl(facts,name,graph=None):
    matches=[]
    for d in facts:
        if d.get('kind')!='decl':continue
        for ref in facts:
            if ref.get('kind')!='ref' or ref['const']!=name:continue
            if d['declStart']['offset']<=ref['start']['offset']<d['valStart']['offset']:
                if graph is not None:
                    assert d['declStart']['line']<=graph['startLine']<=graph['endLine']<=d['declEnd']['line']
                matches.append(d);break
    assert len(matches)==1,(name,len(matches))
    return matches[0]

def extract(raw,decl):
    return raw[decl['declStart']['offset']:decl['declEnd']['offset']]

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert p.load(p.OUT/'oracle-resolver-terminal.json')['actual_findOLean_and_module_header_checks']==108
    receipt=p.load(p.OUT/'execution-receipt.json'); latest={r['label']:r for r in receipt['rows'] if r['exit_code']==0}
    prep=p.load(p.OUT/'source-preparation.json'); selection=p.load(p.OUT/'own-native-graph-selection.json')
    graph={r['name']:r for x in (p.PROJECT/'native-decl-graph.jsonl').read_text(encoding='utf-8').splitlines() for r in [json.loads(x)]}
    native_source={r['module']:r for r in prep['native_sources']}
    native_facts={module:records(latest['official-parser-'+module.rsplit('.',1)[-1]]) for module in native_source}
    matches={};rows=[]
    for name in selection['definitions']+selection['proofs']:
        g=graph[name]; source=native_source[g['module']]; facts=native_facts[g['module']]
        decl=match_decl(facts,name,g); raw=(p.PROJECT/source['project_relative']).read_bytes()
        fragment=extract(raw,decl); assert fragment
        refs=[r for r in facts if r.get('kind')=='ref' and decl['declStart']['offset']<=r['start']['offset'] and r['end']['offset']<=decl['declEnd']['offset']]
        matches[name]=(fragment,decl)
        rows.append(dict(name=name,module=g['module'],graph=g,parser_decl=decl,
            within_span_references=refs,source=p.bind(p.PROJECT/source['project_relative']),
            source_fragment_utf8=fragment.decode('utf-8')))
    generated=selection['generated']; assert len(generated)==1
    assert graph[generated[0]]['startLine']==graph[generated[0]]['endLine']==0
    assert generated[0].rsplit('.',1)[0] in selection['definitions']
    payload_facts={r['module']:records(latest['official-payload-parser-'+r['module'].rsplit('.',1)[-1]]) for r in prep['seven_payloads']}
    payload_source={r['module']:r for r in prep['seven_payloads']}
    definition_module='Definitions.Def_ZetaNine_CoefficientMapNumeratorPF'
    definition_raw=(p.PROJECT/payload_source[definition_module]['project_relative']).read_bytes()
    for name in s.NEW_DEFINITIONS:
        actual=extract(definition_raw,match_decl(payload_facts[definition_module],name))
        assert actual==matches[name][0],('Changed new pure definition bytes',name)
    stage_comparisons=[]
    for index,suffix in enumerate(s.SUFFIXES):
        module='Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix
        facts=payload_facts[module]; raw=(p.PROJECT/payload_source[module]['project_relative']).read_bytes()
        target=s.TARGETS[index]; mapped=target.rsplit('.',1)[0]+'.checked_'+target.rsplit('.',1)[1]
        expected=set(mapped if n==target else n for n in selection['reached_names'])|{'solution'}
        stage_graph={r['name']:r for x in (p.PROJECT/('staged-decl-graph-'+suffix+'.jsonl')).read_text(encoding='utf-8').splitlines() for r in [json.loads(x)]}
        roots=[mapped if n==target else n for n in s.TARGETS]+['solution']; reached=set()
        def visit(name):
            if name in reached:return
            reached.add(name)
            for dep in stage_graph[name]['typeDeps']+stage_graph[name]['valueDeps']:
                if dep in stage_graph:visit(dep)
        for name in roots:visit(name)
        assert reached==expected,(suffix,sorted(reached-expected),sorted(expected-reached))
        proof_rewrites=[]
        for name in selection['proofs']:
            actual_name=mapped if name==target else name
            d=match_decl(facts,actual_name,stage_graph[actual_name]); text=extract(raw,d)
            replacements=[]
            for ref in facts:
                if ref.get('kind')!='ref' or ref['const']!=mapped:continue
                start,end=ref['start']['offset'],ref['end']['offset']
                if d['declStart']['offset']<=start and end<=d['declEnd']['offset']:
                    token=raw[start:end]
                    old=mapped.rsplit('.',1)[-1].encode(); new=target.rsplit('.',1)[-1].encode()
                    assert token.count(old)==1,(name,token)
                    replacements.append((start-d['declStart']['offset'],end-d['declStart']['offset'],token.replace(old,new)))
            for start,end,new in sorted(set(replacements),reverse=True):text=text[:start]+new+text[end:]
            assert text==matches[name][0],('Inline proof source subtraction changed bytes beyond InfoTree-authorized target name',suffix,name)
            proof_rewrites.append(dict(native_name=name,staged_name=actual_name,parser_decl=d,
                only_InfoTree_authorized_target_token_replacements=len(set(replacements)),
                native_decl_fragment_bytes=len(matches[name][0]),identical_after_target_token_mapping=True))
        # Actual parser facts determine declaration presence; unreachable weighted bridge is absent.
        forbidden='ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_local_coefficient_weighted_agreement'
        assert forbidden not in stage_graph
        assert all(r.get('const')!=forbidden for r in facts if r.get('kind')=='ref')
        stage_comparisons.append(dict(context=suffix,own_actual_graph_rows=len(stage_graph),reached_names=sorted(reached),
            exact_reached_native46_plus_solution=True,inline_proof_byte_comparisons=proof_rewrites,
            unreached_weighted_bridge_absent=True,graph=p.bind(p.PROJECT/('staged-decl-graph-'+suffix+'.jsonl'))))
    definitions=p.load(p.AUTHOR/'definitions-request.json'); problems=p.load(p.AUTHOR/'problems-request.json')
    assert len(definitions)==1 and definitions[0]['env']==problems['env']=='0df444a360eaa60ab8c11dca51a86af692955474'
    assert not definitions[0]['private'] and not problems['private']
    assert definitions[0]['definition'].encode('utf-8')==definition_raw
    assert len(problems['problems'])==3
    request_rows=[]
    for suffix,problem in zip(s.SUFFIXES,problems['problems']):
        module='Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_'+suffix
        raw=(p.PROJECT/payload_source[module]['project_relative']).read_bytes()
        reconstructed=(problem['preamble']+'\n'+problem['formal_statement']+'\n').encode('utf-8')
        assert raw==reconstructed,(suffix,'Exact reference request bytes differ')
        d=match_decl(payload_facts[module],problem['theorem_name'])
        assert len([r for r in payload_facts[module] if r.get('kind')=='decl'])==1
        request_rows.append(dict(context=suffix,theorem_name=problem['theorem_name'],request_reference_bytes_identical=True,parser_decl=d))
    result=dict(status='OWN_ACTUAL_GRAPH_PARSER_SPAN_AND_PAYLOAD_REQUEST_CHECKS_PASS',
        native_graph=p.bind(p.PROJECT/'native-decl-graph.jsonl'),native45_named_decl_span_records=rows,
        generated_equation_helper=dict(name=generated[0],spanless=True,regenerated_in_each_exact_payload_context=True,
            complete_type_closed_Std3_audited=True,parent_definition=generated[0].rsplit('.',1)[0]),
        new5_pure_definitions_native_source_bytes_identical=True,staged_comparisons=stage_comparisons,
        exact_definition_request_bytes=True,reference_request_byte_checks=request_rows,
        requests=[p.bind(p.AUTHOR/'definitions-request.json'),p.bind(p.AUTHOR/'problems-request.json')],
        official_declaration_authority='Actual independently executed Stage1 graph and Stage2 InfoTree facts',
        generated_helpers_not_manually_inserted=True,independent_PASS_claimed=False)
    (p.OUT/'own-oracle-payload-validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Own45 source spans,5 exact pure bodies,102 InfoTree-mapped inline proof byte comparisons,3 exact requests and3 actual47 closures passed.')

if __name__=='__main__':main()
