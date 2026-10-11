"""Actual-oracle driven, serial NumeratorPF platform AUTHOR continuation.

This file is added after the immutable 80-file preparation. No import-time Lean.
Only own pa1 objects and shared fixed Mathlib packages are used.
"""
import argparse, json, sys
sys.dont_write_bytecode = True
import prepare as p
import execute_oracles as e

OUT,TASK,ROOT,PROJECT,NS = p.OUT,p.TASK,p.ROOT,p.PROJECT,p.NS
DATA='missions.zeta9.formalization.CoefficientMapFormalTransportData'
DEF_PATH='Definitions/Def_ZetaNine_CoefficientMapNumeratorPF.lean'
DEF_MODULE=DEF_PATH[:-5].replace('/','.')

def edit(data, changes):
    edge=len(data)
    for a,b,v in sorted(set(changes),reverse=True):
        assert 0<=a<=b<=edge, (a,b,edge)
        data=data[:a]+v+data[b:];edge=a
    return data

def save_leaf(label,text):
    p.write(OUT/(label+'.lean'),text);p.write(PROJECT/(label+'.lean'),text)

def compile_module(label,module):
    obj='b/lib/lean/'+module.replace('.','/')+'.olean'
    (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    e.run(label,['-o',obj,module.replace('.','/')+'.lean'])

def context():
    state=e.gate();receipt=p.load(OUT/'compile-receipt.json')
    latest={r['label']:r for r in receipt['rows']}
    assert all(latest[k]['exit_code']==0 for k in ['stage1-extract','stage2-header']+
        ['stage2-'+r['parser_name'] for r in state['native_sources']])
    graph=e.rows(OUT/'decl_graph.jsonl');byname={r['name']:r for r in graph}
    assert len(graph)==545 and not any(r['kind']=='axiom' for r in graph)
    sources={r['module']:(OUT/(r['parser_name']+'-oracle-input.lean')).read_bytes() for r in state['native_sources']}
    facts={r['module']:e.rows(OUT/(r['parser_name']+'-sketch_info.jsonl')) for r in state['native_sources']}
    normalization=[]
    for r in state['native_sources']:
        raw=(PROJECT/r['project_relative']).read_bytes();oracle=sources[r['module']]
        assert oracle==raw.replace(b'\r\n',b'\n')
        normalization.append(dict(module=r['module'],raw=p.binding(PROJECT/r['project_relative']),
            parser_input=p.binding(OUT/(r['parser_name']+'-oracle-input.lean')),only_CRLF_to_LF=True))
    p.dump(OUT/'parser-input-normalization.json',dict(records=normalization,
        source_position_authority='Actual persisted Stage2 input bytes'))
    reached=set();work=[NS+'.'+n for n in p.TARGETS]+[r['name'] for r in graph if r['isInstance']]
    while work:
        n=work.pop()
        if n in reached:continue
        reached.add(n);work.extend(byname[n]['typeDeps']+byname[n]['valueDeps'])
    spanful=sorted([byname[n] for n in reached if byname[n]['startLine']>0],key=lambda r:(r['module'],r['startLine']))
    proofs=[r for r in spanful if r['kind']=='theorem'];defs=[r for r in spanful if r['kind']=='def']
    assert len(spanful)==45 and len(proofs)==34 and len(defs)==11
    ownproofs=[r for r in proofs if r['module']==p.NATIVE]
    helpers=[r for r in proofs if r['module']!=p.NATIVE]
    newdefs=[r for r in defs if r['module'] in [p.NATIVE,DATA]]
    assert len(ownproofs)==18 and len(helpers)==16 and len(newdefs)==5
    def declaration(name):
        r=byname[name];found=[f for f in facts[r['module']] if f['kind']=='decl' and
            f['declStart']['line']<=r['startLine']<=f['declEnd']['line']]
        assert len(found)==1 and found[0]['valStart'] is not None
        return found[0]
    core=[r for r in graph if r['module']==p.NATIVE and r['startLine']>0]
    assert len(core)==27
    return dict(state=state,graph=graph,byname=byname,sources=sources,facts=facts,reached=reached,
        spanful=spanful,proofs=proofs,defs=defs,newdefs=newdefs,ownproofs=ownproofs,helpers=helpers,
        core=core,declaration=declaration)

def headers():
    c=context()
    modules=list(dict.fromkeys([r['module'] for r in c['helpers']]+[DATA]))
    for module in modules:
        parser=next(r['parser_name'] for r in c['state']['native_sources'] if r['module']==module)
        label='header-'+parser
        e.run(label,['--run','extract_header.lean',module.replace('.','/')+'.lean'],output=label+'.jsonl')
    print('Five extra real header calls completed.',flush=True)

def skeleton(c,module,keep,rename=None):
    source=c['sources'][module];facts=c['facts'][module]
    hfile=OUT/'header_info.jsonl' if module==p.NATIVE else OUT/('header-'+module.rsplit('.',1)[1]+'.jsonl')
    header=e.rows(hfile)[0];assert header['start']['offset']==0
    kept={c['declaration'](n)['declStart']['offset'] for n in keep}
    cuts=[(0,header['end']['offset'],b'')]
    cuts += [(f['declStart']['offset'],f['declEnd']['offset'],b'') for f in facts if
        f['kind']=='decl' and f['declStart']['offset'] not in kept]
    edits=[]
    for f in facts:
        if f['kind']!='command':continue
        if f['syntaxKind'] in ['Lean.Parser.Command.printAxioms','Lean.Parser.Command.moduleDoc']:
            cuts.append((f['span']['start']['offset'],f['span']['end']['offset'],b''))
        if module==DATA and f['syntaxKind']=='Lean.Parser.Command.open':
            a,b=f['span']['start']['offset'],f['span']['end']['offset']
            if b'CoefficientMapConnection' in source[a:b]:
                edits.append((a,b,b'open CoefficientMapJet CoefficientMapInjectivity'))
    if rename:
        for f in facts:
            if f['kind']=='ref' and f['const'] in rename:
                a,b=f['start']['offset'],f['end']['offset']
                if any(x<=a and b<=y for x,y,_ in cuts):continue
                spelling=source[a:b].decode();old=f['const'];new=rename[old]
                assert spelling in [old,old.rsplit('.',1)[1]]
                edits.append((a,b,(new if spelling==old else new.rsplit('.',1)[1]).encode()))
    return edit(source,cuts+edits).decode(),dict(module=module,header=header,
        retained_names=sorted(keep),cuts=[(a,b) for a,b,_ in cuts],
        context_and_rename_edits=[(a,b,v.decode()) for a,b,v in edits])

def prepare_stage():
    c=context();defs=[r['name'] for r in c['newdefs']]
    ownproofnames={r['name'] for r in c['proofs']}
    assert all(not set(c['byname'][n]['typeDeps']+c['byname'][n]['valueDeps'])&ownproofnames for n in defs)
    existing=[r['module'] for r in c['state']['parent_definitions']]
    prefix=''.join('import '+m+'\n' for m in existing)+'import Mathlib.Data.Matrix.Basic\nimport Mathlib.Tactic\n\n'
    chunks=[];records=[]
    for module in [DATA,p.NATIVE]:
        chunk,record=skeleton(c,module,{n for n in defs if c['byname'][n]['module']==module})
        chunks.append(chunk);records.append(record)
    definition=prefix+'\n'.join(chunks)
    p.write(OUT/'staged'/DEF_PATH,definition);p.write(PROJECT/DEF_PATH,definition)
    bridge=[]
    for module in list(dict.fromkeys(r['module'] for r in c['helpers'])):
        chunk,record=skeleton(c,module,{r['name'] for r in c['helpers'] if r['module']==module})
        bridge.append(chunk);records.append(record)
    bridge='\n'.join(bridge);p.write(OUT/'actual-proof-bridge.lean.inc',bridge)
    targets=[];target_records=[];problems=[]
    for name,suffix,args in zip(p.TARGETS,p.SUFFIXES,p.ARGS):
        full=NS+'.'+name;checked=NS+'.checked_'+name;fact=c['declaration'](full)
        refs=[f for f in c['facts'][p.NATIVE] if f['kind']=='ref' and f['const']==full and
            fact['declStart']['offset']<=f['start']['offset']<fact['valStart']['offset']]
        assert len(refs)==1;binding=refs[0]
        bs,be=binding['start']['offset'],binding['end']['offset'];a,v=fact['declStart']['offset'],fact['valStart']['offset']
        signature=c['sources'][p.NATIVE][be:v].decode()
        body,record=skeleton(c,p.NATIVE,{r['name'] for r in c['ownproofs']},{full:checked})
        solprefix='import '+DEF_MODULE+'\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 3000000\n\n'
        opens='open scoped BigOperators\nopen Finset Polynomial ZetaNine '+NS+' ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\n'
        solution=solprefix+bridge+'\n'+body+'\n'+opens+'\ntheorem solution'+signature+':= by\n  exact '+checked+' '+args+'\n\n#print axioms solution\n'
        changes=[(bs-a,be-a,full.encode())]
        if fact['docstring']:
            ds=fact['docstring'];changes.append((ds['start']['offset']-a,ds['end']['offset']-a,b''))
        formal=edit(c['sources'][p.NATIVE][a:v],changes).decode().strip()+':= by sorry'
        refprefix='import '+DEF_MODULE+'\n\nset_option autoImplicit false\n'+opens
        solpath='Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix+'.lean'
        refpath='Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_'+suffix+'.lean'
        for path,text in [(solpath,solution),(refpath,refprefix+'\n'+formal+'\n')]:
            p.write(OUT/'staged'/path,text);p.write(PROJECT/path,text)
        targets.append(dict(theorem_name=full,local_solution=solpath,local_reference=refpath,wrapper_arguments=args))
        target_records.append(dict(target=full,actual_declaration_fact=fact,actual_binding_fact=binding,
            original_signature=signature,rename_skeleton=record,extra_hypotheses=[]))
        problems.append(dict(theorem_name=full,theorem_title='Actual numerator '+suffix+' partial fractions',
            formal_statement=formal,preamble=refprefix,natural_language_statement=[
            'For every natural m and rational polynomial A of degree less than 9(m+1), the polynomial numerator reconstructed from its actual first nine local jets equals A.',
            'For every natural m and rational polynomial A of degree less than 9(m+1), its rational function has the full actual jet partial fraction expansion at every rational regular point t.',
            'For every natural m and two rational polynomials of degree less than 9(m+1), equality of all actual local coefficients at poles j<=m and orders 1..9 implies equality of the polynomials.'][p.SUFFIXES.index(suffix)],
            source='Frozen actual native source SHA256 '+p.SOURCE_SHA,tags=['number-theory','formalization']))
    excluded=[dict(r,reason='Not reachable from the three complete generic endpoints or an instance root') for r in c['core'] if r['name'] not in c['reached']]
    p.dump(OUT/'integration-provenance.json',dict(role='Platform AUTHOR; separate independent review required',
        source_sha256=p.SOURCE_SHA,graph_records=545,actual_instance_roots=0,roots=[NS+'.'+n for n in p.TARGETS],
        reached_names=sorted(c['reached']),spanful_reached_records=c['spanful'],new_definition_names=defs,
        parent_helper_names=[r['name'] for r in c['helpers']],PF_proof_names=[r['name'] for r in c['ownproofs']],
        excluded_native_PF_declarations=excluded,excluded_other_Data_declarations=[f for f in c['facts'][DATA] if f['kind']=='decl' and
            f['declStart']['offset'] not in {c['declaration'](n)['declStart']['offset'] for n in defs if c['byname'][n]['module']==DATA}],
        skeletons=records,target_skeletons=target_records,proof_records_per_solution=35,
        proof_source_closure_inlined=True,source_stub_imports=[],abstract_PF_assumptions=[],
        genuine_native_author_provenance='This agent authored the native PF module; native independent review is a different agent.'))
    p.dump(OUT/'target-plan.json',dict(definition='ZetaNine_CoefficientMapNumeratorPF',local_definition=DEF_PATH,
        targets=targets,existing_definitions=c['state']['parent_definitions']))
    p.dump(OUT/'definitions-request.json',[dict(definition_name='ZetaNine_CoefficientMapNumeratorPF',definition_title='Actual arbitrary numerator jets and reconstruction',
        definition=definition,natural_language_statement='Five actual pure definitions: cleared local power series, their local coefficients, truncation, partial blocks and reconstructed numerator. No abstract coefficient or PF existence assumption.',
        source='Frozen actual native source SHA256 '+p.SOURCE_SHA,tags=['number-theory','formalization'],env=p.REV,private=False)])
    p.dump(OUT/'problems-request.json',dict(env=p.REV,private=False,problems=problems))
    print('Prepared actual skeletons: 5 new pure definitions, 18 PF + 16 parent proofs, 35 proofs per Solution.',flush=True)

def stage():
    prepare_stage();compile_module('build-definition',DEF_MODULE)
    for i,row in enumerate(p.load(OUT/'target-plan.json')['targets']):
        for kind in ['solution','reference']:
            compile_module('build-'+str(i)+'-'+kind,row['local_'+kind][:-5].replace('/','.'))

def main():
    sys.stdout.reconfigure(encoding='utf-8');q=argparse.ArgumentParser()
    q.add_argument('phase',choices=['headers','prepare','stage']);q.add_argument('--lane-granted',action='store_true');a=q.parse_args()
    if a.phase=='prepare':prepare_stage();return
    assert a.lane_granted and not (OUT/'author-audit.json').exists()
    if a.phase=='headers':headers()
    else:stage()

if __name__=='__main__':main()
