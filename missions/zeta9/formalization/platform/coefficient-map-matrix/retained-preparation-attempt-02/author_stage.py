"""Matrix stage/audit continuation driven exclusively by completed real oracles.

No import-time execution. Reuses the immutable actual-call recorder, not any
proof objects from another project. Each Lean phase needs the existing lane.
"""
from pathlib import Path
import argparse, json, sys
import prepare as p
import execute_oracles as e

OUT,TASK,ROOT,PROJECT,NS = p.OUT,p.TASK,p.ROOT,p.PROJECT,p.NS
DEF_PATH='Definitions/Def_ZetaNine_CoefficientMapMatrix.lean'
ALIAS_NS=NS+'ValueComparison'


def edit(data, changes):
    edge=len(data)
    for a,b,value in sorted(set(changes),reverse=True):
        assert 0<=a<=b<=edge
        data=data[:a]+value+data[b:];edge=a
    return data


def context():
    state=e.gate()
    receipt=p.load(OUT/'compile-receipt.json');latest={r['label']:r for r in receipt['rows']}
    assert all(label in latest and latest[label]['exit_code']==0 for label in
        ['stage1-extract','stage2-header']+['stage2-'+r['parser_name'] for r in state['native_sources']])
    graph=e.rows(OUT/'decl_graph.jsonl');byname={r['name']:r for r in graph}
    sources={r['module']:(OUT/(r['parser_name']+'-oracle-input.lean')).read_bytes() for r in state['native_sources']}
    facts={r['module']:e.rows(OUT/(r['parser_name']+'-sketch_info.jsonl')) for r in state['native_sources']}
    normalization=[]
    for row in state['native_sources']:
        raw=(PROJECT/row['project_relative']).read_bytes()
        oracle=sources[row['module']]
        assert oracle==raw.replace(b'\r\n',b'\n')
        normalization.append(dict(module=row['module'],raw_source_binding=p.binding(PROJECT/row['project_relative']),
            actual_oracle_input_binding=p.binding(OUT/(row['parser_name']+'-oracle-input.lean')),
            identical_bytes=oracle==raw,only_CRLF_to_LF=True,
            source_position_authority='actual persisted parser input, not raw CRLF offsets'))
    p.dump(OUT/'parser-input-normalization.json',dict(records=normalization,
        actual_parser_inputs_are_position_authority=True,raw_frozen_native_sources_unchanged=True))
    core=sorted([r for r in graph if r['module']==p.NATIVE and r['startLine']>0],key=lambda r:r['startLine'])
    assert len(core)==22 and sum(r['kind']=='def' for r in core)==5 and sum(r['kind']=='theorem' for r in core)==17
    assert not any(r['kind']=='axiom' for r in graph)
    def declaration(name):
        row=byname[name];fs=facts[row['module']]
        found=[f for f in fs if f['kind']=='decl' and f['declStart']['line']<=row['startLine']<=f['declEnd']['line']]
        assert row['startLine']>0 and len(found)==1 and found[0]['valStart'] is not None
        return found[0]
    reached=set();work=[r['name'] for r in core]+[r['name'] for r in graph if r['isInstance']]
    work += [r['name'] for r in graph if r['startLine']>0 and r['module'] in [c['module'] for c in state['native_controls']]]
    while work:
        name=work.pop()
        if name in reached:continue
        reached.add(name);work.extend(byname[name]['typeDeps']+byname[name]['valueDeps'])
    helpers=[];bridge=[];opens=[]
    for row in e.topological_sources(state['native_sources'],'project_relative'):
        module=row['module']
        if module==p.NATIVE:continue
        hs=sorted([byname[name] for name in reached if byname[name]['module']==module and
            byname[name]['kind']=='theorem' and byname[name]['startLine']>0],key=lambda r:r['startLine'])
        if not hs:continue
        namespace='ZetaNine.HarmonicStability' if row['parser_name']=='Def_ZetaNine_HarmonicStability' else 'ZetaNine.'+row['parser_name']
        text='open scoped BigOperators Topology\nopen Finset Polynomial Filter\n\nnamespace '+namespace+'\n\n'
        first=min(r['startLine'] for r in graph if r['module']==module and r['startLine']>0)
        for fact in facts[module]:
            if fact['kind']=='command' and fact['syntaxKind']=='Lean.Parser.Command.open' and fact['span']['end']['line']<first:
                text+=sources[module][fact['span']['start']['offset']:fact['span']['end']['offset']].decode()+'\n'
                opens.append(dict(module=module,fact=fact))
        for h in hs:
            fact=declaration(h['name']);helpers.append(dict(name=h['name'],module=module,fact=fact))
            text+=sources[module][fact['declStart']['offset']:fact['declEnd']['offset']].decode()+'\n\n'
        text+='end '+namespace+'\n\n';bridge.append(text)
    data=[r for r in graph if r['module'] in sources and r['kind']=='def' and r['startLine']>0]
    assert len(data)==70
    return dict(state=state,graph=graph,byname=byname,core=core,sources=sources,facts=facts,
        declaration=declaration,reached=reached,helpers=helpers,bridge=''.join(bridge),opens=opens,
        definition_names=[r['name'] for r in sorted(data,key=lambda r:(r['module'],r['startLine']))])


def emitter(module,names):
    text='import '+module+'\nimport Lean\nopen Lean\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\nrun_meta do\n'
    text+='''  let emit (label : String) (name : Name) : Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Meta.ppExpr d.value).pretty)
      | _ => pure none
    let fullvalue := match ci with | .defnInfo d => some (reprStr d.value) | _ => none
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson value),("value_expression_repr",toJson fullvalue),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    return text+''.join('  emit '+json.dumps(label)+' `'+name+'\n' for label,name in names)


def save_leaf(label,text):
    p.write(OUT/(label+'.lean'),text);p.write(PROJECT/(label+'.lean'),text)


def compile_module(label,module):
    obj='b/lib/lean/'+module.replace('.','/')+'.olean'
    (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    e.run(label,['-o',obj,module.replace('.','/')+'.lean'])


def prepare_stage():
    c=context();source=c['sources'][p.NATIVE];fs=c['facts'][p.NATIVE]
    header=e.rows(OUT/'header_info.jsonl')[0]
    assert header['start']['offset']==0
    assert source[:header['end']['offset']].decode().strip().splitlines()==[
        'import missions.zeta9.formalization.CoefficientMapKernelBridge',
        'import Mathlib.LinearAlgebra.Matrix.NonsingularInverse']
    defs=[c['declaration'](NS+'.'+name) for name in p.DEFS]
    chunks=[source[f['declStart']['offset']:f['declEnd']['offset']].decode() for f in defs]
    own_proofs={r['name'] for r in c['core'] if r['kind']=='theorem'}
    assert all(not set(c['byname'][NS+'.'+name]['typeDeps']+c['byname'][NS+'.'+name]['valueDeps'])&own_proofs for name in p.DEFS)
    preamble='import Definitions.Def_ZetaNine_CoefficientMapKernelBridge\nimport Mathlib.LinearAlgebra.Matrix.NonsingularInverse\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators Matrix\nopen Polynomial\n\nnamespace '+NS+'\n\nopen CoefficientMapAggregate CoefficientMapKernelBridge\n\n'
    definition=preamble+'\n\n'.join(chunks)+'\n\nend '+NS+'\n'
    p.write(OUT/'staged'/DEF_PATH,definition);p.write(PROJECT/DEF_PATH,definition)
    alias='import '+p.NATIVE+'\nimport Mathlib.LinearAlgebra.Matrix.NonsingularInverse\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators Matrix\nopen Polynomial\n\nnamespace '+ALIAS_NS+'\n\nopen CoefficientMapAggregate CoefficientMapKernelBridge\n\n'+'\n\n'.join(chunks)+'\n\nend '+ALIAS_NS+'\n'
    save_leaf('NativeValueComparisonDefinition',alias)
    save_leaf('StagedValueComparisonDefinition',alias.replace('import '+p.NATIVE,'import '+DEF_PATH.removesuffix('.lean').replace('/','.')))
    compare='import NativeValueComparisonDefinition\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.proofs true\n'
    compare+='\n'.join('theorem native_value_'+name+'_eq : '+ALIAS_NS+'.'+name+' = '+NS+'.'+name+' := rfl' for name in p.DEFS)+'\n\nrun_meta do\n'
    compare+='  for (name,aliasName) in ['+', '.join('(`'+NS+'.'+name+', `'+ALIAS_NS+'.'+name+')' for name in p.DEFS)+'] do\n'
    compare+='''    let .defnInfo d ← getConstInfo name | throwError "Original is not a Definition"
    let .defnInfo a ← getConstInfo aliasName | throwError "Alias is not a Definition"
    let te ← isDefEq d.type a.type
    let ve ← isDefEq d.value a.value
    unless te && ve do throwError "Whole Matrix Definition differs: {name}"
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_kernel_equality"),
      ("declaration",Json.str name.toString),("type_kernel_equal",toJson te),
      ("full_value_kernel_equal",toJson ve),("original_type_expression_repr",Json.str (reprStr d.type)),
      ("alias_type_expression_repr",Json.str (reprStr a.type)),
      ("original_value_expression_repr",Json.str (reprStr d.value)),
      ("alias_value_expression_repr",Json.str (reprStr a.value)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    compare+='  for name in ['+', '.join('`native_value_'+name+'_eq' for name in p.DEFS)+'] do\n'
    compare+='''    let ci ← getConstInfo name
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind",Json.str "whole_function_rfl"),("declaration",Json.str name.toString),
      ("type_expression_repr",Json.str (reprStr ci.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    save_leaf('native-value-comparison',compare)
    save_leaf('staged-value-comparison',compare.replace('import NativeValueComparisonDefinition','import StagedValueComparisonDefinition'))
    cuts=[(f['declStart']['offset'],f['declEnd']['offset'],b'') for f in defs]+[(0,header['end']['offset'],b'')]
    diagnostics=[f for f in fs if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.printAxioms']
    cuts += [(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in diagnostics]
    refs=[f for f in fs if f['kind']=='ref'];targets=[];proofs={}
    titles=['The actual monomial-row matrix has nonzero determinant',
        'The actual selected rational multiplier has row inverse coordinates',
        'The selected integer output has its genuine sum and absolute convergence']
    naturals=['For every even n>=2 the actual monomial-row, formal-output-column F matrix has nonzero rational determinant. Its invertibility is derived from the original aggregate kernel and bijection proofs; no determinant or invertibility premise is assumed.',
        'For every even n>=2 and integers b,a, the actual inverse multiplier for the output (b,0,0,0,a) has rational quartic coordinates equal to (b,a) times the actual selection matrix S times the actual F inverse. No integer polynomial inverse or integral coefficient claim is made.',
        'For every even n>=2 and integers b,a, the actual selected rational quartic multiplier has a genuine HasSum of weightedR at all positive integers, equal to b+a*zetaReal(9), and its absolute norms are Summable. Both conclusions are derived from the complete actual source proof closure, with no HasSum or summability premise.']
    problems=[]
    solprefix='import '+DEF_PATH.removesuffix('.lean').replace('/','.')+'\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 3000000\nnoncomputable section\n'+c['bridge']
    for index,(name,args) in enumerate(zip(p.TARGETS,p.ARGS)):
        full=NS+'.'+name;fact=c['declaration'](full);a,v=fact['declStart']['offset'],fact['valStart']['offset']
        ownrefs=[r for r in refs if r['const']==full]
        bindings=[r for r in ownrefs if a<=r['start']['offset']<v];assert len(bindings)==1
        binding=bindings[0];bs,be=binding['start']['offset'],binding['end']['offset']
        assert source[bs:be].decode()==name
        signature=source[be:v].decode();changes=[]
        for r in ownrefs:
            x,y=r['start']['offset'],r['end']['offset']
            if any(ca<=x and y<=cb for ca,cb,_ in cuts):continue
            spelling=source[x:y].decode();assert spelling in [name,full]
            changes.append((x,y,('checked_'+name if spelling==name else NS+'.checked_'+name).encode()))
        solution=solprefix+'\n'+edit(source,cuts+changes).decode()+'\n\nopen ZetaNine '+NS+' CoefficientMapAggregate CoefficientMapKernelBridge\n\ntheorem solution'+signature+':= by\n  exact '+NS+'.checked_'+name+' '+args+'\n\n#print axioms solution\n'
        formalchanges=[(bs-a,be-a,full.encode())]
        if fact['docstring']:
            ds=fact['docstring'];formalchanges.append((ds['start']['offset']-a,ds['end']['offset']-a,b''))
        formal=edit(source[a:v],formalchanges).decode().strip()+':= by sorry'
        refprefix='import '+DEF_PATH.removesuffix('.lean').replace('/','.')+'\n\nset_option autoImplicit false\nopen scoped BigOperators Matrix\nopen Polynomial ZetaNine '+NS+'\n'
        solpath='Solutions/Sol_ZetaNine_CoefficientMapMatrix_'+name+'.lean'
        refpath='Theorems/Thm_ZetaNine_CoefficientMapMatrix_'+name+'.lean'
        for path,text in [(solpath,solution),(refpath,refprefix+'\n'+formal+'\n')]:
            p.write(OUT/'staged'/path,text);p.write(PROJECT/path,text)
        targets.append(dict(theorem_name=full,local_solution=solpath,local_reference=refpath,wrapper_arguments=args))
        proofs[full]=dict(declaration_fact=fact,binding_fact=binding,original_signature=signature,
            rename_edits=[(x,y,text.decode()) for x,y,text in changes],extra_hypotheses=[],
            solution_sha256=p.sha(OUT/'staged'/solpath),reference_sha256=p.sha(OUT/'staged'/refpath))
        problems.append(dict(theorem_name=full,theorem_title=titles[index],formal_statement=formal,
            preamble=refprefix,natural_language_statement=naturals[index],
            source='Actual frozen native CoefficientMapMatrix source SHA256 '+p.SOURCE_SHA,
            tags=['number-theory','linear-algebra','formalization']))
    p.dump(OUT/'definitions-request.json',[dict(definition_name='ZetaNine_CoefficientMapMatrix',
        definition_title='The actual monomial-row F matrix and selected rational inverse',definition=definition,
        natural_language_statement='Define the genuine F monomial rows and five actual output columns, the two selected integer directions B and rho9, and their actual rational inverse multiplier on Even n>=2. All five original Definition values remain fixed; no invertibility or sum premise is added.',
        source='Actual frozen native CoefficientMapMatrix SHA256 '+p.SOURCE_SHA,
        tags=['number-theory','linear-algebra','formalization'],env=p.REV,private=False)])
    p.dump(OUT/'problems-request.json',dict(env=p.REV,private=False,problems=problems))
    p.dump(OUT/'target-plan.json',dict(definition='ZetaNine_CoefficientMapMatrix',local_definition=DEF_PATH,
        targets=targets,existing_definitions=c['state']['parent_definitions']))
    p.write(OUT/'actual-proof-bridge.lean.inc',c['bridge'])
    p.dump(OUT/'integration-provenance.json',dict(source_sha256=p.SOURCE_SHA,graph_records=len(c['graph']),
        source_declarations=22,source_defs=5,source_proofs=17,all_project_source_definitions=70,
        header=header,definition_facts=defs,actual_definition_valueDeps={name:c['byname'][NS+'.'+name]['valueDeps'] for name in p.DEFS},
        cross_module_core_closure=sorted(c['reached']),inline_helper_facts=c['helpers'],
        inline_helper_names=[r['name'] for r in c['helpers']],bridge_open_context_facts=c['opens'],
        deleted_diagnostic_facts=diagnostics,targets=proofs,new_external_theorem_boundaries=[],
        statement_proof_spans_from_actual_parser_only=True,proof_records_per_solution=len(c['helpers'])+18))
    print(json.dumps(dict(actual_graph_records=len(c['graph']),actual_parent_helpers=len(c['helpers']),
        full_original_Matrix_proofs=17,proof_records_per_Solution=len(c['helpers'])+18,new_Definitions=5)))


def stage():
    prepare_stage()
    compile_module('build-definition',DEF_PATH.removesuffix('.lean').replace('/','.'))
    compile_module('build-native-alias','NativeValueComparisonDefinition')
    e.run('native-value-comparison',['native-value-comparison.lean'])
    compile_module('build-staged-alias','StagedValueComparisonDefinition')
    e.run('staged-value-comparison',['staged-value-comparison.lean'])
    for index,row in enumerate(p.load(OUT/'target-plan.json')['targets']):
        for kind in ['solution','reference']:
            compile_module('build-'+str(index)+'-'+kind,row['local_'+kind].removesuffix('.lean').replace('/','.'))
    print('All eleven actual Matrix stage calls completed; author audits/freeze remain pending.')


def audits():
    c=context();targets=p.load(OUT/'target-plan.json')['targets']
    matrix_proofs=[r['name'] for r in c['core'] if r['kind']=='theorem']
    groups=[('types-original',p.NATIVE,[(n,n) for n in c['definition_names']+matrix_proofs]),
        ('types-definition',DEF_PATH.removesuffix('.lean').replace('/','.'),[(n,n) for n in c['definition_names']])]
    for index,target in enumerate(targets):
        original=target['theorem_name'];checked=NS+'.checked_'+original.rsplit('.',1)[1]
        sol=target['local_solution'].removesuffix('.lean').replace('/','.')
        ref=target['local_reference'].removesuffix('.lean').replace('/','.')
        mapped=lambda name:checked if name==original else name
        groups += [('types-'+str(index)+'-solution',sol,[(n,mapped(n)) for n in c['definition_names']+matrix_proofs]+[('solution','solution')]),
            ('types-'+str(index)+'-reference',ref,[(n,n) for n in c['definition_names']+[original]]),
            ('proofs-'+str(index),sol,[(r['name'],r['name']) for r in c['helpers']]+[(n,mapped(n)) for n in matrix_proofs]+[('solution','solution')])]
    for label,module,names in groups:
        save_leaf(label,emitter(module,names));e.run(label,[label+'.lean'])
    resolver='import '+p.NATIVE+'\nimport '+DEF_PATH.removesuffix('.lean').replace('/','.')+'\n'
    # Native and staged modules define the same namespaces; never import both
    # into one environment. Resolution is audited with staged imports only.
    resolver='import '+DEF_PATH.removesuffix('.lean').replace('/','.')+'\n'+''.join(
        'import '+row['local_solution'].removesuffix('.lean').replace('/','.')+'\n' for row in targets)
    # Solutions also duplicate the complete original proof namespace, so
    # findOLean needs no imports of all three at once: use Lean's resolver API.
    resolver='import Lean\nopen Lean\nrun_meta do\n'
    modules=list(dict.fromkeys([r['module'] for r in c['state']['native_sources']]+[
        r['module'] for r in c['state']['parent_definitions']]+[DEF_PATH.removesuffix('.lean').replace('/','.')]+[
        row['local_'+kind].removesuffix('.lean').replace('/','.') for row in targets for kind in ['solution','reference']]+[
        'NativeValueComparisonDefinition','StagedValueComparisonDefinition']))
    resolver+='  for name in ['+', '.join('`'+m for m in modules)+'] do\n'
    resolver+='''    let path ← findOLean name
    IO.println (Json.mkObj [("module",Json.str name.toString),("olean",Json.str path.toString)]).compress
'''
    save_leaf('resolution-audit',resolver);e.run('resolution-audit',['resolution-audit.lean'])
    print('Basic types/proof/source-resolution audits completed; exact independent-type and boundary replay pending.')


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser();parser.add_argument('phase',choices=['prepare','stage','audits'])
    parser.add_argument('--lane-granted',action='store_true')
    args=parser.parse_args()
    if args.phase=='prepare':prepare_stage();return
    assert args.lane_granted,'Explicit Root lane grant required.'
    assert not (OUT/'author-audit.json').exists(),'Frozen author must never be modified.'
    if args.phase=='stage':stage()
    else:audits()


if __name__=='__main__':main()
