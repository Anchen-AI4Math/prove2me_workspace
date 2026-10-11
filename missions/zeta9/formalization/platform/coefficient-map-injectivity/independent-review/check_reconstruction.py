"""Independently reconstruct seven stages from the replayed actual Lean facts."""
from pathlib import Path
import hashlib,json,sys
sys.stdout.reconfigure(encoding='utf-8')
HERE=Path(__file__).resolve().parent;BATCH=HERE.parent;TASK=BATCH.parents[2];ROOT=TASK.parents[1]
NS='ZetaNine.CoefficientMapInjectivity'
DEFS=['baseNumerator','baseU','weightedNumerator','polePolynomial','AllLocalCoefficientsZero','ProperMultiplier','fullLocalCoefficientMap']
TARGETS=['all_local_coefficients_zero_implies_zero','fullLocalCoefficientMap_injective','quartic_is_proper']
ARGS=['n W hproper hzero','n','n W hW']
MATHLIB=['Mathlib.Algebra.Polynomial.BigOperators','Mathlib.Algebra.Polynomial.RingDivision','Mathlib.Algebra.Polynomial.Degree.Lemmas','Mathlib.RingTheory.Coprime.Lemmas']
EXPECTED={'CoefficientMap':'e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03','CoefficientMapJet':'e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a','CoefficientMapInjectivity':'ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095'}
checks=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def check(n,okay,e=None):
    checks.append({'name':n,'pass':bool(okay),'evidence':e});assert okay,n
def canonical(rs):
    result=[]
    for r in rs:
        r=dict(r)
        for k in ['typeDeps','valueDeps']:
            if k in r:r[k]=sorted(r[k])
        result.append(json.dumps(r,sort_keys=True,ensure_ascii=False))
    return sorted(result)
def splice(data,edits):
    edge=len(data)
    for a,b,v in sorted(set(edits),reverse=True):
        assert 0<=a<=b<=edge,(a,b,edge)
        data=data[:a]+v+data[b:];edge=a
    return data
jet=TASK/'formalization/platform/coefficient-map-jet'
graph_template=(jet/'extract_decl_graph.lean').read_text(encoding='utf-8-sig').replace('import missions.zeta9.formalization.CoefficientMapJet','import missions.zeta9.formalization.CoefficientMapInjectivity').replace('missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl','../decl_graph.jsonl')
parser_template=(jet/'extract_sketch_info.lean').read_text(encoding='utf-8-sig')
check('official_predecessor_metaprogram_parser_header_bodies_unchanged_only_documented_wrapper_inputs',graph_template==(BATCH/'extract_decl_graph.lean').read_text(encoding='utf-8-sig') and all(parser_template.replace('missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean','../'+('oracle-input.lean' if n.endswith('Injectivity') else n+'-oracle-input.lean'))==(BATCH/('extract_'+n+'_sketch.lean')).read_text(encoding='utf-8-sig') for n in EXPECTED) and (jet/'extract_header.lean').read_bytes()==(BATCH/'extract_header.lean').read_bytes())
sources={n:(TASK/f'formalization/{n}.lean').read_bytes() for n in EXPECTED}
for n,h in EXPECTED.items():
    snapshot='oracle-input.lean' if n.endswith('Injectivity') else n+'-oracle-input.lean'
    check(n+'_source_and_parser_snapshot_exact',digest(sources[n])==h and sources[n]==(HERE/snapshot).read_bytes()==(BATCH/snapshot).read_bytes())
source=sources['CoefficientMapInjectivity']
graph=rows(HERE/'decl_graph.jsonl');byname={g['name']:g for g in graph}
check('independent_actual_94_record_three_module_Stage1_graph_exact',len(graph)==94 and canonical(graph)==canonical(rows(BATCH/'decl_graph.jsonl')))
facts={}
for n in EXPECTED:
    fn='sketch_info.jsonl' if n.endswith('Injectivity') else n+'-sketch_info.jsonl'
    facts[n]=rows(HERE/fn)
    check(n+'_actual_Stage2_declaration_reference_command_spans_exact',canonical(facts[n])==canonical(rows(BATCH/fn)),{k:sum(x['kind']==k for x in facts[n]) for k in ['decl','ref','command']})
headers=rows(HERE/'header_info.jsonl');header=headers[0];he=header['end']['offset']
check('actual_header_parser_replay_exact_native_import_boundary',len(headers)==1 and canonical(headers)==canonical(rows(BATCH/'header_info.jsonl')) and header['start']['offset']==0 and source[:he].decode().strip().splitlines()==['import missions.zeta9.formalization.CoefficientMapJet']+['import '+m for m in MATHLIB],header)
check('cross_module_graph_contains_only_actual_defs_and_proofs_no_axiom',len(byname)==94 and all(g['kind'] in ['def','theorem'] for g in graph))
def declaration(full):
    g=byname[full];assert g['startLine']>0
    module=g['module'].split('.')[-1]
    ds=[d for d in facts[module] if d['kind']=='decl' and d['declStart']['line']<=g['startLine']<=d['declEnd']['line']]
    assert len(ds)==1 and ds[0]['valStart'] is not None
    return ds[0]
core=[g for g in graph if g['module'].endswith('.CoefficientMapInjectivity') and g['startLine']>0]
generated=[g['name'] for g in graph if g['module'].endswith('.CoefficientMapInjectivity') and not g['startLine']]
check('Inject_source_twenty_five_actual_seven_defs_eighteen_proofs_four_generated_eq_1',len(core)==25 and sum(g['kind']=='def' for g in core)==7 and sum(g['kind']=='theorem' for g in core)==18 and len(generated)==4,{'generated':generated})
reached=set();work=[g['name'] for g in core]+[g['name'] for g in graph if g['isInstance']]
while work:
    n=work.pop()
    if n in reached:continue
    reached.add(n);work.extend(byname[n]['typeDeps']+byname[n]['valueDeps'])
helper_names=[];bridge=''
for module in ['CoefficientMap','CoefficientMapJet']:
    hs=sorted([byname[n] for n in reached if byname[n]['module'].endswith('.'+module) and byname[n]['kind']=='theorem' and byname[n]['startLine']>0],key=lambda g:g['startLine'])
    if not hs:continue
    bridge+='open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.'+module+'\n\n'
    for g in hs:
        d=declaration(g['name']);helper_names.append(g['name'])
        bridge+=sources[module][d['declStart']['offset']:d['declEnd']['offset']].decode()+'\n\n'
    bridge+='end ZetaNine.'+module+'\n\n'
expected_helpers=['ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero']+['ZetaNine.CoefficientMapJet.'+n for n in ['shiftedVariable_eval','shiftedClearedDenominator_eval','shiftedClearedDenominator_constant','shiftedClearedDenominator_constant_ne_zero','clearedSeries_denominator_identity','weightedClearedSeries_denominator_identity']]
check('actual_cross_module_closure_selects_exact_one_Base_six_Jet_proofs',helper_names==expected_helpers,{'helpers':helper_names,'closure':sorted(reached)})
check('inline_seven_helper_bridge_reconstructed_from_original_parser_bytes',bridge.encode()==(BATCH/'actual-proof-bridge.lean.inc').read_bytes(),{'sha256':digest(bridge.encode())})
def_facts=[declaration(NS+'.'+n) for n in DEFS]
defpath='Definitions/Def_ZetaNine_CoefficientMapInjectivity.lean'
prefix='import Definitions.Def_ZetaNine_CoefficientMapJet\n'+'\n'.join('import '+m for m in MATHLIB)+'\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace '+NS+'\n\n'
definition=prefix.encode()+b'\n\n'.join(source[d['declStart']['offset']:d['declEnd']['offset']] for d in def_facts)+('\n\nend '+NS+'\n').encode()
check('seven_Def_spans_are_original_actual_defs_without_proof_formula_replacement',all(byname[NS+'.'+n]['kind']=='def' for n in DEFS) and definition==(BATCH/'staged'/defpath).read_bytes(),{'sha256':digest(definition)})
dreq=load(BATCH/'definitions-request.json')
check('definition_request_exact_reconstructed_Def_source',len(dreq)==1 and dreq[0]['definition'].encode()==definition)
cmds=[d for d in facts['CoefficientMapInjectivity'] if d['kind']=='command']
diags=[d for d in cmds if d['syntaxKind']=='Lean.Parser.Command.printAxioms']
diagcuts=[(d['span']['start']['offset'],d['span']['end']['offset'],b'') for d in diags]
cuts=[(0,he,b'')]+[(d['declStart']['offset'],d['declEnd']['offset'],b'') for d in def_facts]+diagcuts
check('exact_nine_actual_parser_printAxioms_diagnostics_removed',len(diags)==9 and all(source[a:b].startswith(b'#print axioms ') for a,b,_ in diagcuts))
refs=[f for f in facts['CoefficientMapInjectivity'] if f['kind']=='ref']
solheader='import Definitions.Def_ZetaNine_CoefficientMapInjectivity\nimport Mathlib.Tactic\n'+'\n'.join('import '+m for m in MATHLIB)+'\n\n'+bridge
preamble='import Definitions.Def_ZetaNine_CoefficientMapInjectivity\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen '+NS+'\n'
req=load(BATCH/'problems-request.json')
check('exact_three_public_pinned_offline_problem_endpoints',req['env']=='0df444a360eaa60ab8c11dca51a86af692955474' and req['private'] is False and [p['theorem_name'] for p in req['problems']]==[NS+'.'+n for n in TARGETS])
targets=[]
for i,n in enumerate(TARGETS):
    full=NS+'.'+n;d=declaration(full);a,v=d['declStart']['offset'],d['valStart']['offset']
    rs=[r for r in refs if r['const']==full];bs=[r for r in rs if a<=r['start']['offset']<v];assert len(bs)==1
    b,e=bs[0]['start']['offset'],bs[0]['end']['offset'];assert source[b:e].decode()==n
    sig=source[e:v];renames=[]
    for r in rs:
        x,y=r['start']['offset'],r['end']['offset']
        if any(ca<=x and y<=cb for ca,cb,_ in cuts):continue
        old=source[x:y].decode();assert old in [n,full]
        renames.append((x,y,('checked_'+n if old==n else NS+'.checked_'+n).encode()))
    sol=solheader.encode()+b'\n'+splice(source,cuts+renames)+('\n\nopen '+NS+'\n\ntheorem solution').encode()+sig+(':= by\n  exact '+NS+'.checked_'+n+' '+ARGS[i]+'\n\n#print axioms solution\n').encode()
    edits=[(b-a,e-a,full.encode())]
    if d['docstring']:
        doc=d['docstring'];edits.append((doc['start']['offset']-a,doc['end']['offset']-a,b''))
    formal=splice(source[a:v],edits).decode().strip()+':= by sorry'
    ref=(preamble+'\n'+formal+'\n').encode()
    solpath='Solutions/Sol_ZetaNine_CoefficientMapInjectivity_'+n+'.lean';refpath='Theorems/Thm_ZetaNine_CoefficientMapInjectivity_'+n+'.lean'
    check(n+'_full_solution_exact_original_byte_splice_all_eighteen_plus_seven_proofs',sol==(BATCH/'staged'/solpath).read_bytes(),{'sha256':digest(sol),'rename_spans':[[x,y] for x,y,_ in renames],'retained_source_proofs':18,'inline_original_helpers':7})
    check(n+'_stub_and_request_use_exact_original_signature_no_extra_hypotheses',ref==(BATCH/'staged'/refpath).read_bytes() and req['problems'][i]['formal_statement']==formal and req['problems'][i]['preamble']==preamble,{'signature':sig.decode()})
    targets.append({'theorem':full,'solution':solpath,'reference':refpath,'signature':sig.decode()})
frozen=[]
for line in (BATCH/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
    h,rel=line.split('  ',1);p=(BATCH/rel).resolve();assert p.is_relative_to(TASK)
    frozen.append({'task_relative':p.relative_to(TASK).as_posix(),'expected':h,'actual':sha(p)})
check('all_134_frozen_author_members_intact',len(frozen)==134 and all(f['expected']==f['actual'] for f in frozen))
check('frozen_audit_plan_manifest_control_hashes_exact',sha(BATCH/'author-audit.json')=='b91251de9261a7656de3274575072995452706d8a9ee0e570ae9ded4ce5b2253' and sha(BATCH/'root-copy-plan.json')=='51bc6ae331a1e8b781c4dd8250248e4bed8e7c5092bb50db5bcd73f4423cf9c3' and sha(BATCH/'SHA256SUMS.txt')=='d04da22546da82edfbdc68949573e71359ebaef5542f93d3e12b44df21edccb2')
result={'checks':checks,'targets':targets,'frozen_manifest_members':frozen,'cross_module_core_closure':sorted(reached),'inline_helpers':helper_names,'actual_Stage1_records':len(graph),'Inject_source_records':len(core),'Inject_generated_records':generated,'actual_Stage2_counts':{k:sum(f['kind']==k for f in facts['CoefficientMapInjectivity']) for k in ['decl','ref','command']},'header':header}
(HERE/'reconstruction-report.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Independent reconstruction PASS: actual graph/parser/header, seven original-byte stages, all 134 hashes.',flush=True)
