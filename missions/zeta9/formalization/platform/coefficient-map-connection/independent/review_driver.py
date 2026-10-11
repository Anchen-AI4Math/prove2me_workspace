"""Actual Connection oracle-driven author pipeline, with resumable immutable runs.

No import-time operations. Every Lean phase requires --lane-granted. This file
does not install root modules, alter scope, read credentials, or call any API.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, subprocess, sys, time

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
PROJECT = TASK/'.rt/ct1'
BUILD = PROJECT/'b/lib/lean'
NS = 'ZetaNine.CoefficientMapConnection'
ALIAS_NS = NS+'ValueComparison'
NATIVE = 'missions.zeta9.formalization.CoefficientMapConnection'
SOURCE_SHA = '098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
REV = '0df444a360eaa60ab8c11dca51a86af692955474'
DEFS = ['connectionU','connectionV','connectionD','connectionH','connectionReflection',
        'coefficientPolynomial','inputP','inputQ','connectionOperator','connectionLinearMap',
        'connectionZ','connectionTarget']
TARGETS = ['connection_homogeneous_kernel_zero','connectionLinearMap_bijective',
           'connection_five_systems_unique']
ARGS = ['n hn P q hqdeg heq','n hn','n hn r']
MATHLIB = ['Mathlib.Algebra.Polynomial.RingDivision','Mathlib.Algebra.Polynomial.Degree.Lemmas',
           'Mathlib.Algebra.Polynomial.BigOperators','Mathlib.LinearAlgebra.FiniteDimensional.Basic',
           'Mathlib.Tactic']
STD = {'propext','Classical.choice','Quot.sound'}
DEF_PATH = 'Definitions/Def_ZetaNine_CoefficientMapConnection.lean'
AUTHOR = TASK/'verification/formalization-coefficient-map-connection-2026-10-04'

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
digest = lambda b: hashlib.sha256(b).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
rows = lambda p: [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]

def write(p, s):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(s if isinstance(s, bytes) else s.encode('utf-8'))

def dump(p, d):
    write(p, json.dumps(d, ensure_ascii=False, indent=2)+'\n')

def binding(p):
    return dict(task_relative=p.relative_to(TASK).as_posix(), bytes=p.stat().st_size, sha256=sha(p))

def edit(data, edits):
    edge = len(data)
    for a, b, replacement in sorted(set(edits), reverse=True):
        assert 0 <= a <= b <= edge, 'Overlapping or out-of-range actual parser edits.'
        data = data[:a]+replacement+data[b:]
        edge = a
    return data

def preconditions():
    gate = load(OUT/'frozen-handoff.json')
    assert gate['explicit_parent_lane1_authorized']
    parent=OUT.parent
    assert sha(parent/'author-audit.json') == gate['author_sha256']
    for r in load(parent/'author-audit.json')['stable_files']:
        p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
    rootfreeze=TASK/gate['Root_freeze']['task_relative']
    assert sha(rootfreeze)==gate['Root_freeze']['sha256']
    for r in load(rootfreeze)['stable_files']:
        p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
    assert sha(TASK/'formalization/CoefficientMapConnection.lean')==SOURCE_SHA
    assert sha(PROJECT/(NATIVE.replace('.','/')+'.lean'))==SOURCE_SHA
    assert (PROJECT/'.lake/packages').is_junction()
    assert (PROJECT/'.lake/packages').resolve()==(ROOT/'.lake/packages').resolve()

def configure():
    """Pure preparation, no invocation of Lean or Lake."""
    preconditions()
    assert not (PROJECT/'b').exists(), 'Configuration requires the recorded fresh empty cache.'
    code = '''import Lake
open Lake DSL
package zeta9ConnectionPlatformAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'''+REV+'''"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapConnection]
  globs := #[.one `missions.zeta9.formalization.CoefficientMapConnection]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
lean_lib ValueComparison where
  roots := #[`NativeValueComparisonDefinition, `StagedValueComparisonDefinition]
  globs := #[.one `NativeValueComparisonDefinition, .one `StagedValueComparisonDefinition]
'''
    write(PROJECT/'lakefile.lean', code)
    for name in ['lean-toolchain','lake-manifest.json']:
        assert (PROJECT/name).read_bytes() == (ROOT/name).read_bytes()
    for name in ['extract_decl_graph.lean','extract_header.lean','parse-source.lean',
                 'parse-native-author.lean','parse-native-boundary.lean']:
        write(PROJECT/name, (OUT/name).read_bytes())
    write(PROJECT/'native-type-audit.lean', (OUT/'native-type-audit.lean').read_bytes())
    write(PROJECT/'native-boundary-audit.lean', (OUT/'native-boundary-audit.lean').read_bytes())
    # This helper removes any ancestor Root source/object fallback supplied by
    # the calling environment, and records the exact paths used by actual Lean.
    wrapper = '''from pathlib import Path
import json, os, subprocess, sys
ROOT = Path(r"'''+str(ROOT)+'''")
PROJECT = Path(__file__).resolve().parent
env = os.environ.copy()
selected = {}
for name in ['LEAN_PATH', 'LEAN_SRC_PATH']:
    old = env.get(name, '')
    paths = [x for x in old.split(os.pathsep) if x]
    keep = []
    for raw in paths:
        p = Path(raw).resolve()
        if p.is_relative_to(PROJECT) or p.is_relative_to(ROOT/'.lake/packages'):
            keep.append(raw)
    if name == 'LEAN_PATH':
        own = str(PROJECT/'b/lib/lean')
        if own not in keep: keep.insert(0, own)
    if name == 'LEAN_SRC_PATH':
        if str(PROJECT) not in keep: keep.insert(0, str(PROJECT))
    env[name] = os.pathsep.join(keep)
    selected[name] = {'original': paths, 'filtered': keep}
label = env['CONNECTION_RUN_LABEL']
receipt = Path(env['CONNECTION_RUN_PATHS_RECEIPT'])
receipt.write_text(json.dumps(selected, indent=2)+'\\n', encoding='utf-8')
p = subprocess.run(sys.argv[1:], env=env)
sys.exit(p.returncode)
'''
    write(PROJECT/'lean_call.py', wrapper)
    modules = [NATIVE, DEF_PATH.removesuffix('.lean').replace('/','.')]
    for t in TARGETS:
        for role in ['Solutions.Sol_', 'Theorems.Thm_']:
            modules.append(role+'ZetaNine_CoefficientMapConnection_'+t)
    objects = [PROJECT/'b/lib/lean'/(m.replace('.','/')+'.olean') for m in modules]
    checks = [dict(object_path=str(p), length=len(str(p)), path_plus_64=len(str(p))+64,
                   passed=len(str(p))+64<=259) for p in objects]
    assert all(x['passed'] for x in checks)
    dump(OUT/'author-execution-plan.json', dict(status='PREPARATION_ONLY', Lean_executed=False,
        source_sha256=SOURCE_SHA, path_checks=checks,
        phases=['fresh native and actual source/control/header parsers',
                'actual local-have constructor closure and original/staged kernel equality',
                '7 staged modules and actual 12 types/values in 7 contexts',
                '84 complete source+wrapper proof records and target exact types',
                'native39 and closed12 boundary replay against complete staged solution',
                'author immutable freeze; separate independent platform review'],
        no_borrowed_native_objects=True, no_root_API_scope_credential_writes=True))
    print('Pure author driver configured; no Lean or Lake executed.', flush=True)

def run(label, args, stdout_file=None):
    """Retain every actual attempt; successful prior same-byte runs may resume."""
    preconditions()
    receiptfile = OUT/'compile-receipt.json'
    receipt = load(receiptfile) if receiptfile.exists() else dict(
        role='independent platform replay actual executions', source_sha256=SOURCE_SHA,
        source_project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        fresh_build_task_relative=(PROJECT/'b').relative_to(TASK).as_posix(),
        native_and_staged_objects_borrowed=False, root_writes=False, API_calls=False, rows=[])
    matching = [r for r in receipt['rows'] if r['label'] == label]
    successful = [r for r in matching if r['exit_code'] == 0 and r['command_tail'] == args]
    if successful:
        r = successful[-1]
        assert sha(TASK/r['log']['task_relative']) == r['log']['sha256']
        assert all(sha(TASK/x['task_relative']) == x['sha256'] for x in r['input_bindings'])
        assert all(sha(TASK/x['task_relative']) == x['sha256'] for x in r['output_bindings'])
        print(label+': resumed verified actual exit 0', flush=True)
        return r
    attempt = OUT/'actual-runs'/(label+'-'+str(len(matching)+1).zfill(2))
    attempt.mkdir(parents=True, exist_ok=False)
    inputs = [PROJECT/'lean_call.py',PROJECT/'lakefile.lean',PROJECT/'lean-toolchain',PROJECT/'lake-manifest.json']
    inputs += [PROJECT/x for x in args if x.endswith('.lean') and (PROJECT/x).is_file()]
    input_bindings = [binding(p) for p in dict.fromkeys(inputs)]
    env = os.environ.copy()
    env.pop('LEAN_PATH', None); env.pop('LEAN_SRC_PATH', None)
    env['CONNECTION_RUN_LABEL'] = label
    env['CONNECTION_RUN_PATHS_RECEIPT'] = str(attempt/'selected-paths.json')
    cmd = ['lake','env',sys.executable,str(PROJECT/'lean_call.py')]+args
    start = time.time()
    p = subprocess.run(cmd, cwd=PROJECT, env=env, capture_output=True)
    write(attempt/'stdout.log',p.stdout); write(attempt/'stderr.log',p.stderr)
    write(attempt/'combined.log',p.stdout+p.stderr);write(attempt/'exit.txt',str(p.returncode)+'\n')
    outputs = []
    if '-o' in args:
        obj = PROJECT/args[args.index('-o')+1]
        if p.returncode == 0:
            assert obj.is_file()
            outputs = [binding(x) for x in sorted(obj.parent.glob(obj.name+'*')) if x.is_file()]
    r = dict(label=label, attempt=len(matching)+1, command=cmd, command_tail=args,
             elapsed_seconds=time.time()-start, exit_code=p.returncode,
             log=binding(attempt/'combined.log'), stdout=binding(attempt/'stdout.log'),
             stderr=binding(attempt/'stderr.log'), exit_file=binding(attempt/'exit.txt'),
             selected_paths=binding(attempt/'selected-paths.json'),
             input_bindings=input_bindings, output_bindings=outputs)
    receipt['rows'].append(r);dump(receiptfile,receipt)
    write(OUT/(label+'.log'),p.stdout+p.stderr);write(OUT/(label+'-exit.txt'),str(p.returncode)+'\n')
    if stdout_file: write(OUT/stdout_file,p.stdout)
    print(label+': actual exit '+str(p.returncode),flush=True)
    if p.returncode:
        print((p.stdout+p.stderr).decode('utf-8', errors='replace'),flush=True)
    assert p.returncode == 0, 'Actual failed execution retained.'
    return r

def compile_module(label, module):
    source = module.replace('.','/')+'.lean'
    obj = 'b/lib/lean/'+module.replace('.','/')+'.olean'
    assert len(str(PROJECT/obj))+64 <= 259
    (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    return run(label,['lean','-o',obj,source])

def oracles():
    if not (OUT/'compile-receipt.json').exists():
        assert not (PROJECT/'b').exists(), 'First actual compile requires absent fresh cache.'
    run('toolchain',['lean','--version'])
    compile_module('build-native',NATIVE)
    run('stage1-extract',['lean','extract_decl_graph.lean'])
    run('stage2-source',['lean','--run','parse-source.lean',NATIVE.replace('.','/')+'.lean','ZetaNine'],'sketch_info.jsonl')
    run('stage2-header',['lean','--run','extract_header.lean',NATIVE.replace('.','/')+'.lean'],'header_info.jsonl')
    run('native-author-audit',['lean','native-type-audit.lean'])
    run('native-boundary-audit',['lean','native-boundary-audit.lean'])
    run('parse-native-author',['lean','--run','parse-native-author.lean','native-type-audit.lean','ZetaNine'],'native-author-sketch_info.jsonl')
    run('parse-native-boundary',['lean','--run','parse-native-boundary.lean','native-boundary-audit.lean','ZetaNine'],'native-boundary-sketch_info.jsonl')

def context():
    source = (OUT/'CoefficientMapConnection-oracle-input.lean').read_bytes()
    assert digest(source) == SOURCE_SHA
    graph = rows(OUT/'decl_graph.jsonl');facts=rows(OUT/'sketch_info.jsonl')
    byname = {g['name']:g for g in graph}
    assert not any(g['kind']=='axiom' for g in graph)
    core = sorted([g for g in graph if g['module']==NATIVE and g['startLine']>0],key=lambda g:g['startLine'])
    assert len(core)==39 and sum(g['kind']=='def' for g in core)==12 and sum(g['kind']=='theorem' for g in core)==27
    assert len([f for f in facts if f['kind']=='decl'])==39
    def declaration(full):
        g=byname[full]
        ds=[f for f in facts if f['kind']=='decl' and f['declStart']['line']<=g['startLine']<=f['declEnd']['line']]
        assert len(ds)==1 and ds[0]['valStart'] is not None
        return ds[0]
    def closure(seed):
        reached=set();work=list(seed)
        while work:
            name=work.pop()
            if name in reached:continue
            reached.add(name);work.extend(byname[name]['typeDeps']+byname[name]['valueDeps'])
        return reached
    defs=[declaration(NS+'.'+n) for n in DEFS]
    return dict(source=source,graph=graph,core=core,byname=byname,facts=facts,
                refs=[f for f in facts if f['kind']=='ref'],declaration=declaration,
                closure=closure,DEFS=DEFS,def_facts=defs,NATIVE=NATIVE,NS=NS,ALIAS_NS=ALIAS_NS,
                MATHLIB=MATHLIB,OUT=OUT,PROJECT=PROJECT,write=write,dump=dump,edit=edit,rows=rows,
                run=lambda label,args: run(label,args[2:] if args[:2]==['lake','env'] else args),
                serial_Lean_lane_allocated=True,actual_oracles_successful=True)

def emitter(module,names):
    code='import '+module+'\nimport Lean\nopen Lean\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\nrun_meta do\n'
    code+='''  let emit (label : String) (name : Name) : Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let type ← Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Meta.ppExpr d.value).pretty)
      | _ => pure none
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str type.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson value),("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    code+=''.join('  emit '+json.dumps(label)+' `'+name+'\n' for label,name in names)
    return code

def stage():
    c=context();source=c['source'];refs=c['refs'];decl=c['declaration']
    spec=importlib.util.spec_from_file_location('connection_fields',OUT/'embed_definition_fields.py')
    fields=importlib.util.module_from_spec(spec);spec.loader.exec_module(fields)
    definition,alias,provenance=fields.create_definitions(c)
    write(OUT/'staged'/DEF_PATH,definition);write(PROJECT/DEF_PATH,definition)
    write(OUT/'NativeValueComparisonDefinition.lean',alias);write(PROJECT/'NativeValueComparisonDefinition.lean',alias)
    stagedalias=alias.replace('import '+NATIVE,'import '+DEF_PATH.removesuffix('.lean').replace('/','.'))
    write(OUT/'StagedValueComparisonDefinition.lean',stagedalias);write(PROJECT/'StagedValueComparisonDefinition.lean',stagedalias)
    fields.create_value_comparison(c)
    nativecompare=(OUT/'native-value-comparison.lean').read_text(encoding='utf-8')
    stagecompare=nativecompare.replace('import NativeValueComparisonDefinition','import StagedValueComparisonDefinition')
    write(OUT/'staged-value-comparison.lean',stagecompare);write(PROJECT/'staged-value-comparison.lean',stagecompare)
    header=rows(OUT/'header_info.jsonl')[0];he=header['end']['offset']
    assert header['start']['offset']==0
    assert source[:he].decode().strip().splitlines()==['import '+m for m in MATHLIB]
    diagnostics=[f for f in c['facts'] if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Command.printAxioms']
    cuts=[(d['declStart']['offset'],d['declEnd']['offset'],b'') for d in c['def_facts']]
    cuts += [(0,he,b'')]+[(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in diagnostics]
    solprefix='import '+DEF_PATH.removesuffix('.lean').replace('/','.')+'\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\n'
    preamble='import '+DEF_PATH.removesuffix('.lean').replace('/','.')+'\n\nset_option autoImplicit false\nnoncomputable section\nopen Polynomial '+NS+'\n'
    targets=[];problems=[];pt={}
    titles=['Original connection homogeneous kernel is zero for n>=1',
            'The genuine fifteen-coordinate connection map is bijective',
            'The five original connection systems have unique bounded rational solutions']
    naturals=[
        'For every n>=1, rational polynomials P,q with natDegree(q)<=9 satisfying the actual homogeneous identity D_n P(u_n)+H_n(q)=0 must both vanish. No P-degree bound or preassigned kernel conclusion is assumed. The tenfold root argument retains n>=1; the written signed n=0 system has a nonzero kernel.',
        'For every n>=1, the genuine rational linear map from the five P coefficients and ten q coefficients to the fifteen even t coefficients of D_n P(u_n)+H_n(q) is bijective. Reflection recovers the whole polynomial. These even t coordinates are triangularly equivalent to the paper u coordinates; identical matrix entries are not asserted.',
        'For every n>=1 and r=0,...,4, there exists exactly one rational polynomial pair P,q of natural degrees at most four and nine satisfying the full original polynomial identity with the genuine scaled three-factor Z_n(u)(u-n-1)^r target. Rational-function, HasSum and five-output parameter transport are separate results.']
    origin='Actual original D/H connection system; frozen source SHA256 '+SOURCE_SHA+'.'
    for i,name in enumerate(TARGETS):
        full=NS+'.'+name;d=decl(full);a,v=d['declStart']['offset'],d['valStart']['offset']
        occurrences=[r for r in refs if r['const']==full]
        bs=[r for r in occurrences if a<=r['start']['offset']<v];assert len(bs)==1
        bs=bs[0];x,y=bs['start']['offset'],bs['end']['offset'];assert source[x:y].decode()==name
        sig=source[y:v].decode();changes=[]
        for r in occurrences:
            x0,y0=r['start']['offset'],r['end']['offset']
            if any(ca<=x0 and y0<=cb for ca,cb,_ in cuts):continue
            text=source[x0:y0].decode();assert text in [name,full]
            changes.append((x0,y0,('checked_'+name if text==name else NS+'.checked_'+name).encode()))
        solution=solprefix+'\n'+edit(source,cuts+changes).decode()+'\n\nopen Polynomial '+NS+'\n\ntheorem solution'+sig+':= by\n  exact '+NS+'.checked_'+name+' '+ARGS[i]+'\n\n#print axioms solution\n'
        edits=[(x-a,y-a,full.encode())]
        if d['docstring']:
            doc=d['docstring'];edits.append((doc['start']['offset']-a,doc['end']['offset']-a,b''))
        formal=edit(source[a:v],edits).decode().strip()+':= by sorry'
        solpath='Solutions/Sol_ZetaNine_CoefficientMapConnection_'+name+'.lean'
        refpath='Theorems/Thm_ZetaNine_CoefficientMapConnection_'+name+'.lean'
        for rel,text in [(solpath,solution),(refpath,preamble+'\n'+formal+'\n')]:
            write(OUT/'staged'/rel,text);write(PROJECT/rel,text)
        targets.append(dict(theorem_name=full,local_solution=solpath,local_reference=refpath,wrapper_arguments=ARGS[i]))
        problems.append(dict(theorem_name=full,theorem_title=titles[i],formal_statement=formal,
            natural_language_statement=naturals[i],preamble=preamble,source=origin,tags=['number-theory','polynomials','formalization']))
        pt[full]=dict(declaration_fact=d,binding_fact=bs,target_refs=occurrences,
                      original_signature=sig,rename_edits=[[a,b,v.decode()] for a,b,v in changes],extra_hypotheses=[])
    dump(OUT/'target-plan.json',dict(definition='ZetaNine_CoefficientMapConnection',local_definition=DEF_PATH,targets=targets,existing_definitions=[]))
    dump(OUT/'definitions-request.json',[dict(definition_name='ZetaNine_CoefficientMapConnection',
        definition_title='The original polynomial D/H connection and genuine Fin15 coordinate map',
        definition=definition,natural_language_statement='Define the original rational polynomial coordinates u=t(t+n), v=t(t+n-1) for n>=1, D=(u-n-1)^10, the true H difference polynomial, actual Fin15 coordinate map, and original three-factor Z targets. The linear-map proof fields contain complete local linearity proofs. No kernel or bijectivity property is supplied as a premise.',
        source=origin,tags=['number-theory','polynomials','formalization'],env=REV,private=False)])
    dump(OUT/'problems-request.json',dict(env=REV,private=False,problems=problems))
    dump(OUT/'integration-provenance.json',dict(source_sha256=SOURCE_SHA,graph_records=len(c['graph']),
        source_declarations=39,source_defs=12,source_proofs=27,header=header,definition_facts=c['def_facts'],
        deleted_diagnostic_facts=diagnostics,actual_constructor_closure=provenance,targets=pt,
        cuts=[[a,b] for a,b,_ in cuts],actual_source_position_authority='Actual complete native Lean declaration graph, source and control parsers, and real Parser.parseHeader; no regex positions.',
        new_external_theorem_boundaries=[],actual_inline_parent_helpers=[]))
    compile_module('build-definition',DEF_PATH.removesuffix('.lean').replace('/','.'))
    compile_module('build-native-alias','NativeValueComparisonDefinition')
    run('native-value-comparison',['lean','native-value-comparison.lean'])
    compile_module('build-staged-alias','StagedValueComparisonDefinition')
    run('staged-value-comparison',['lean','staged-value-comparison.lean'])
    for i,t in enumerate(targets):
        for kind in ['solution','reference']:
            compile_module('build-'+str(i)+'-'+kind,t['local_'+kind].removesuffix('.lean').replace('/','.'))
    print('All actual parser-generated source closure and seven staged modules compiled.',flush=True)

def audits():
    c=context();plan=load(OUT/'target-plan.json')
    defnames=[NS+'.'+n for n in DEFS]
    contexts=[('original',NATIVE,[(n,n) for n in defnames]+[(NS+'.'+t,NS+'.'+t) for t in TARGETS]),
              ('definition',DEF_PATH.removesuffix('.lean').replace('/','.'),[(n,n) for n in defnames])]
    for i,t in enumerate(plan['targets']):
        contexts += [('types_'+str(i)+'_solution',t['local_solution'].removesuffix('.lean').replace('/','.'),[(n,n) for n in defnames]+[(t['theorem_name'],'solution')]),
                     ('types_'+str(i)+'_reference',t['local_reference'].removesuffix('.lean').replace('/','.'),[(n,n) for n in defnames]+[(t['theorem_name'],t['theorem_name'])])]
        proofs=[g['name'] for g in c['core'] if g['kind']=='theorem']
        proofs=[NS+'.checked_'+TARGETS[i] if n==t['theorem_name'] else n for n in proofs]+['solution']
        contexts += [('helpers_'+str(i),t['local_solution'].removesuffix('.lean').replace('/','.'),[(n,n) for n in proofs])]
    for label,module,names in contexts:
        code=emitter(module,names);write(OUT/(label+'.lean'),code);write(PROJECT/(label+'.lean'),code)
        run(label,['lean',label+'.lean'])
    # Exact native author source/control bytes are replayed against the complete
    # final solution using only actual header/ref token spans from real parsers.
    solution=plan['targets'][2]['local_solution'].removesuffix('.lean').replace('/','.')
    replacements={NS+'.'+TARGETS[2]:NS+'.checked_'+TARGETS[2]}
    reports=[]
    for label,snapshot,factsfile,originalfile,count in [
        ('stage-native-author','native-author-oracle-input.lean','native-author-sketch_info.jsonl',AUTHOR/'type-audit.lean',39),
        ('stage-native-boundary','native-boundary-oracle-input.lean','native-boundary-sketch_info.jsonl',AUTHOR/'boundary-audit.lean',12)]:
        data=(OUT/snapshot).read_bytes();assert data==originalfile.read_bytes()
        facts=rows(OUT/factsfile)
        # The recorded actual command spans identify the one native import.
        importfacts=[f for f in facts if f['kind']=='command' and f['syntaxKind']=='Lean.Parser.Module.import']
        # Header parsing is required because Stage2 emits body commands only.
        copied=label+'-original.lean';write(PROJECT/copied,data)
        run(label+'-header',['lean','--run','extract_header.lean',copied],label+'-header.jsonl')
        header=rows(OUT/(label+'-header.jsonl'))[0];he=header['end']['offset']
        assert data[:he].decode().strip().splitlines()==['import '+NATIVE,'import Lean']
        changes=[(0,he,('import '+solution+'\nimport Lean\n').encode())]
        used=[]
        for r in facts:
            if r['kind']!='ref' or r['const'] not in replacements:continue
            a,b=r['start']['offset'],r['end']['offset'];old=data[a:b].decode()
            full=r['const'];name=full.rsplit('.',1)[1]
            assert old in [name,full]
            new=replacements[full] if old==full else replacements[full].rsplit('.',1)[1]
            changes.append((a,b,new.encode()));used.append(r)
        if label=='stage-native-author':
            # The original meta audit quotes names; those Name literals are
            # data, not resolved term references, and must not be represented
            # as oracle reference spans. Generate a fresh getConstInfo audit
            # from the actual 39 source graph records and explicit target map.
            names=[g['name'] for g in c['core']]
            text=emitter(solution,[(n,replacements.get(n,n)) for n in names]).encode()
            provenance=dict(actual_header=header,actual_source_graph_names=names,
                reference_span_edits_claimed=False,
                semantic_name_mapping=replacements,
                original_sha256=digest(data),staged_sha256=digest(text))
        else:
            assert used, 'Actual target references must be found and remapped.'
            text=edit(data,changes)
            provenance=dict(actual_header=header,actual_target_refs=used,
                edits=[[a,b,v.decode()] for a,b,v in changes],original_sha256=digest(data),staged_sha256=digest(text))
        write(OUT/(label+'.lean'),text);write(PROJECT/(label+'.lean'),text)
        dump(OUT/(label+'-provenance.json'),provenance)
        run(label,['lean',label+'.lean']);rs=rows(OUT/(label+'.log'));assert len(rs)==count
        reports.append(dict(label=label,records=rs,actual_exit_code=0))
    dump(OUT/'stage-boundary-report.json',dict(runs=reports,all_zero=True,records=51))
    # An actual findOLean probe binds native and all seven stage import objects
    # to this fresh cache, rather than merely assuming the selected search path.
    modules=[NATIVE,DEF_PATH.removesuffix('.lean').replace('/','.')]+[t['local_'+kind].removesuffix('.lean').replace('/','.') for t in plan['targets'] for kind in ['solution','reference']]
    probe='import Lean\nopen Lean\nrun_meta do\n  for n in ['+', '.join('`'+m for m in modules)+'] do\n    let p ← findOLean n\n    IO.println (Json.mkObj [("module",toJson n.toString),("olean",toJson p.toString)]).compress\n'
    write(OUT/'resolution-audit.lean',probe);write(PROJECT/'resolution-audit.lean',probe)
    run('resolution-audit',['lean','resolution-audit.lean'])
    print('Actual type, complete-proof, closed boundary and module-resolution audits finished.',flush=True)

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser()
    parser.add_argument('phase',choices=['configure','oracles','stage','audits'])
    parser.add_argument('--lane-granted',action='store_true')
    args=parser.parse_args()
    if args.phase=='configure':configure();return
    assert args.lane_granted, 'Explicit parent Lean lane grant is required.'
    {'oracles':oracles,'stage':stage,'audits':audits}[args.phase]()

if __name__=='__main__':main()
