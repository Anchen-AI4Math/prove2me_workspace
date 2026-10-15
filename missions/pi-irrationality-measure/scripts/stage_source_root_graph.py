"""Pure immutable staging of the original Main/Consequence three-parent sketch."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / 'verification'
STAGE = V / 'graph-source-root-20261011'
SELF = Path(__file__).resolve()
COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
AST = V / 'ast-unit-inventory.json'
SCOPES = V / 'ast-scope-inventory.json'
GRAPH = V / 'decl_graph.jsonl'
CORE = V / 'TypeOnlyTheoremSnapshotCore.inc'
RUNTIME = V / 'lean-runtime.json'
CONTEXT = TASK / 'scripts/validate_namespace_context_providers.py'
LOOKUP = V / 'source-root-exact-name-lookup-20261011T131753_707821Z.json'
CANONICAL = ROOT / 'Definitions/Def_OAI_PiExponent_ApproximationDefinitions.lean'
ROOT_ID = 'e717eef2-11b1-4b14-9789-65f52c0502e1'
ROOT_NAME = 'OAI.PiExponent.pi_eventual_lower_bound'
CONSEQUENCE = 'OAI.PiExponent.piEventualLowerBound_of_globalInterpolation'
DEFINITION_MODULE = 'Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData'
IMPORTS = ['Definitions.Def_OAI_PiExponent_ApproximationDefinitions', DEFINITION_MODULE]
PREAMBLE = ''.join('import '+x+'\n' for x in IMPORTS) + '\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction\n\n'
SOURCE_SNAPSHOT = 'SourceSnapshot.lean'
GENERATED_SNAPSHOT = 'GeneratedSnapshot.lean'
SOURCE_JSON = 'source-types.json'
GENERATED_JSON = 'generated-types.json'
ROOT_JSON = 'root-sketch-interface.json'
SOLUTION_FILE = 'Solutions/Sol_OAI_PiExponent_pi_eventual_lower_bound_source_root_graph.lean'
CERTIFICATE = 'actual-source-root-graph-validation.json'
CONFIGS = [
    {'key':'conditional', 'name':'OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate', 'source_module':'OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction', 'source_sha256':'74329150cc64ac655ee0ce56454519170ce15b4b58dfd85ba5a9ab850c740e53', 'range':[8308,9062], 'unit_sha256':'e423aecf7c1a794d42270a9a44338408b6fb9be11983b0a16a89dd7e1e333621', 'title':'The conditional interpolation and analytic determinant argument for pi', 'statement':r'Assume the global interpolation statement and the analytic aggregate statement for the original fixed admissible data. Then, for every real $\nu>2$, there is an integer $Q\ge2$ such that every $p\in\mathbb Z$ and $q\in\mathbb N$ with $q\ge Q$ satisfy\n\n$$q^{-\nu}\le\left|\pi-\frac pq\right|.$$\n\nThis is the conditional conclusion of the source determinant contradiction, with the original quantified interpolation and analytic hypotheses.'},
    {'key':'geometry', 'name':'OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation', 'source_module':'OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry', 'source_sha256':'e2971c28c9553c95ffd61a0d16baf55300b22acb681f917845f07e38f23528c6', 'range':[1945,2155], 'unit_sha256':'1103791ce3b55fbdbfcc99b200ef4bf9310cfc34a1e8c7900706e4639c6c7e69', 'title':'Global surjectivity of the original admissible interpolation matrix', 'statement':r'For every real $\nu>2$, every fixed admissible datum $d$, and every real lower height $L$, the original interpolation matrix $A_d(H)$ is surjective at some height $H\ge L$:\n\n$$\forall\nu>2\;\forall d\;\forall L\in\mathbb R\;\exists H\ge L,\quad\operatorname{Surjective}(A_d(H)).$$\n\nHere the matrix, its weighted row and column domains, and the fixed-data parameters are exactly those of the source global interpolation statement.'},
    {'key':'analytic', 'name':'OAI.PiExponent.LiteralAnalytic.analyticAggregate', 'source_module':'OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate', 'source_sha256':'65bdf23dab0f6e8364d9e498718f0896b08910dbf83d6dafcf014c4c3112283e', 'range':[4686,4986], 'unit_sha256':'221c3211d696cf29be1ec4450fa1949a6ecdf5327a4c20f224e12f4c6e379ed3', 'title':'The original analytic aggregate bound for admissible selected minors', 'statement':r'For every real $\nu>2$ and fixed admissible datum $d$, there is an error $e_d(H)\to0$ as $H\to+\infty$. Eventually, every selected minor $D$ with nonzero determinant satisfies\n\n$$\frac{\log\|\det D\|}{M_d(H)H}\le a_d+e_d(H)+\max\{-\gamma_d(H),-\nu[A_d(1-\eta_d)-b_d(H)]\}.$$\n\nHere $M_d(H)$ is the row count, $a_d$ the analytic error parameter, $\gamma_d(H)$ the collision rate, $A_d$ and $\eta_d$ the fixed-data parameters, and $b_d(H)$ the normalized weighted row mean. The bound is uniform over the original column selections and is precisely the source analytic aggregate statement.'},
]
for c in CONFIGS:
    c['file'] = 'Theorems/Thm_' + c['name'].replace('.', '_') + '.lean'
    c['module'] = c['file'][:-5].replace('/', '.')
NAMES = [c['name'] for c in CONFIGS]
PUBLICATION_RECORDS = [V/'ap10/interpolation/publication/publication.json', V/'ap10/arithmetic/publication/publication.json', V/'ap10/determinant/publication-helper-v2/publication.json']

def need(ok, message):
    if not ok: raise ValueError(message)
def read(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(p): return sha_bytes(Path(p).read_bytes())
def encode(x): return (json.dumps(x, ensure_ascii=False, indent=2)+'\n').encode('utf-8')
def rel(p): return Path(p).resolve().relative_to(TASK.resolve()).as_posix()
def workspace_rel(p): return Path(p).resolve().relative_to(ROOT.resolve()).as_posix()
def verification_rel(p): return Path(p).resolve().relative_to(V.resolve()).as_posix()

def authority(name, expected_module=None, expected_sha=None, expected_range=None, expected_unit=None):
    modules = read(AST)['modules']
    pairs = [(m,u) for m in modules for u in m['units'] if name in u['graph_names']]
    need(len(pairs)==1, 'Ambiguous authoritative AST: '+name)
    m,u = pairs[0]; module=m['module']
    source=TASK/('port/lean/'+module.replace('.', '/')+'.lean')
    original=TASK/('source/lean/'+module.replace('.', '/')+'.lean')
    raw=source.read_bytes(); start=u['start']['offset']; end=u['end']['offset']; unit=raw[start:end]
    need(sha(source)==m['source_sha256'] and u['graph_names']==[name] and u['graph_kinds']==['theorem'] and u['privateTok'] is None, 'Source/AST changed: '+name)
    need(expected_module is None or module==expected_module, 'Owner module changed')
    need(expected_sha is None or sha(source)==expected_sha, 'Pinned source changed')
    need(expected_range is None or [start,end]==expected_range, 'AST range changed')
    need(expected_unit is None or sha_bytes(unit)==expected_unit, 'AST unit changed')
    need(original.read_bytes().replace(b'\r\n',b'\n').count(unit.replace(b'\r\n',b'\n'))==1, 'Original/port AST command differs')
    sm=next(x for x in read(SCOPES)['modules'] if x['source']==module.replace('.','/')+'.lean')
    scope=next(x for x in sm['declarations'] if x['verified_name']==name)
    need(sm['source_sha256']==sha(source), 'Source scope hash changed')
    rows=[json.loads(x) for x in GRAPH.read_text(encoding='utf-8').splitlines() if x.strip()]
    graph=next(x for x in rows if x['name']==name)
    return {'name':name,'module':module,'source':rel(source),'source_sha256':sha(source),'original':rel(original),'original_sha256':sha(original),'start':start,'end':end,'unit_sha256':sha_bytes(unit),'ast':u,'scope':scope,'graph':graph,'unit':unit}

PROBE = r'''
namespace SourceRootGraphSnapshot
open Lean Meta
def exportRows (names : Array Name) (owners : Array String) (output : String) (openTargets : Bool) : MetaM Unit := do
  let env ← getEnv
  unless names.size == owners.size do throwError "Snapshot owner domain differs"
  let mut rows : Array Json := #[]
  for i in [:names.size] do
    let name := names[i]!
    let some ci := env.find? name | throwError "Missing actual declaration: {name}"
    let .thmInfo info := ci | throwError "Expected theorem CI: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || info.value.hasMVar || info.value.hasFVar then
      throwError "Unclosed theorem CI: {name}"
    unless ← isProp ci.type do throwError "The theorem type is not Prop: {name}"
    let owner ← match env.getModuleIdxFor? name with
      | none => pure env.mainModule.toString
      | some idx => do
        let some m := env.header.moduleNames[idx.toNat]? | throwError "Invalid CI owner: {name}"
        pure m.toString
    unless owner == owners[i]! do throwError "Actual declaration owner differs: {name}"
    let axioms ← Lean.collectAxioms name
    let axioms := (axioms.map Name.toString).qsort (· < ·)
    for a in axioms do
      unless a == "propext" || a == "Classical.choice" || a == "Quot.sound" || (openTargets && a == "sorryAx") do
        throwError "Unexpected theorem axiom: {a}"
    if openTargets && !axioms.contains "sorryAx" then throwError "Expected Open placeholder/sketch dependency"
    let typeRefs := (ci.type.getUsedConstants.map Name.toString).qsort (· < ·)
    let valueRefs := (info.value.getUsedConstants.map Name.toString).qsort (· < ·)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", PiExponentInterfaceSnapshot.exprJson ci.type), ("value", Json.null),
      ("closedType", toJson true), ("closedValue", toJson true), ("isProp", toJson true),
      ("actualOwner", toJson owner), ("axioms", toJson axioms),
      ("typeRefs", toJson typeRefs), ("valueRefs", toJson valueRefs),
      ("Open_sketch_type_check", toJson openTargets)]
  IO.FS.writeFile output (Json.arr rows |>.compress)
end SourceRootGraphSnapshot
'''

def snapshot(names, owners, output, open_targets, imports, suffix=''):
    ns='#['+', '.join('`'+n for n in names)+']'
    os='#['+', '.join(json.dumps(x) for x in owners)+']'
    return (''.join('import '+x+'\n' for x in imports)+'\n'+CORE.read_text(encoding='utf-8').rstrip()+'\n'+PROBE+'\n'+suffix+'\nrun_meta do\n  SourceRootGraphSnapshot.exportRows '+ns+' '+os+' '+json.dumps(workspace_rel(STAGE/output))+' '+str(open_targets).lower()+'\n'+''.join('#print axioms '+n+'\n' for n in names)).encode('utf-8')

def stage_files():
    lookup=read(LOOKUP)
    need(lookup['read_only'] is True and [x['theorem_name'] for x in lookup['records']]==NAMES and all(x['http_status']==200 and x['matches']==[] and x['lookup_total']==0 for x in lookup['records']), 'Exact-name lookup differs')
    units=[authority(c['name'],c['source_module'],c['source_sha256'],c['range'],c['unit_sha256']) for c in CONFIGS]
    main=authority(ROOT_NAME, 'OAI.NumberTheory.PiExponent.Main','97b3c6c9901c4047c688cb7af4d55b42a500308a2616d525b0cb57879cf3b74a',[193,347],'61ec89aa9760955f3477dd32159e868968e1c8e24e1ad95b07ef13876e4dd8a3')
    consequence=authority(CONSEQUENCE,'OAI.NumberTheory.PiExponent.Approximation.InterpolationConsequence','c638533b4b7df971d47c7cc38391abb8674e43d9bf2d67e39188959280b5c4f4',[227,520],'551223dd919dc4eb5aaeff641ff17fd4c1a4be3a3314dc444d8b105c47501d43')
    generated={}; parents=[]; pins=[SELF,AST,SCOPES,GRAPH,CORE,RUNTIME,CONTEXT,Path(runner.__file__),LOOKUP]
    dependencies=[]
    for record_path in PUBLICATION_RECORDS:
        record=read(record_path); body=record['target_readback']['body']
        need(record['target_readback']['http_status']==200 and body['status']=='Definition' and body['visibility']=='public' and record['last_publish_verdict']['body']['status']=='PUBLISHED', 'Core Definition is not Published')
        need(body['definition']==record['publish_intent']['payload']['definition'], 'Published literal Definition differs')
        dependencies.append({'record':rel(record_path),'record_sha256':sha(record_path),'definition_id':record['definition_id'],'literal_body_sha256':sha_bytes(body['definition'].encode())})
        pins.append(record_path)
    for u in units+[main,consequence]:
        pins += [TASK/u['source'],TASK/u['original']]
        generated['source/'+u['name'].replace('.','_')+'.lean.txt']=u['unit']
    for c,u in zip(CONFIGS,units,strict=True):
        unit=u['unit']; ast=u['ast']; a=ast['nameRange']['start']['offset']-u['start']; b=ast['nameRange']['end']['offset']-u['start']; value=ast['valueStart']['offset']-u['start']
        need(unit[value:value+2]==b':=', 'Expected source theorem value delimiter')
        formal=unit[:a]+c['name'].encode()+unit[b:value]+b':= by\n  sorry\n'
        assembled=PREAMBLE.encode()+formal
        generated[c['file']]=assembled
        metadata={'title':c['title'],'statement':c['statement'].replace(r'\n\n','\n\n'),'tags':['number-theory','openai-pi-exponent-017'],'source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/'+c['source_module'].replace('.','/')+'.lean#L'+str(ast['start']['line'])+'-L'+str(ast['end']['line'])}
        generated['parents/'+c['key']+'/academic-metadata.json']=encode(metadata)
        generated['parents/'+c['key']+'/wire-theorem-source.lean']=assembled
        parents.append({**c,'preamble':PREAMBLE,'formal_statement':formal.decode(),'source_interface':{k:v for k,v in u.items() if k!='unit'},'target_sha256':sha_bytes(assembled),'metadata':metadata,'status':'Open','placeholder_semantics':'Open reference emitter; sorryAx intentional; not a closed proof','expected_olean':rel(runner.STAGED_LIB/Path(c['file']).with_suffix('.olean'))})
    source_imports=['Lean']+list(dict.fromkeys([c['source_module'] for c in CONFIGS]+[main['module']]))
    generated_imports=['Lean']+[c['module'] for c in CONFIGS]
    generated[SOURCE_SNAPSHOT]=snapshot(NAMES+[ROOT_NAME],[c['source_module'] for c in CONFIGS]+[main['module']],SOURCE_JSON,False,source_imports)
    mbody=main['unit'][main['ast']['valueStart']['offset']-main['start']:].decode().replace('\r\n','\n')
    cbody=consequence['unit'][consequence['ast']['valueStart']['offset']-consequence['start']:].decode().replace('\r\n','\n')
    need(mbody.strip()==':=\n  piEventualLowerBound_of_globalInterpolation AdmissibleMatrixInterpolation.globalInterpolation', 'Main reduction body changed')
    need(cbody.count('hgeometry')==1 and cbody.startswith(':=\n  DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate'), 'Consequence reduction body changed')
    body=cbody.replace('hgeometry','AdmissibleMatrixInterpolation.globalInterpolation')
    solution='theorem solution : PiEventualLowerBound '+body+'\n'
    root_imports=IMPORTS+[c['module'] for c in CONFIGS]
    root_preamble=''.join('import '+x+'\n' for x in root_imports)+'\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction\n\n'
    generated['root-sketch-wire.lean']=(root_preamble+solution).encode()
    generated[SOLUTION_FILE]=(root_preamble+solution).encode()
    generated_imports=['Lean']+root_imports
    # The combined generated snapshot checks all three imported target CIs and
    # the identical reduction solution body. The submission wire is modechecked
    # separately, with no exporter or filesystem effects in the submitted code.
    generated[GENERATED_SNAPSHOT]=snapshot(NAMES+['solution'],[c['module'] for c in CONFIGS]+['GeneratedSnapshot'],GENERATED_JSON,True,generated_imports,'open OAI.PiExponent OAI.PiExponent.DeterminantContradiction\n\n'+solution)
    files=[c['file'] for c in CONFIGS]+[SOURCE_SNAPSHOT,GENERATED_SNAPSHOT,SOLUTION_FILE]
    imports=[IMPORTS]*3+[source_imports,generated_imports,root_imports]
    modes=['emit-olean']*3+['modecheck']*3
    input_hashes={rel(p):sha(p) for p in pins}
    # Canonical file is outside the mission: preserve its literal bytes as an input.
    generated['canonical-approximation-definitions.lean.txt']=CANONICAL.read_bytes()
    rows={}; commands=[]
    for i,(filename,im,mode) in enumerate(zip(files,imports,modes,strict=True),1):
        mf=f'c{i}.json'; module=filename[:-5].replace('/','.')
        manifest={'schema_version':1,'artifact_kind':'source-root-graph-bounded-compiler-manifest','output':workspace_rel(STAGE/filename),'output_sha256':sha_bytes(generated[filename]),'imports':im,'input_hashes':input_hashes,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False}
        generated[mf]=encode(manifest)
        command='python scripts/preflight_staged_module.py '+verification_rel(STAGE/filename)+' --root '+verification_rel(STAGE)+' --imports-manifest '+verification_rel(STAGE/mf)+' --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else '')
        rows[filename]={'sha256':sha_bytes(generated[filename]),'manifest':mf,'mode':mode,'imports':im,'module':module}; commands.append(command)
    generated['preparation.json']=encode({'schema_version':1,'artifact_kind':'source-root-three-parent-sketch-preparation','source_commit':COMMIT,'root_id':ROOT_ID,'root_name':ROOT_NAME,'canonical_definition_sha256':sha(CANONICAL),'canonical_definition_workspace_path':workspace_rel(CANONICAL),'parents':parents,'source_interfaces':[{k:v for k,v in u.items() if k!='unit'} for u in [main,consequence]],'published_definition_dependencies':dependencies,'root_preamble':root_preamble,'root_solution':solution,'root_sketch_source_sha256':sha_bytes(generated[SOLUTION_FILE]),'root_sketch_file':SOLUTION_FILE,'source_snapshot_json':SOURCE_JSON,'generated_snapshot_json':GENERATED_JSON,'composition':'Substitute the original Main geometry argument for the single hgeometry argument in the original InterpolationConsequence proof body; no other proof expression changes.','target_owns_no_new_definition':True,'excluded_community_adapters_imported':False,'source_proof_values_exported':False,'Open_placeholders_emit_reference_oleans':True,'closed_proof':False,'expected_generated_axioms':'Std3 plus sorryAx because the three imported source obligations are Open','input_hashes':input_hashes,'files':rows,'compile_commands':commands,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    generated['compile-commands.txt']=('\n'.join(commands)+'\n').encode()
    return generated

def check_only():
    generated=stage_files()
    for filename,raw in generated.items(): need((STAGE/filename).is_file() and (STAGE/filename).read_bytes()==raw,'Immutable stage reconstruction differs: '+filename)
    p=read(STAGE/'preparation.json')
    for filename,row in p['files'].items():
        mf=read(STAGE/row['manifest']); runner.verify_manifest_inputs(mf); runner.verify_source_certificate(STAGE/filename,mf)
    need(sha(CANONICAL)==p['canonical_definition_sha256'],'Canonical Definition changed')
    return {'checked_files':len(generated),'all_hashes_match':True,'parents':NAMES,'root_id':ROOT_ID,'Open_sketch':True,'closed_proof':False,'validated':False,'Lean_started':False,'API_used':False,'compile_commands':p['compile_commands']}

def main():
    parser=argparse.ArgumentParser(description=__doc__); modes=parser.add_mutually_exclusive_group(required=True); modes.add_argument('--prepare',action='store_true'); modes.add_argument('--check-only',action='store_true'); args=parser.parse_args()
    if args.prepare:
        for filename,raw in stage_files().items():
            path=STAGE/filename
            if path.exists(): need(path.read_bytes()==raw,'Refusing to overwrite stage: '+filename)
            else: path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__': main()
