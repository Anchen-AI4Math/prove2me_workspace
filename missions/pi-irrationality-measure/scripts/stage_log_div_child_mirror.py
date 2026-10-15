"""Pure original-name standard module mirror of the genuinely Accepted LogDiv leaf."""
from __future__ import annotations
import argparse, json
from pathlib import Path
import stage_collision_remainder_limit_route as route
import stage_selected_minor_clearing_bound_node as core

TASK, ROOT, V = route.TASK, route.data.ROOT, route.V
SELF = Path(__file__).resolve(); STAGE = V/'ap19/log-div-child-mirror'
TARGET, MODULE, OLD = route.PARENT, route.PARENT_MODULE, route.PARENT_STAGE
SOURCE_MODULE = 'OAI.NumberTheory.PiExponent.Polynomials.SimplexLog'
SOURCE = TASK/('port/lean/'+SOURCE_MODULE.replace('.','/')+'.lean')
ORIGINAL = TASK/('source/lean/'+SOURCE_MODULE.replace('.','/')+'.lean')
OUTPUT = MODULE.replace('.','/')+'.lean'
SOURCE_SNAPSHOT, GENERATED_SNAPSHOT = 'SourceSnapshot.lean', 'GeneratedSnapshot.lean'
SOURCE_TYPE_JSON, GENERATED_TYPE_JSON = 'source-types.json', 'generated-types.json'
SOURCE_REFS_JSON, GENERATED_REFS_JSON = 'source-proof-references.json', 'generated-proof-references.json'
INVENTORY_JSON, CERTIFICATE = 'actual-owned-CI-inventory.json', 'local-child-validation.json'
RUNNER = TASK/'scripts/preflight_staged_module_windows_bounded.py'
LEGACY_RUNNER = TASK/'scripts/preflight_staged_module.py'
CONSUMER = TASK/'scripts/certify_log_div_child_mirror.py'
read, sha, sha_bytes, encode, need, rel = route.read, route.sha, route.data.sha_bytes, route.encode, route.need, route.rel


def source_unit():
    route.source_units()  # Cheap literal Accepted boundary plus exact route provenance; no historical consumer replay.
    am = next(m for m in read(route.data.base.AST)['modules'] if m['module']==SOURCE_MODULE)
    sm = next(m for m in read(route.data.base.SCOPES)['modules'] if m['source']==SOURCE_MODULE.replace('.','/')+'.lean')
    u = next(u for u in am['units'] if TARGET in u['graph_names'])
    s = next(s for s in sm['declarations'] if s['verified_name']==TARGET)
    raw = SOURCE.read_bytes(); command = raw[157:1065]
    contexts = [raw[c['range']['start']['offset']:c['range']['end']['offset']].decode() for c in s['context_commands']]
    graph = next(r for r in map(json.loads,route.data.base.GRAPH.read_text(encoding='utf-8').splitlines()) if r['name']==TARGET)
    need(am['source_sha256']==sm['source_sha256']==sha(SOURCE)
         and [u['start']['offset'],u['end']['offset']]==[157,1065]
         and [u['start']['line'],u['end']['line']]==[10,28]
         and u['graph_names']==[TARGET] and u['graph_kinds']==['theorem']
         and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance']
         and contexts==['open Filter Topology','open scoped BigOperators']
         and s['namespace']=='OAI.PiExponent' and all(x['kind']=='namespace' for x in s['scope_stack'])
         and graph['typeDeps']==graph['valueDeps']==[]
         and ORIGINAL.read_bytes().replace(b'\r\n',b'\n').count(command.replace(b'\r\n',b'\n'))==1,
         'Original LogDiv AST/scope/empty project closure differs')
    historical = read(OLD/'validation.json'); pub = read(OLD/'publication.json'); body=pub['target_readback']['body']
    need(historical['validated'] is True and historical['kernel_types_equal'] is True
         and historical['standard_axioms_only'] is True and body['theorem_id']==pub['theorem_id']
         and body['mathlib_rev']=='0df444a360eaa60ab8c11dca51a86af692955474'
         and body['visibility']=='public' and body['deprecated_at'] is None,
         'Genuine Accepted LogDiv historical kernel/environment differs')
    old_sol=next(OLD.glob('Sol_*.lean')); old_thm=next(OLD.glob('Thm_*.lean'))
    need(MODULE=='Theorems.'+old_thm.stem, 'Standard Accepted module mismatch')
    imports=[x.removeprefix('import ').strip() for x in old_sol.read_text(encoding='utf-8').splitlines() if x.startswith('import ')]
    need(len(imports)==12 and len(set(imports))==12 and all(x.startswith('Mathlib.') for x in imports),
         'Historically actual LogDiv Mathlib import profile differs')
    return command,u,s,contexts,imports,pub


INVENTORY = r'''
namespace LogDivOwnedInventory
open Lean Meta FullRowMinorProofSnapshot
def exportInventory (target : Name) (moduleName output : String) : MetaM Unit := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? target | throwError "LogDiv target lacks imported owner"
  unless env.header.moduleNames[moduleIndex.toNat]?.map Name.toString == some moduleName do
    throwError "LogDiv standard imported owner differs"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Actual owned CI vanished"
    let value := valueOf ci
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | _ => "other"
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("kind",toJson kind),
      ("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("owner",← ownerOf env name),("levelParams",toJson (ci.levelParams.map Name.toString)),
      ("closedType",toJson (!ci.type.hasMVar && !ci.type.hasFVar && !ci.type.hasLooseBVars)),
      ("closedValue",toJson (value.map fun v => !v.hasMVar && !v.hasFVar && !v.hasLooseBVars)),
      ("isProp",toJson (← isProp ci.type)),("type",PiExponentInterfaceSnapshot.exprJson ci.type),
      ("typeRefs",toJson ((refs ci.type).map Name.toString)),
      ("valueRefs",toJson ((value.map refs |>.getD #[]).map Name.toString)),
      ("allUsedConstants",toJson ((value.map (fun v => refs (mkApp ci.type v)) |>.getD (refs ci.type)).map Name.toString)),
      ("axioms",toJson ((← Lean.collectAxioms name).map Name.toString |>.qsort (fun a b => a < b)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("mirrorModule",toJson moduleName),
    ("rawOwnedNames",toJson (names.map Name.toString)),("rawOwnedCIs",Json.arr rows)]).compress
end LogDivOwnedInventory
'''


def snapshot(side):
    source=side=='source'; module=SOURCE_MODULE if source else MODULE
    t=SOURCE_TYPE_JSON if source else GENERATED_TYPE_JSON; r=SOURCE_REFS_JSON if source else GENERATED_REFS_JSON
    prefix='import Lean\nimport '+module+'\n\n'+core.SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()+'\n'+core.base.ap8.PROBE+'\n'+core.PROBE+'\n'
    if not source: prefix+=INVENTORY+'\n'
    early='' if source else '  LogDivOwnedInventory.exportInventory `'+TARGET+' '+json.dumps(MODULE)+' '+json.dumps(core.workspace_rel(STAGE/INVENTORY_JSON))+'\n'
    return (prefix+'run_meta do\n'+early+'  let roots := #[`'+TARGET+']\n'
        +'  PiExponentInterfaceSnapshot.exportSnapshot roots '+json.dumps(core.workspace_rel(STAGE/t))+'\n'
        +'  SelectedMinorProofSnapshot.exportBundle '+json.dumps(side)+' '+json.dumps(core.workspace_rel(STAGE/r))+' roots #['+json.dumps(module)+'] #[]\n'
        +'#print axioms '+TARGET+'\n').encode()


def staged_files():
    command,u,s,contexts,imports,pub=source_unit()
    body=(''.join('import '+m+'\n' for m in imports)+'\nnamespace OAI.PiExponent\n\n'+'\n'.join(contexts)+'\n\n').encode()+command+b'\n\nend OAI.PiExponent\n'
    need(b'sorry' not in body and b'import Solutions.' not in body and body.count(b'theorem ')==1,
         'Single original public LogDiv proof mirror differs')
    paths=[SELF,CONSUMER,route.SELF,route.data.base.AST,route.data.base.SCOPES,route.data.base.GRAPH,route.data.base.OWNERS,
        SOURCE,ORIGINAL,OLD/'publication.json',OLD/'validation.json',OLD/'original-type.json',OLD/'generated-type.json',
        next(OLD.glob('Sol_*.lean')),next(OLD.glob('Thm_*.lean')),core.SNAPSHOT_CORE,Path(core.__file__),
        Path(core.base.ap8.__file__),RUNNER,LEGACY_RUNNER,core.RUNTIME]
    pins={rel(p):sha(p) for p in paths}; result={OUTPUT:body,SOURCE_SNAPSHOT:snapshot('source'),GENERATED_SNAPSHOT:snapshot('generated')};commands=[]
    for i,(f,imps,mode) in enumerate([(OUTPUT,imports,'emit-olean'),(SOURCE_SNAPSHOT,['Lean',SOURCE_MODULE],'modecheck'),(GENERATED_SNAPSHOT,['Lean',MODULE],'modecheck')],1):
        result[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap19-log-div-standard-child-bounded-manifest',
            'output':core.workspace_rel(STAGE/f),'output_sha256':sha_bytes(result[f]),'imports':imps,'input_hashes':pins,
            'runtime_sha256':sha(core.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,
            'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),
            'validated':False,'submission_ready':False})
        commands.append("& '"+route.data.PYTHON+"' scripts/preflight_staged_module_windows_bounded.py ap19/log-div-child-mirror/"+f+' --root ap19/log-div-child-mirror --imports-manifest ap19/log-div-child-mirror/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    result['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap19-log-div-original-name-closed-child-preparation',
        'source_commit':route.data.COMMIT,'source_module':SOURCE_MODULE,'platform_module':MODULE,'source_unit':u,'source_scope':s,
        'original_AST_units':1,'original_source_lines':19,'private_helper_names':[],'public_platform_boundary_names':[TARGET],
        'source_command_sha256':sha_bytes(command),'source_proof_suffix_sha256':sha_bytes(command[u['valueStart']['offset']-157:]),
        'all_original_proof_suffixes_unchanged':True,'raw_owned_inventory_exported_before_classification':True,
        'historical_Accepted_theorem_id':pub['theorem_id'],'historical_Accepted_proof_id':pub['submission_id'],
        'historical_accepted_publication_sha256':sha(OLD/'publication.json'),'input_hashes':pins,'compile_commands':commands,
        'validated':False,'submission_ready':False,'Lean_started':False,'API_used':False})
    result['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return result


def check_only():
    outputs=staged_files()
    for f,raw in outputs.items():need((STAGE/f).read_bytes()==raw,'Immutable LogDiv mirror differs: '+f)
    for i,f in enumerate([OUTPUT,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):
        m=read(STAGE/f'c{i}.json');core.base.runner.verify_manifest_inputs(m);core.base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(outputs),'validated':False,'Lean_started':False,'API_used':False}


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        outputs=staged_files()
        for f,raw in outputs.items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        for f,raw in outputs.items():need((STAGE/f).read_bytes()==raw,'Written LogDiv mirror differs: '+f)
        result={'prepared_files':len(outputs),'validated':False,'Lean_started':False,'API_used':False}
    else:result=check_only()
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
