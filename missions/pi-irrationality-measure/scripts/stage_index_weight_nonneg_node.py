"""Pure source-faithful AP21 leaf staging; three new contexts and one actual reused stub."""
from __future__ import annotations
import argparse,hashlib,json
from pathlib import Path
import validate_namespace_context_providers as context

TASK=Path(__file__).resolve().parents[1];ROOT=TASK.parents[1];V=TASK/'verification'
SELF=Path(__file__).resolve();CONSUMER=TASK/'scripts/certify_index_weight_nonneg_node.py'
STAGE=V/'ap21/index-weight-nonneg-node'
TARGET='OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg';THEOREM_ID='0aeabe86-ff79-46b4-b8e3-eacc0125c4e4'
MODULE='Theorems.Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg'
SOLUTION_MODULE='Solutions.Sol_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg_ap21'
TARGET_OUTPUT=MODULE.replace('.','/')+'.lean';SOLUTION_OUTPUT=SOLUTION_MODULE.replace('.','/')+'.lean'
HELPERS=['OAI.PiExponent.DeterminantContradiction.logWeights_eq','OAI.PiExponent.LiteralAnalytic.fixedWeights_pos']
NAMES=HELPERS+[TARGET];ROUTE=V/'ap20/analytic-small-leaf-candidates/indexWeight_nonneg/source-route.json'
GRAPH_STAGE=V/'ap20/analytic-translated-two-layer-reduction-final-v3'
PUBLICATION=GRAPH_STAGE/'publication-v4/publication.json'
COMMIT='adc7f1241b42e322a6451854ab7e4b4c146bf78a';ENV='0df444a360eaa60ab8c11dca51a86af692955474'
CORE=V/'TypeOnlyTheoremSnapshotCore.inc';RUNTIME=V/'lean-runtime.json'
RUNNER=TASK/'scripts/preflight_staged_module_windows_bounded.py';LEGACY_RUNNER=TASK/'scripts/preflight_staged_module.py'
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
SOURCE_SNAPSHOT='SourceTypeAndRefsSnapshot.lean';GENERATED_SNAPSHOT='GeneratedSnapshot.lean'
SOURCE_JSON='source-actual-CIs.json';GENERATED_JSON='generated-actual-CIs.json'
SOURCE_INVENTORY='source-owned-CI-inventory.json';GENERATED_INVENTORY='generated-owned-CI-inventory.json'
CERTIFICATE=STAGE/'node-validation.json'
FILES=[SOURCE_SNAPSHOT,TARGET_OUTPUT,SOLUTION_OUTPUT,GENERATED_SNAPSHOT]
MODES=['modecheck','emit-olean','emit-olean','modecheck']
DATA_STAGE=V/'ap20/literal-interface-data';DATA_CERT=DATA_STAGE/'actual-provider-validation.json'
DATA_PUB=DATA_STAGE/'publication/publication.json'
DATA_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData'
BASELINE=V/'ap20/analytic-translated-graph-route/actual-Published31-Accepted-boundaries.json'
COVERAGE=V/'ap20/analytic-translated-graph-route/report.json'
TYPE_AUDIT=GRAPH_STAGE/'type-import-closure-audit.json'

def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def digest(raw):return hashlib.sha256(raw).hexdigest()
def sha(p):return digest(Path(p).read_bytes())
def encode(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def rel(p):return Path(p).resolve().relative_to(TASK.resolve()).as_posix()
def ws(p):return Path(p).resolve().relative_to(ROOT.resolve()).as_posix()
def need(ok,msg):
    if not ok:raise ValueError(msg)

PROBE=r'''
namespace IndexWeightActualCI
open Lean Meta

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]?.getD env.mainModule).toString
  | none => env.mainModule.toString

def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | .opaqueInfo o => some o.value
  | _ => none

def refs (e : Expr) : Array String :=
  (e.getUsedConstants.map Name.toString).qsort (· < ·)

def row (n : Name) : MetaM Json := do
  let ci ← getConstInfo n
  let v := valueOf ci
  let tr := refs ci.type
  let vr := v.map refs |>.getD #[]
  let used := ((tr ++ vr).toList.eraseDups.toArray).qsort (· < ·)
  let kind := match ci with
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .ctorInfo _ => "constructor"
    | .inductInfo _ => "inductive"
    | .recInfo _ => "recursor"
    | .axiomInfo _ => "axiom"
    | .quotInfo _ => "quotient"
  return Json.mkObj [
    ("name",toJson n.toString),("actualOwner",toJson (owner (← getEnv) n)),
    ("privateUserName",toJson ((privateToUserName? n).map Name.toString)),
    ("kind",toJson kind),("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("type",PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value",if kind == "def" then v.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null else Json.null),
    ("closedType",toJson (!ci.type.hasMVar && !ci.type.hasFVar && !ci.type.hasLooseBVars)),
    ("closedValue",toJson (!v.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars))),
    ("isProp",toJson (← isProp ci.type)),("typeRefs",toJson tr),("valueRefs",toJson vr),
    ("allUsedConstants",toJson used),
    ("axioms",toJson ((← collectAxioms n).map Name.toString |>.qsort (· < ·)))]

def inventory (anchors : Array Name) (output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let mut indices : Std.HashSet Nat := {}
  for n in anchors do
    let some i := env.getModuleIdxFor? n | throwError "Inventory anchor has no actual imported owner: {n}"
    indices := indices.insert i.toNat
  let mut names : Array Name := #[]
  -- Inspect every constant. Only matching ModuleIdx entries incur name/type work.
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if indices.contains i.toNat then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do rows := rows.push (← row n)
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("inventorySelection",toJson "all constants, imported ModuleIdx first"),
    ("anchorNames",toJson (anchors.map Name.toString)),("rawOwnedNames",toJson (names.map Name.toString)),
    ("rawOwnedCIs",Json.arr rows)]).compress
  return names

def proofClosure (roots boundaries : Array Name) : MetaM (Array Json) := do
  let env ← getEnv
  let mut owned : Std.HashSet Nat := {}
  for n in roots do
    if let some i := env.getModuleIdxFor? n then owned := owned.insert i.toNat
  let mut queue := roots
  let mut seen : Std.HashSet Name := {}
  let mut result : Array Json := #[]
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    if seen.contains n then continue
    seen := seen.insert n
    let ci ← getConstInfo n
    let .thmInfo t := ci | throwError "Proof closure root is not an actual theorem: {n}"
    result := result.push (← row n)
    for r in ci.type.getUsedConstants ++ t.value.getUsedConstants do
      if boundaries.contains r then continue
      let project := (privateToUserName r).toString.startsWith "OAI."
      let localOwner := (env.getModuleIdxFor? r).any (fun i => owned.contains i.toNat)
      if project || localOwner then
        if let some (.thmInfo _) := env.find? r then queue := queue.push r
  return result.qsort (fun a b =>
    (a.getObjValAs? String "name").toOption.getD "" < (b.getObjValAs? String "name").toOption.getD "")

def exportSource (roots boundaries : Array Name) (inventoryPath output : String) : MetaM Unit := do
  let _ ← inventory roots inventoryPath
  let rows ← proofClosure roots boundaries
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("side",toJson "source"),
    ("probeMainModule",toJson (← getEnv).mainModule.toString),("rootNames",toJson (roots.map Name.toString)),("boundaryNames",toJson (boundaries.map Name.toString)),
    ("rows",Json.arr rows)]).compress

def exportGenerated (helpers boundaries : Array Name) (inventoryPath output : String) : MetaM Unit := do
  let names ← inventory #[`solution] inventoryPath
  let mut roots : Array Name := #[]
  for helper in helpers do
    let actual := names.filter (fun n => privateToUserName? n == some helper)
    unless actual.size == 1 do throwError "Private helper has no unique actual compiler CI: {helper}"
    roots := roots.push actual[0]!
  roots := roots.push `solution
  let rows ← proofClosure roots boundaries
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("side",toJson "generated"),
    ("probeMainModule",toJson (← getEnv).mainModule.toString),("rootNames",toJson (roots.map Name.toString)),("boundaryNames",toJson (boundaries.map Name.toString)),
    ("sourceHelperNames",toJson (helpers.map Name.toString)),("rows",Json.arr rows),
    ("comparatorCI",← row `OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg)]).compress
end IndexWeightActualCI
'''

def history(rec,pins,external):
    d=rec['data'];need(d['success'] and not d['timed_out'] and d['exit_code']==0 and d['seconds']<=300,'Historical context was not genuinely bounded PASS')
    for key,before,after in [('source','source_sha256_before','source_sha256_after'),('manifest','manifest_sha256_before','manifest_sha256_after')]:
        p=context.file(d[key]);need(sha(p)==d[before]==d[after],'Historical before/after mismatch');pins[rel(p)]=sha(p)
    p=context.file(d['log']);need(sha(p)==d['log_sha256']==d['stdout_and_stderr_sha256'],'Historical log changed');pins[rel(p)]=sha(p)
    p=context.file(rec['record']);need(sha(p)==rec['record_sha256'],'Historical sidecar changed');pins[rel(p)]=sha(p)
    for row in d['dependency_oleans']:
        p=Path(row['path']);need(row['stable_during_compile'] and sha(p)==row['sha256_before']==row['sha256_after'],'Historical dependency OLean changed')
        try:pins[rel(p)]=sha(p)
        except ValueError:external[str(p)]=sha(p)
    if d['output_olean']:
        p=context.file(d['output_olean']);need(sha(p)==d['output_olean_sha256'],'Historical emitted OLean changed');pins[rel(p)]=sha(p)

def staged_files():
    route=read(ROUTE);pub=read(PUBLICATION);witness=pub['readbacks']['norm-child-'+TARGET];body=witness['body']
    need(witness['http_status']==200 and body['theorem_id']==THEOREM_ID and body['theorem_name']==TARGET and body['status']=='Open'
      and body['mathlib_rev']==ENV and body['visibility']=='public' and body['deprecated_at'] is None,'Genuine exact Open public target differs')
    wire=(body['preamble']+body['formal_statement']).encode();units=route['source_units']
    need(route['closure_order']==NAMES and route['proof_AST_count']==3 and route['source_line_count']==12 and not route['missing_data_names'] and not route['finite_port_adaptations'] and not route['uses_unProved_platform_boundaries'],'Original source three-unit closure differs')
    pins={rel(p):sha(p) for p in [SELF,CONSUMER,ROUTE,PUBLICATION,CORE,RUNTIME,RUNNER,LEGACY_RUNNER,TYPE_AUDIT,GRAPH_STAGE/'preparation.json',DATA_CERT,DATA_PUB,DATA_STAGE/'preparation.json',BASELINE,COVERAGE]};external={};files={TARGET_OUTPUT:wire}
    commands=[];original_units=[];source_modules=[];solution=body['preamble'].encode()
    for u in units:
        raw=(TASK/u['source']).read_bytes();original=(TASK/u['original']).read_bytes();cmd=raw[u['start']:u['end']]
        need(sha(TASK/u['source'])==u['source_sha256'] and sha(TASK/u['original'])==u['original_sha256'] and digest(cmd)==u['command_sha256'] and original.replace(b'\r\n',b'\n').count(cmd.replace(b'\r\n',b'\n'))==1,'Original/source AST hash mismatch: '+u['name'])
        for p in [TASK/u['source'],TASK/u['original']]:pins[rel(p)]=sha(p)
        f='source-units/'+u['name'].replace('.','_')+'.lean.txt';files[f]=cmd
        f='original-normalized-units/'+u['name'].replace('.','_')+'.lean.txt';files[f]=cmd.replace(b'\r\n',b'\n')
        original_units.append(u)
        if u['source_module'] not in source_modules:source_modules.append(u['source_module'])
        local=u['name'].rsplit('.',1)[1];needle=('theorem '+local).encode();need(cmd.count(needle)==1,'Exact theorem binding differs')
        if u['name'] in HELPERS:
            ns=u['name'].rsplit('.',1)[0];solution+=('\nnamespace '+ns+'\n'+'\n'.join(u['contexts'])+'\n').encode()+cmd.replace(needle,b'private '+needle,1)+('\nend '+ns+'\n').encode()
        else:solution+=b'\n'+cmd.replace(needle,b'theorem solution',1)+b'\n'
    files[SOLUTION_OUTPUT]=solution
    cert=read(DATA_CERT);dp=read(DATA_PUB);need(cert['validated'] and cert['Std3_only'] and dp['definition_id']==dp['target_readback']['body']['theorem_id']=='20a36293-ad9b-41de-b2a1-463e0f7f0094' and dp['last_publish_verdict']['body']['status']=='PUBLISHED' and dp['target_readback']['body']['definition'].encode()==(DATA_STAGE/(DATA_MODULE.replace('.','/')+'.lean')).read_bytes(),'Actual Published seventeen-Def boundary differs')
    data_prep=read(DATA_STAGE/'preparation.json');pins.update(data_prep['input_hashes']);external.update(data_prep['external_dependency_olean_hashes']);pins.update(cert['implementation_hashes']);pins.update(cert['output_json_sha256'])
    for rec in cert['preflights'].values():history(rec,pins,external)
    for p in [TASK/cert['provider_olean'],DATA_STAGE/(DATA_MODULE.replace('.','/')+'.lean')]:pins[rel(p)]=sha(p)
    need(sha(TASK/cert['provider_olean'])==cert['provider_olean_sha256'],'Certified Definition OLean differs')
    coverage=read(COVERAGE)['actual_Published31_coverage'];need(len(coverage)==31,'Immutable actual Published31 baseline differs')
    covered=set(cert['provided_names']);records=[]
    for r in coverage:
        p=TASK/r['publication_record'];need(sha(p)==r['publication_record_sha256'],'Published baseline record changed');d=read(p);b=d['target_readback']['body']
        need(b['theorem_id']==r['definition_id'] and b['status']=='Definition' and b['mathlib_rev']==ENV and b['visibility']=='public' and d['last_publish_verdict']['body']['status']=='PUBLISHED','Actual prior Published Definition identity differs')
        pins[rel(p)]=sha(p);covered.update(r['actual_source_graph_names']);records.append(r)
    records.append({'definition_id':dp['definition_id'],'publication_record':rel(DATA_PUB),'publication_record_sha256':sha(DATA_PUB),'actual_source_graph_names':cert['provided_names']})
    need(len({r['definition_id'] for r in records})==32,'Actual Published32 coverage not unique')
    files['actual-Published32-coverage.json']=encode({'definition_count':32,'records':records,'provided_source_graph_names':sorted(covered),'mutable_progress_counter_used':False})
    graph={r['name']:r for r in map(json.loads,(V/'decl_graph.jsonl').read_text(encoding='utf-8').splitlines())}
    todo=list(NAMES);seen=set();boundaries=set()
    while todo:
        n=todo.pop()
        if n in seen:continue
        seen.add(n);g=graph[n]
        if n in covered:boundaries.add(n)
        elif n not in NAMES:need(False,'Missing source-faithful public data or inline proof: '+n)
        todo.extend(g['typeDeps']+(g['valueDeps'] if g['kind']!='theorem' or n in NAMES else []))
    boundary_names=sorted(boundaries)
    audit=read(TYPE_AUDIT);row=next(r for r in audit['rows'] if r['name']==TARGET);need(not row['missing_data_CIs'],'Actual source target type/import domain is incomplete')
    old_plan=read(GRAPH_STAGE/'preparation.json');old=old_plan['reused_actual_contexts'][TARGET_OUTPUT]
    need((TASK/old['source']).read_bytes()==wire,'Public wire differs from genuine historical comparator emitter')
    rec=context.record(TASK/old['source'],TASK/old['manifest'],'emit-olean',MODULE,TASK/old['root']);need(rec==old['preflight'],'Historical target stub witness differs');history(rec,pins,external)
    core=CORE.read_bytes()
    for side in ['source','generated']:
        filename=SOURCE_SNAPSHOT if side=='source' else GENERATED_SNAPSHOT
        imports=['Lean']+(source_modules if side=='source' else [MODULE,SOLUTION_MODULE])
        inventory=SOURCE_INVENTORY if side=='source' else GENERATED_INVENTORY;output=SOURCE_JSON if side=='source' else GENERATED_JSON
        names=NAMES if side=='source' else HELPERS
        call='exportSource' if side=='source' else 'exportGenerated'
        suffix=('\nrun_meta do\n  IndexWeightActualCI.'+call+' #['+', '.join('`'+n for n in names)+'] #['+', '.join('`'+n for n in boundary_names)+'] '+json.dumps(ws(STAGE/inventory))+' '+json.dumps(ws(STAGE/output))+'\n').encode()
        if side=='generated':suffix+=b'#print axioms solution\n'
        else:suffix+=(''.join('#print axioms '+n+'\n' for n in NAMES)).encode()
        files[filename]=(''.join('import '+m+'\n' for m in imports)+'\nset_option maxRecDepth 100000\n\n').encode()+core+b'\n'+PROBE.encode()+suffix
    plan={'schema_version':1,'artifact_kind':'ap21-indexWeight-nonneg-source-faithful-closed-node-preparation','source_commit':COMMIT,'source_units':original_units,'original_AST_count':3,'original_source_lines':12,'private_visibility_prefix_only':True,'target_binding_only_solution_rename':True,'finite_port_adaptations':[],
      'target':TARGET,'theorem_id':THEOREM_ID,'public_target_readback_key':'norm-child-'+TARGET,'public_wire_sha256':digest(wire),'preamble':body['preamble'],'formal_statement':body['formal_statement'],'helpers':HELPERS,'source_modules':source_modules,
      'Published32_coverage_sha256':digest(files['actual-Published32-coverage.json']),'actual_target_type_import_closure':row,'data_certificate_sha256':sha(DATA_CERT),'data_definition_id':dp['definition_id'],'data_provider_olean':cert['provider_olean'],'data_provider_olean_sha256':cert['provider_olean_sha256'],
      'historical_comparator_context':old,'total_actual_context_count':4,'new_bounded_context_count':3,'reused_actual_context_count':1,'finite_metadata_maxRecDepth':100000,'complete_raw_owned_inventory_before_classification':True,'source_and_generated_data_boundary_names':boundary_names,'source_graph_complete_type_and_Def_value_dependency_domain':sorted(seen),'published_data_values_not_retraversed_by_proof_closure':True,
      'input_hashes':pins,'external_dependency_olean_hashes':external,'files':{},'commands':commands,'validated':False,'closed_proof_verified':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False}
    for i,(f,mode) in enumerate(zip(FILES,MODES,strict=True),1):
        imports=[l[7:].strip() for l in files[f].decode().splitlines() if l.startswith('import ')]
        plan['files'][f]={'sha256':digest(files[f]),'mode':mode,'imports':imports,'manifest':old['manifest'] if i==2 else f'c{i}.json','actual_context_reused':i==2}
        if i==2:continue
        files[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap21-indexWeight-nonneg-bounded-manifest','output':ws(STAGE/f),'output_sha256':digest(files[f]),'imports':imports,'input_hashes':pins,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'validated':False,'submission_ready':False})
        commands.append('& '+repr(PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap21/index-weight-nonneg-node/'+f+' --root ap21/index-weight-nonneg-node --imports-manifest ap21/index-weight-nonneg-node/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    files['preparation.json']=encode(plan);files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def write_exact(outputs,write):
    for f,raw in outputs.items():
        p=STAGE/f
        if p.exists():need(p.read_bytes()==raw,'Refusing changed frozen artifact: '+f)
        elif write:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
        else:need(False,'Missing prepared artifact: '+f)
    return {'files':len(outputs),'new_contexts':3,'actual_reused_contexts':1,'validated':False,'Lean_started':False,'API_used':False}
def check_only():return write_exact(staged_files(),False)
def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args();print(json.dumps(write_exact(staged_files(),a.prepare),indent=2))
if __name__=='__main__':main()
