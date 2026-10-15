"""Pure AP20 exact seventeen original data commands, three bounded compiler contexts."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_analytic_remainder_data_provider as base
import stage_analytic_translated_graph_route as route
import validate_namespace_context_providers as context

TASK,ROOT,V,SELF=base.TASK,base.ROOT,base.V,Path(__file__).resolve()
STAGE=V/'ap20/literal-interface-data';COMMIT=base.COMMIT
PLATFORM_MODULE=route.DATA_MODULE;PROVIDER_FILE=PLATFORM_MODULE.replace('.','/')+'.lean'
CONFIGS=['interface'];REPORT=route.STAGE/'report.json';BASELINE=route.BASELINE
NAMES=base.read(REPORT)['minimal_new_definition_names']
IMPORTS=[m for m in base.read(REPORT)['candidate_imports'] if m!=PLATFORM_MODULE]
SOURCE_MODULES=list(dict.fromkeys(next(r['module'] for r in base.read(REPORT)['source_units'] if r['name']==n) for n in NAMES))
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT=base.SOURCE_SNAPSHOT,base.GENERATED_SNAPSHOT
SOURCE_JSON,GENERATED_JSON=base.SOURCE_JSON,base.GENERATED_JSON
INVENTORY_JSON='actual-owned-CI-inventory.json'
SOURCE_CACHES,GENERATED_CACHES='source-used-proof-CIs.json','generated-used-proof-CIs.json'
CORE,RUNTIME,RUNNER=base.CORE,base.base.RUNTIME,base.RUNNER
INVENTORY=V/'ap20/literal-interface-data-spec/OwnerIndexFirstInventory.inc'
CONSUMER=TASK/'scripts/certify_literal_analytic_interface_data_existing.py'
CERTIFICATE=STAGE/'actual-provider-validation.json'
ROW_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData'
REMAINDER_CERT=V/'ap19/analytic-remainder-auto-ci-validation-v5/actual-provider-validation-auto-ci-v5.json'
REMAINDER_PUB=V/'ap19/analytic-remainder-data/publication-v4/publication.json'
ROW_CERT=V/'ap14/row-data/actual-provider-validation.json';ROW_PUB=V/'ap14/row-data/publication/publication.json'
read,encode,sha,sha_bytes,need,rel,workspace_rel=base.read,base.encode,base.sha,base.sha_bytes,base.need,base.rel,base.workspace_rel
_BINDING=None

def config(key='interface'):
    need(key=='interface','Unknown provider key')
    return {'stage':STAGE,'platform_module':PLATFORM_MODULE,'provider_file':PROVIDER_FILE,'names':NAMES,'imports':IMPORTS,'source_modules':SOURCE_MODULES}

def authority():
    p=read(REPORT);need(p['source_commit']==COMMIT and len(NAMES)==17 and p['minimal_new_definition_source_lines']==49,'Frozen original17 route differs')
    owners={r['source_name']:r for r in read(base.base.OWNERS)['owners']};units=[]
    for n in NAMES:
        r=next(r for r in p['source_units'] if r['name']==n);s=TASK/r['source'];o=TASK/r['original'];raw=s.read_bytes()[r['start']:r['end']]
        need(sha(s)==r['source_sha256'] and sha(o)==r['original_sha256'] and sha_bytes(raw)==r['command_sha256']
             and r['ast']['graph_names']==[n] and r['ast']['graph_kinds']==['def'] and r['finite_source_port_version_adaptation'] is None
             and o.read_bytes().replace(b'\r\n',b'\n').count(raw.replace(b'\r\n',b'\n'))==1,'Original Def AST/bytes differ: '+n)
        need([s.read_bytes()[c['range']['start']['offset']:c['range']['end']['offset']].decode() for c in r['scope']['context_commands']]==r['contexts'], 'Exact source contexts differ: '+n)
        units.append(dict(r,bytes=raw,owner=owners[n],source_module=r['module']))
    return units

def historical(record,pins,external):
    """Check actual old compiler source/manifest/log against recorded before/after hashes."""
    need(sha(TASK/record['record'])==record['record_sha256'] and read(TASK/record['record'])==record['data'],'Historical sidecar changed')
    pins[record['record']]=record['record_sha256'];d=record['data']
    need(d['success'] is True and d['exit_code']==0 and d['timed_out'] is False and 0<d['seconds']<=300
         and d['source_unchanged'] and d['manifest_unchanged'] and d['runtime_unchanged'] and d['dependencies_stable_during_compile'], 'Historical compiler witness was not bounded/stable')
    for k in ['source','manifest']:
        path=context.file(d[k]);h=sha(path)
        need(h==d[k+'_sha256_before']==d[k+'_sha256_after'],'Historical '+k+' differs from actual before/after witness')
        pins[rel(path)]=h
    path=context.file(d['log']);h=sha(path)
    need(h==d['log_sha256']==d['stdout_and_stderr_sha256'],'Historical compiler log differs')
    pins[rel(path)]=h
    need(d['manifest_input_hashes_before']==d['manifest_input_hashes_after'],'Historical compiler inputs drifted')
    for dep in d['dependency_oleans']:
        need(dep['stable_during_compile'] and dep['sha256_before']==dep['sha256_after']==sha(Path(dep['path'])),'Historical dependency OLean differs')
        path=Path(dep['path'])
        try:pins[rel(path)]=dep['sha256_before']
        except ValueError:external[str(path)]=dep['sha256_before']
    if d['output_olean'] is not None:
        path=context.file(d['output_olean']);need(sha(path)==d['output_olean_sha256'],'Historical emitted OLean differs');pins[rel(path)]=sha(path)

def inherited_binding():
    global _BINDING
    if _BINDING is not None:
        doc,pins,external=_BINDING
        for p,h in pins.items():need(sha(TASK/p)==h,'Fixed dependency evidence changed: '+p)
        for p,h in external.items():need(sha(Path(p))==h,'Fixed external OLean changed: '+p)
        return doc,dict(pins),dict(external)
    core,pins=base.inherited_binding();external=dict(base._CORE_CACHE[2])
    pair=core['certified_actual_helper_pair']
    for rec in list(core['preflights'].values())+[v['preflight'] for v in pair['actual_witnesses'].values()]:historical(rec,pins,external)
    need(sha(REMAINDER_CERT)=='85ee5785a8dee831f8d008886fdf8da3860f95b26fb5c4173f549bc79cbf9174','Genuine AP19 six-CI certificate changed')
    remainder=read(REMAINDER_CERT);row=read(ROW_CERT)
    need(remainder['validated'] and remainder['Std3_only'] and remainder['primary_Def_full_types_values_equal'] and len(remainder['actual_owned_CI_names'])==6
         and len(remainder['actual_source_generated_closed_Prop_autoCI_pairs'])==2,'AP19 exact actual six-CI evidence differs')
    need(row['validated'] and row['Std3_only'] and row['definition_values_equal_and_exported'] and row['platform_module']==ROW_MODULE,'Actual RowTranslation full-Def witness differs')
    for cert,path,pubpath,module,identifier,olean_key,hash_key in [
      (remainder,REMAINDER_CERT,REMAINDER_PUB,base.PLATFORM_MODULE,'04008248-130e-40ba-b6a3-df3e9b9df91b','original_emitted_provider_olean','original_emitted_provider_olean_sha256'),
      (row,ROW_CERT,ROW_PUB,ROW_MODULE,None,'provider_olean','provider_olean_sha256')]:
        pub=read(pubpath);body=pub['target_readback']['body'];wire=pub['publish_intent']['payload']['definition']
        need(body['status']=='Definition' and body['visibility']=='public' and body['definition']==wire and body['theorem_id']==pub['definition_id']==pub['last_publish_verdict']['body']['theorem_id']
             and pub['last_publish_verdict']['body']['status']=='PUBLISHED' and (identifier is None or pub['definition_id']==identifier),'Actual Published dependency readback differs')
        filename=module.replace('.','/')+'.lean';parent=V/('ap19/analytic-remainder-data' if module==base.PLATFORM_MODULE else 'ap14/row-data')
        need((parent/filename).read_bytes()==wire.encode() and sha(context.file(cert[olean_key]))==cert[hash_key],'Published dependency bytes/OLean differ')
        for f in [path,pubpath,parent/filename,parent/'preparation.json',context.file(cert[olean_key])]:pins[rel(f)]=sha(f)
        pins.update(cert['implementation_hashes']);pins.update(read(parent/'preparation.json')['input_hashes'])
        pins.update(cert.get('output_json_sha256',{}))
        for rec in cert.get('original_preflights',cert.get('preflights',{})).values():historical(rec,pins,external)
        if 'source_automatic_preflight' in cert:
            historical(cert['source_automatic_preflight'],pins,external)
            automatic=V/'ap19/analytic-remainder-auto-ci-source-v4/source-automatic-ci.json'
            need(sha(automatic)==cert['source_automatic_json_sha256'],'Actual AP19 source automatic-CI JSON differs')
            pins[rel(automatic)]=cert['source_automatic_json_sha256']
            # The original full Def snapshots and raw inventory remain immutable.
            for f in [parent/SOURCE_JSON,parent/GENERATED_JSON,parent/base.INVENTORY_JSON]:pins[rel(f)]=sha(f)
    baseline=read(BASELINE);need(baseline['definition_count']==31 and len(baseline['definitions'])==31,'Immutable actual Published31 baseline differs')
    for r in baseline['definitions']:
        p=TASK/r['publication_record'];pub=read(p);b=pub['target_readback']['body']
        need(sha(p)==r['publication_record_sha256'] and b['status']=='Definition' and b['theorem_id']==r['definition_id']
             and b['definition']==pub['publish_intent']['payload']['definition'] and sha_bytes(b['definition'].encode())==r['source_sha256'],'Actual31 literal Published record differs')
        pins[rel(p)]=sha(p)
    # Actual source parent/children compiler evidence; no mutable graph/publication counters.
    top=V/'ap19/analytic-aggregate-two-child-reduction-final'
    source=top/'SourceTypeAndRefsSnapshot.lean';record=read(source.with_name(source.name+'.preflight.json'))
    historical({'record':rel(source.with_name(source.name+'.preflight.json')),'record_sha256':sha(source.with_name(source.name+'.preflight.json')),'data':record},pins,external)
    for f in [top/'preparation.json',top/'source-types-and-refs.json']:pins[rel(f)]=sha(f)
    # Never feed external paths to manifest task_file input resolution.
    local={}
    for p,h in pins.items():
        path=Path(p) if Path(p).is_absolute() else TASK/p
        try:local[rel(path)]=h
        except ValueError:external[str(path)]=h
    for p,h in local.items():need(sha(TASK/p)==h,'Historical dependency input changed: '+p)
    for p,h in external.items():need(sha(Path(p))==h,'External dependency input changed: '+p)
    doc={'CoreData_certificate_sha256':sha(base.CORE_CERT),'CoreData_definition_id':'03bc0316-3599-4c4d-97a8-3fce8ad984af',
      'CoreData_raw_equal_definitions':12,'CoreData_actual_closed_Prop_substitution_defs':2,'CoreData_actual_closed_Prop_pair':pair,
      'remainder_certificate_sha256':sha(REMAINDER_CERT),'remainder_definition_id':'04008248-130e-40ba-b6a3-df3e9b9df91b',
      'RowData_certificate_sha256':sha(ROW_CERT),'published31_baseline_sha256':sha(BASELINE)}
    _BINDING=(doc,dict(local),dict(external));return doc,local,external

CACHE_PROBE=r'''
namespace LiteralInterfaceUsedProofInventory
open Lean Meta PiExponentStructuralKernelSnapshot
def exportUsedProofs (roots : Array Name) (allowedOwners : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut todo : List Name := []
  for name in roots do
    let ci ← getConstInfo name
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo t => some t.value
      | _ => none
    todo := exprNames ci.type ++ (value.map exprNames |>.getD []) ++ todo
  let mut seen : List Name := []
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := name :: seen
    let some ci := env.find? name | continue
    let some owner := moduleFor? env name | continue
    if !allowedOwners.contains owner.toString then continue
    let .thmInfo t := ci | continue
    todo := exprNames ci.type ++ exprNames t.value ++ todo
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("owner",toJson owner.toString),
      ("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (envKind ci)),("levelParams",toJson (ci.levelParams.map Name.toString)),
      ("closedType",toJson (isClosed ci.type)),("closedValue",toJson (isClosed t.value)),
      ("isProp",toJson (← isProp ci.type)),("type",exprJson ci.type),("value",exprJson t.value),
      ("typeRefs",toJson ((uniqueSortedNames (exprNames ci.type)).map Name.toString)),
      ("valueRefs",toJson ((uniqueSortedNames (exprNames t.value)).map Name.toString)),
      ("axioms",toJson ((← Lean.collectAxioms name).toList.map Name.toString |>.mergeSort (fun a b => compare a b == .lt)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("roots",toJson (roots.toList.map Name.toString)),
    ("allowedOwners",toJson allowedOwners),("actualUsedProofCIs",Json.arr rows)]).compress
end LiteralInterfaceUsedProofInventory
'''

def allowed_modules(generated):
    if not generated:
        return sorted({json.loads(line)['module'] for line in base.base.GRAPH.read_text(encoding='utf-8').splitlines() if line.strip()})
    result=[PLATFORM_MODULE]
    for r in read(BASELINE)['definitions']:
        name=read(TASK/r['publication_record'])['publish_intent']['payload']['definition_name']
        result.append('Definitions.Def_'+name)
    return sorted(set(result))

def snapshot(units,generated):
    imports=['Lean',PLATFORM_MODULE] if generated else ['Lean']+SOURCE_MODULES
    requests=',\n'.join(base.base.request_text(r['owner'],PLATFORM_MODULE if generated else r['source_module']) for r in units)
    roots='#['+', '.join('`'+n for n in NAMES)+']'
    modules='#['+', '.join(json.dumps(n) for n in allowed_modules(generated))+']'
    probe=INVENTORY.read_text(encoding='utf-8') if generated else ''
    early='  LiteralAnalyticInterfaceOwnedInventory.exportInventory `'+NAMES[-1]+' '+json.dumps(PLATFORM_MODULE)+' '+json.dumps(workspace_rel(STAGE/INVENTORY_JSON))+'\n' if generated else ''
    return (''.join('import '+m+'\n' for m in imports)+'\n'+CORE.read_text(encoding='utf-8').rstrip()+'\n'+probe+'\n'+CACHE_PROBE+
      '\nopen PiExponentStructuralKernelSnapshot\ndef literalInterfaceRequests : Array StructuralRequest := #[\n'+requests+'\n]\n\nrun_meta do\n'+early+
      '  LiteralInterfaceUsedProofInventory.exportUsedProofs '+roots+' '+modules+' '+json.dumps(workspace_rel(STAGE/(GENERATED_CACHES if generated else SOURCE_CACHES)))+'\n'+
      '  exportStructuralSnapshotJsonl literalInterfaceRequests '+json.dumps(workspace_rel(STAGE/(GENERATED_JSON if generated else SOURCE_JSON)))+'\n\n'+
      '\n'.join('#print axioms '+n for n in NAMES)+'\n').encode()

def stage_files():
    units=authority();inherited,pins,external=inherited_binding();p=read(REPORT)
    pins.update(p['input_hashes'])
    for x in [SELF,CONSUMER,Path(base.__file__),Path(route.__file__),base.base.AST,base.base.SCOPES,base.base.GRAPH,base.base.OWNERS,CORE,RUNTIME,RUNNER,base.base.PREFLIGHT,base.base.CONTEXT,REPORT,BASELINE,INVENTORY]:pins[rel(x)]=sha(x)
    candidate=route.STAGE/('candidate/'+PROVIDER_FILE);body=candidate.read_bytes()
    need(sha(candidate)==p['files']['candidate/'+PROVIDER_FILE] and b'theorem ' not in body and b'sorry' not in body,'Original17 candidate provider changed')
    for r in units:need(body.count(r['bytes'])==1,'Original full AST not uniquely present in provider: '+r['name'])
    pins[rel(candidate)]=sha(candidate)
    need(all(not Path(k).is_absolute() and '..' not in Path(k).parts and sha(TASK/k)==h for k,h in pins.items()),'Manifest inputs are not exact mission-relative task files')
    files={PROVIDER_FILE:body,SOURCE_SNAPSHOT:snapshot(units,False),GENERATED_SNAPSHOT:snapshot(units,True)};commands=[]
    for i,(f,imports,mode) in enumerate([(PROVIDER_FILE,IMPORTS,'emit-olean'),(SOURCE_SNAPSHOT,['Lean']+SOURCE_MODULES,'modecheck'),(GENERATED_SNAPSHOT,['Lean',PLATFORM_MODULE],'modecheck')],1):
        files[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap20-original17Def-bounded-manifest','output':workspace_rel(STAGE/f),
          'output_sha256':sha_bytes(files[f]),'imports':imports,'input_hashes':pins,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean',
          'timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(base.base.PREFLIGHT),'validated':False,'submission_ready':False})
        commands.append('& '+repr(base.PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap20/literal-interface-data/'+f+' --root ap20/literal-interface-data --imports-manifest ap20/literal-interface-data/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    files['academic-metadata.json']=encode({'definition_title':'Original literal analytic row choices and summand data',
      'natural_language_statement':r'For the original admissible fixed data $d$, height $H$, row $r$, and column selection, define the finite transverse indices, row choices and choice families used in the literal determinant expansion. The weights are $w=\log q$, $\operatorname{wt}_w(a)=\sum_i w_i a_i$, and the logarithmic period is $\omega=2\pi i$. Define the period series $j\omega+\log(1+X)$, translated monomials, the truncation tail and the original binomial row scalar. The functions $\beta$, rowWeight, indexWeight, choiceScalar and choiceMatrix retain exactly their original source types and formulas. These seventeen definitions state the immediate analytic-minor and summand-bound interfaces; this package asserts no estimate, limit or determinant theorem.',
      'source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L12-L47',
      'tags':['number-theory','power-series','openai-pi-exponent-017']})
    files['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap20-literal-interface-original17Def-preparation','source_commit':COMMIT,
      'platform_module':PLATFORM_MODULE,'provider_file':PROVIDER_FILE,'provided_names':NAMES,'source_modules':SOURCE_MODULES,'imports':IMPORTS,
      'exact_source_units':[{k:v for k,v in r.items() if k!='bytes'} for r in units],'contains_theorems':False,'own_structures_constructors_recursors':[],
      'original17_source_lines':49,'candidate_provider_bytes_unchanged':True,'raw_owned_CI_inventory_exported_before_classification':True,
      'complete_environment_inventory_owner_index_first':True,'actual_used_proof_CI_inventory_no_guessed_names':True,
      'inherited_provider_binding':inherited,'input_hashes':pins,'external_dependency_olean_hashes':external,
      'expected_provider_olean':rel(V/'staged-build/lib/lean'/Path(PROVIDER_FILE).with_suffix('.olean')),
      'commands':commands,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def check_only(key='interface'):
    config(key);files=stage_files()
    for f,raw in files.items():need((STAGE/f).read_bytes()==raw,'Immutable AP20 provider differs: '+f)
    for i,f in enumerate([PROVIDER_FILE,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):
        m=read(STAGE/f'c{i}.json');base.base.runner.verify_manifest_inputs(m);base.base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(files),'provided_names':NAMES,'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        files=stage_files()
        for f,raw in files.items():
            target=STAGE/f
            if target.exists():need(target.read_bytes()==raw,'Refusing overwrite: '+f)
            else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
        for f,raw in files.items():need((STAGE/f).read_bytes()==raw,'Written output differs: '+f)
        result={'prepared_files':len(files),'validated':False,'Lean_started':False,'API_used':False}
    else:result=check_only()
    print(json.dumps(result,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
