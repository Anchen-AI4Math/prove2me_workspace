"""Pure AP19 four original definitions for the immediate analytic-aggregate children."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_weighted_simplex_domains_providers as base
import certify_determinant_core_data_helper_existing as core_cert
TASK,ROOT,V=base.TASK,base.ROOT,base.V;SELF=Path(__file__).resolve()
STAGE=V/'ap19/analytic-remainder-data';COMMIT=base.COMMIT
PLATFORM_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData'
PROVIDER_FILE=PLATFORM_MODULE.replace('.','/')+'.lean'
CORE_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData'
CORE_STAGE=V/'ap10/determinant';CORE_CERT=CORE_STAGE/'actual-provider-validation-helper-v2.json'
CORE_PUB=CORE_STAGE/'publication-helper-v2/publication.json'
CORE_CERT_SHA='d17d1a485e9b7310e16741d70f6ac0cd4b5a37fbfd4c2913a1b58cfb0f98a30e'
CORE_OLEAN_SHA='e36e73def8d80749901c917296c3047cfb24d00c681172a03a93e7162a8e8eea'
CORE=base.CORE;COVERAGE=STAGE/'published30-coverage.json';BASELINE=STAGE/'published30-baseline.json'
REPORT=V/'ap19/analytic-route/report.md'
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT=base.SOURCE_SNAPSHOT,base.GENERATED_SNAPSHOT
SOURCE_JSON,GENERATED_JSON=base.SOURCE_JSON,base.GENERATED_JSON
INVENTORY_JSON='actual-owned-CI-inventory.json'
RUNNER=TASK/'scripts/preflight_staged_module_windows_bounded.py';CONSUMER=TASK/'scripts/certify_analytic_remainder_data_existing.py'
CONFIGS=['remainder'];PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
SPECS=[('OAI.PiExponent.Collision.collisionRatio','CollisionExponential',149,217,9,9),
 ('OAI.PiExponent.Collision.collisionRemainder','CollisionExponential',3607,3741,86,87),
 ('OAI.PiExponent.translationTermCount','TranslationCountLimit',187,309,10,11),
 ('OAI.PiExponent.LiteralAnalytic.analyticRemainder','AnalyticAggregate',2283,2482,49,51)]
NAMES=[s[0] for s in SPECS];SOURCE_MODULES=list(dict.fromkeys('OAI.NumberTheory.PiExponent.Analysis.'+s[1] for s in SPECS))
IMPORTS=['Mathlib.Analysis.SpecialFunctions.Log.Basic','Mathlib.Algebra.Order.Floor.Defs',CORE_MODULE]
read,encode,sha,sha_bytes,need,rel,workspace_rel=base.read,base.encode,base.sha,base.sha_bytes,base.need,base.rel,base.workspace_rel
_CORE_CACHE=None

def config(key='remainder'):
    need(key=='remainder','Unknown provider key')
    return {'stage':STAGE,'platform_module':PLATFORM_MODULE,'provider_file':PROVIDER_FILE,'names':NAMES,'imports':IMPORTS,'source_modules':SOURCE_MODULES}

def actual_coverage():
    p=read(BASELINE);need(p['definition_count']==30,'Expected frozen actual Published30 baseline')
    rows=[];ids=set()
    for r in p['definitions']:
        path=TASK/r['publication_record'];doc=read(path);body=doc['target_readback']['body'];wire=doc['publish_intent']['payload']['definition']
        need(sha(path)==r['publication_record_sha256'] and body['status']=='Definition'
             and body['definition']==wire and body['theorem_id']==r['definition_id']
             and sha_bytes(wire.encode())==r['source_sha256'],'Actual Published literal payload/readback differs')
        need(all(n.rsplit('.',1)[1] not in wire for n in NAMES),'Actual Published wire mentions an unreviewed selected declaration')
        rows.append({'definition_id':r['definition_id'],'publication_record':r['publication_record'],
          'publication_record_sha256':sha(path),'literal_definition_sha256':sha_bytes(wire.encode())});ids.add(r['definition_id'])
    need(len(ids)==30,'Actual Published unique-ID domain differs')
    return {'schema_version':1,'artifact_kind':'ap19-Published30-four-Def-literal-coverage','audited_definition_count':30,
      'queried_names':NAMES,'none_provided':True,'records':rows,'Lean_started':False,'API_used':False}

def authority():
    ast,scopes=read(base.AST),read(base.SCOPES);owners={r['source_name']:r for r in read(base.OWNERS)['owners']}
    graph={r['name']:r for r in map(json.loads,base.GRAPH.read_text(encoding='utf-8').splitlines())};rows=[]
    for name,short,a,b,first,last in SPECS:
        module='OAI.NumberTheory.PiExponent.Analysis.'+short;source=TASK/('port/lean/'+module.replace('.','/')+'.lean');original=TASK/('source/lean/'+module.replace('.','/')+'.lean')
        raw=source.read_bytes();command=raw[a:b];am=next(m for m in ast['modules'] if m['module']==module)
        sm=next(m for m in scopes['modules'] if m['source']==module.replace('.','/')+'.lean')
        u=next(u for u in am['units'] if name in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==name);o=owners[name]
        contexts=[raw[c['range']['start']['offset']:c['range']['end']['offset']].decode() for c in s['context_commands']]
        expected=['open scoped BigOperators'] if short=='CollisionExponential' else ['open Filter Topology'] if short=='TranslationCountLimit' else ['open scoped BigOperators Topology','open Filter','open DeterminantContradiction']
        need(am['source_sha256']==sm['source_sha256']==sha(source) and [u['start']['offset'],u['end']['offset']]==[a,b]
          and [u['start']['line'],u['end']['line']]==[first,last] and u['graph_names']==[name] and u['graph_kinds']==['def']
          and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance']
          and contexts==expected and all(x['kind']=='namespace' for x in s['scope_stack']) and s['namespace']==name.rsplit('.',1)[0]
          and o['command_unit']==module+':'+str(a) and o['source_sha256']==sha(source)
          and original.read_bytes().replace(b'\r\n',b'\n').count(command.replace(b'\r\n',b'\n'))==1,
          'Exact original four-Def AST/scope/owner differs: '+name)
        rows.append({'name':name,'source_module':module,'source_path':rel(source),'source_sha256':sha(source),
          'original_source_path':rel(original),'original_source_sha256':sha(original),'start':a,'end':b,
          'source_lines':[first,last],'sha256':sha_bytes(command),'bytes':command,'ast':u,'scope':s,'owner':o,
          'graph':graph[name],'contexts':contexts})
    expected={NAMES[0]:[],NAMES[1]:[NAMES[0]],NAMES[2]:[],NAMES[3]:['OAI.PiExponent.AdmissibleParameters.m',NAMES[2],
       'OAI.PiExponent.DeterminantContradiction.FixedData','OAI.PiExponent.AdmissibleParameters.v0',
       'OAI.PiExponent.DeterminantContradiction.actualRowCount',NAMES[1],
       'OAI.PiExponent.DeterminantContradiction.collisionConstant','OAI.PiExponent.Arithmetic.lcmConstant']}
    for r in rows:need(r['graph']['valueDeps']==expected[r['name']],'Actual source Def value closure differs')
    return rows

def inherited_binding():
    global _CORE_CACHE
    if _CORE_CACHE is not None:
        cert,pins,dependency_pins=_CORE_CACHE
        for p,h in pins.items():need(sha(TASK/p)==h,'Fixed CoreData evidence changed: '+p)
        for p,h in dependency_pins.items():need(sha(Path(p))==h,'Fixed CoreData imported OLean changed: '+p)
        return cert,dict(pins)
    cert=read(CORE_CERT);pub=read(CORE_PUB);provider=CORE_STAGE/('Definitions/'+CORE_MODULE.split('.')[-1]+'.lean')
    need(sha(CORE_CERT)==CORE_CERT_SHA and cert['validated'] is True and cert['Std3_only'] is True
         and cert['platform_module']==CORE_MODULE and cert['raw_equal_definition_count']==12
         and cert['definition_values_equal_after_certified_proof_CI_substitution'] is True
         and cert['provider_olean_sha256']==CORE_OLEAN_SHA and sha(TASK/cert['provider_olean'])==CORE_OLEAN_SHA
         and pub['definition_id']==pub['target_readback']['body']['theorem_id']==pub['last_publish_verdict']['body']['theorem_id']=='03bc0316-3599-4c4d-97a8-3fce8ad984af'
         and pub['last_publish_verdict']['body']['status']=='PUBLISHED' and pub['target_readback']['body']['status']=='Definition'
         and pub['target_readback']['body']['definition'].encode()==provider.read_bytes()
         and cert['provider_source_sha256']==sha(provider),'Canonical Published CoreData certificate/value/owner/OLean differs')
    pair=cert['certified_actual_helper_pair']
    pins={rel(p):sha(p) for p in [CORE_CERT,CORE_PUB,provider,CORE_STAGE/'preparation.json',TASK/cert['provider_olean'],Path(core_cert.__file__)]}
    pins.update(cert['implementation_hashes']);pins.update(cert['output_json_sha256']);pins.update(read(CORE_STAGE/'preparation.json')['input_hashes'])
    dependency_pins={}
    for r in list(cert['preflights'].values())+[v['preflight'] for v in pair['actual_witnesses'].values()]:
        pins[r['record']]=r['record_sha256']
        for k in ['source','manifest','log']:
            path=core_cert.context.file(r['data'][k]);pins[rel(path)]=sha(path)
        for d in r['data']['dependency_oleans']:
            need(d['stable_during_compile'] and d['sha256_before']==d['sha256_after'],'Historical CoreData imported OLean was unstable')
            dependency_pins[d['path']]=d['sha256_before']
    for v in pair['actual_witnesses'].values():pins[v['output']]=v['output_sha256']
    for p,h in pins.items():need(sha(TASK/p)==h,'Canonical CoreData immutable evidence changed: '+p)
    for p,h in dependency_pins.items():need(sha(Path(p))==h,'Canonical CoreData imported OLean changed: '+p)
    actual=core_cert.validate()
    need(encode(actual)==CORE_CERT.read_bytes(),'First complete CoreData helper-v2 replay differs from the genuine certificate')
    for p,h in pins.items():need(sha(TASK/p)==h,'Canonical CoreData evidence changed during first replay: '+p)
    for p,h in dependency_pins.items():need(sha(Path(p))==h,'Canonical CoreData OLean changed during first replay: '+p)
    _CORE_CACHE=(actual,dict(pins),dict(dependency_pins))
    return cert,pins

INVENTORY_PROBE=r'''
namespace AnalyticRemainderOwnedInventory
open Lean Meta PiExponentStructuralKernelSnapshot
def exportInventory (moduleName output : String) : MetaM Unit := do
  let env ← getEnv
  let mut found : Array (Name × ConstantInfo) := #[]
  for (name, ci) in env.constants.toList do
    if (moduleFor? env name).map Name.toString == some moduleName then
      found := found.push (name, ci)
  found := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut rows : Array Json := #[]
  for (name, ci) in found do
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo t => some t.value
      | _ => none
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("owner",toJson moduleName),
      ("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (envKind ci)),("levelParams",toJson (ci.levelParams.map Name.toString)),
      ("closedType",toJson (isClosed ci.type)),("closedValue",toJson (value.map isClosed)),
      ("isProp",toJson (← isProp ci.type)),("type",exprJson ci.type),
      ("value",value.map exprJson |>.getD Json.null),
      ("typeRefs",toJson ((uniqueSortedNames (exprNames ci.type)).map Name.toString)),
      ("valueRefs",toJson ((uniqueSortedNames (value.map exprNames |>.getD [])).map Name.toString)),
      ("axioms",toJson ((← Lean.collectAxioms name).toList.map Name.toString |>.mergeSort (fun a b => compare a b == .lt)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("providerModule",toJson moduleName),
    ("rawOwnedCIs",Json.arr rows)]).compress
end AnalyticRemainderOwnedInventory
'''

def snapshot(units,generated):
    imports=['Lean',PLATFORM_MODULE] if generated else ['Lean']+SOURCE_MODULES
    requests=',\n'.join(base.request_text(r['owner'],PLATFORM_MODULE if generated else r['source_module']) for r in units)
    output=GENERATED_JSON if generated else SOURCE_JSON
    probe=INVENTORY_PROBE if generated else ''
    early='  AnalyticRemainderOwnedInventory.exportInventory '+json.dumps(PLATFORM_MODULE)+' '+json.dumps(workspace_rel(STAGE/INVENTORY_JSON))+'\n' if generated else ''
    return (''.join('import '+m+'\n' for m in imports)+'\n'+CORE.read_text(encoding='utf-8').rstrip()+'\n'+probe+
      '\nopen PiExponentStructuralKernelSnapshot\ndef analyticRemainderRequests : Array StructuralRequest := #[\n'+requests+'\n]\n\nrun_meta do\n'+early+
      '  exportStructuralSnapshotJsonl analyticRemainderRequests '+json.dumps(workspace_rel(STAGE/output))+'\n\n'+
      '\n'.join('#print axioms '+n for n in NAMES)+'\n').encode()

def stage_files():
    units=authority();cert,pins=inherited_binding();cov=read(COVERAGE)
    need(cov['audited_definition_count']==30 and cov['none_provided'] is True and cov['queried_names']==NAMES,'Frozen actual Published30 coverage differs')
    for r in cov['records']:pins[r['publication_record']]=r['publication_record_sha256']
    body=''.join('import '+m+'\n' for m in IMPORTS).encode()+b'\n'
    for r in units:
        ns=r['scope']['namespace'];body+=('\nnamespace '+ns+'\n\n'+'\n'.join(r['contexts'])+'\n\n').encode()+r['bytes']+('\n\nend '+ns+'\n').encode()
    need(b'theorem ' not in body and b'sorry' not in body and body.count(b'def ')==4,'Provider contains non-original data or proof material')
    files={PROVIDER_FILE:body,SOURCE_SNAPSHOT:snapshot(units,False),GENERATED_SNAPSHOT:snapshot(units,True)}
    for p in [SELF,CONSUMER,Path(base.__file__),base.AST,base.SCOPES,base.GRAPH,base.OWNERS,CORE,base.RUNTIME,base.PREFLIGHT,base.CONTEXT,COVERAGE,BASELINE,RUNNER,REPORT]:pins[rel(p)]=sha(p)
    for r in units:
        pins[r['source_path']]=r['source_sha256'];pins[r['original_source_path']]=r['original_source_sha256']
    plans=[(PROVIDER_FILE,IMPORTS,'emit-olean'),(SOURCE_SNAPSHOT,['Lean']+SOURCE_MODULES,'modecheck'),(GENERATED_SNAPSHOT,['Lean',PLATFORM_MODULE],'modecheck')];commands=[]
    for i,(f,imports,mode) in enumerate(plans,1):
        files[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap19-four-Def-bounded-manifest',
          'output':workspace_rel(STAGE/f),'output_sha256':sha_bytes(files[f]),'imports':imports,'input_hashes':pins,
          'runtime_sha256':sha(base.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,
          'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(base.PREFLIGHT),
          'validated':False,'submission_ready':False})
        commands.append('& '+repr(PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap19/analytic-remainder-data/'+f+' --root ap19/analytic-remainder-data --imports-manifest ap19/analytic-remainder-data/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    metadata={'definition_title':'Original collision and translation remainders for analytic aggregation',
      'natural_language_statement':r'Define $r=\exp(-\log 2/2)$, the collision remainder $C(M,H)=(\log M+\log 2/4-\log(1-r))/H$, and the translation term count $T(m,v,H)=(\lfloor H\rfloor_{\mathbb N}+1)^{2m}(\lfloor H/v\rfloor_{\mathbb N}+1)$. For the original fixed admissible data $d$ with row count $M_d(H)$, define'+'\n\n'+r'$$R_d(H)=C(M_d(H),H)+\frac{\log T(d.m,d.v_0,H)}{H}.$$'+'\n\n'+r'Here $M,m$ are natural numbers and $v,H$ are real. The natural floor is the original source operation; the definitions impose no positivity hypotheses and assert no convergence or determinant estimate. These exact quantities state the two immediate original children of the analytic aggregate theorem.',
      'source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L49-L51',
      'tags':['number-theory','asymptotics','openai-pi-exponent-017']}
    files['academic-metadata.json']=encode(metadata)
    files['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap19-analytic-remainder-four-Def-preparation',
      'source_commit':COMMIT,'source_modules':SOURCE_MODULES,'platform_module':PLATFORM_MODULE,'provided_names':NAMES,
      'provider_file':PROVIDER_FILE,'imports':IMPORTS,'exact_source_units':[{k:v for k,v in r.items() if k!='bytes'} for r in units],
      'contains_theorems':False,'own_structures_constructors_recursors':[],'raw_owned_CI_inventory_exported_before_classification':True,
      'source_theorem_values_not_requested':True,'published_coverage':rel(COVERAGE),'published_coverage_sha256':sha(COVERAGE),
      'frozen_actual_Published30_baseline':rel(BASELINE),'frozen_actual_Published30_baseline_sha256':sha(BASELINE),
      'canonical_CoreData_certificate':rel(CORE_CERT),'canonical_CoreData_certificate_sha256':sha(CORE_CERT),
      'canonical_CoreData_definition_id':'03bc0316-3599-4c4d-97a8-3fce8ad984af','canonical_CoreData_module':CORE_MODULE,
      'canonical_CoreData_OLean':cert['provider_olean'],'canonical_CoreData_OLean_sha256':CORE_OLEAN_SHA,
      'canonical_CoreData_raw_equal_definitions':12,'canonical_CoreData_closed_Prop_helper_substitution_defs':2,
      'input_hashes':pins,'expected_provider_olean':rel(V/'staged-build/lib/lean'/Path(PROVIDER_FILE).with_suffix('.olean')),
      'commands':commands,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def check_only(key='remainder'):
    config(key);files=stage_files()
    for f,raw in files.items():need((STAGE/f).read_bytes()==raw,'Immutable AP19 provider differs: '+f)
    for i,f in enumerate([PROVIDER_FILE,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):
        m=read(STAGE/f'c{i}.json');base.runner.verify_manifest_inputs(m);base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(files),'provided_names':NAMES,'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        if not BASELINE.exists():
            progress=read(V/'verified-stage-progress.json');need(progress['definition_count']==30,'Initial actual Published30 baseline differs')
            BASELINE.parent.mkdir(parents=True,exist_ok=True)
            BASELINE.write_bytes(encode({'schema_version':1,'artifact_kind':'ap19-immutable-actual-Published30-baseline',
              'definition_count':30,'definitions':progress['definitions'],
              'origin_progress_sha256_at_capture':sha(V/'verified-stage-progress.json'),
              'mutable_progress_not_pinned_or_read_on_replay':True}))
        if not COVERAGE.exists():COVERAGE.parent.mkdir(parents=True,exist_ok=True);COVERAGE.write_bytes(encode(actual_coverage()))
        files=stage_files()
        for f,raw in files.items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        for f,raw in files.items():need((STAGE/f).read_bytes()==raw,'Written output differs: '+f)
        result={'prepared_files':len(files),'validated':False,'Lean_started':False,'API_used':False}
    else:result=check_only()
    print(json.dumps(result,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
