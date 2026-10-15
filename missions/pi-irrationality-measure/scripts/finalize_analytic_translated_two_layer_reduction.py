"""Pure two-layer analytic sketch candidate; final manifests require real17Def Published evidence."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_analytic_translated_graph_route as route
import stage_literal_analytic_interface_data_provider as data
import certify_literal_analytic_interface_data_existing as data_consumer
import stage_source_root_graph as source_root

TASK,ROOT,V,SELF=data.TASK,data.ROOT,data.V,Path(__file__).resolve()
STAGE=V/'ap20/analytic-translated-two-layer-reduction-final'
CANDIDATE=V/'ap20/analytic-translated-two-layer-reduction-candidate'
CONSUMER=TASK/'scripts/certify_analytic_translated_two_layer_reduction.py'
CERTIFICATE=STAGE/'open-sketch-interface-validation.json'
LOOKUP=V/'ap20/exact-new-analytic-and-collision-name-lookup.json'
LOOKUP_SHA='46c40632d84952262c90ffe39d56f5f50de93fef127ea1cd27cb754a45d1c115'
ACTUAL,NORM,CHILDREN=route.ACTUAL,route.NORM,route.CHILDREN
NEW_NAMES=[NORM]+[n for n in CHILDREN[ACTUAL]+CHILDREN[NORM] if n!=NORM]
ACCEPTED=[route.LOGSUM,route.TRANSLATED];INTERFACE_NAMES=[ACTUAL]+NEW_NAMES+ACCEPTED
ACTUAL_ID='a08a3f36-e4a6-4a12-a77b-53e5c07f6ac9'
SOURCE_SNAPSHOT='SourceTypeAndRefsSnapshot.lean';SOURCE_JSON='source-types-and-refs.json'
SOURCE_AUX_JSON='source-actual-auxiliary-CIs.json'
GENERATED_SNAPSHOTS={p:('GeneratedNormSnapshot.lean' if p==NORM else 'GeneratedActualSnapshot.lean') for p in [NORM,ACTUAL]}
GENERATED_JSON={p:('generated-norm-types-and-refs.json' if p==NORM else 'generated-actual-types-and-refs.json') for p in [NORM,ACTUAL]}
OWNED_JSON={p:('generated-norm-owned-CIs.json' if p==NORM else 'generated-actual-owned-CIs.json') for p in [NORM,ACTUAL]}
SOLUTION_MODULES={p:'Solutions.Sol_'+p.replace('.','_')+'_two_layer_graph_ap20' for p in [NORM,ACTUAL]}
SOURCE_CORE=V/'TypeOnlyTheoremSnapshotCore.inc';RUNNER=data.RUNNER;RUNTIME=data.RUNTIME
PUBLICATION=data.STAGE/'publication/publication.json'
PRIOR_STAGE=V/'ap19/analytic-aggregate-two-child-reduction-final'
PRIOR_CERT=V/'ap19/analytic-aggregate-two-child-reduction-validation-v2/open-sketch-interface-validation-v2.json'
read,encode,sha,digest,need,rel,workspace_rel=data.read,data.encode,data.sha,data.sha_bytes,data.need,data.rel,data.workspace_rel
_BOUNDARY=None

def theorem_module(n):return route.module(n)
def theorem_file(n):return theorem_module(n).replace('.','/')+'.lean'
def solution_file(n):return SOLUTION_MODULES[n].replace('.','/')+'.lean'

def units():
    report=read(route.STAGE/'report.json');selected={r['name']:r for r in report['source_units']};result={}
    for n in INTERFACE_NAMES:
        if n in selected:
            r=dict(selected[n]);r['command']=(TASK/r['source']).read_bytes()[r['start']:r['end']]
            need(sha(TASK/r['source'])==r['source_sha256'] and digest(r['command'])==r['command_sha256'],'Original typed interface source changed: '+n)
        else:
            r=source_root.authority(n);r['command']=r.pop('unit');r['command_sha256']=r['unit_sha256']
        r['source_module']=r['module'];a=r['ast']['nameRange']['start']['offset']-r['start'];b=r['ast']['nameRange']['end']['offset']-r['start'];v=r['ast']['valueStart']['offset']-r['start']
        need(r['command'][v:].startswith(b':='),'Original theorem proof delimiter differs')
        r['name_offsets']=[a,b];r['value_offset']=v;r['proof_suffix_sha256']=digest(r['command'][v:])
        if n in [ACTUAL,NORM]:
            need(r['finite_source_port_version_adaptation'] is None and (TASK/r['original']).read_bytes().replace(b'\r\n',b'\n').count(r['command'].replace(b'\r\n',b'\n'))==1,'Original parent proof bytes differ')
        result[n]=r
    return result

def lookup_and_leaves():
    need(sha(LOOKUP)==LOOKUP_SHA,'Actual fixed-environment exact-name lookup changed')
    lookup=read(LOOKUP);need(lookup['read_only'] and lookup['request_methods']==['GET'],'Lookup was not read-only')
    by={r['theorem_name']:r for r in lookup['records']};parent=by[ACTUAL]
    need(parent['lookup_total']==1 and len(parent['matches'])==len(parent['readbacks'])==1,'Existing actualMinor is not unique')
    actual=parent['readbacks'][0]['parsed_body'];need(actual['theorem_id']==ACTUAL_ID and actual['theorem_name']==ACTUAL and actual['status']=='Open' and actual['visibility']=='public','Existing actualMinor boundary changed')
    for n in NEW_NAMES:
        r=by[n];need(r['lookup_total']==0 and r['matches']==[] and r['readbacks']==[] and len(r['pages'])==1,'New source analytic name already exists: '+n)
        q=r['pages'][0];need(q['http_status']==200 and q['parsed_body']=={'theorems':[],'total':0} and digest(q['raw_body_utf8'].encode())==q['raw_body_sha256'],'Raw exact-name result differs')
    leaves={};report=read(route.STAGE/'report.json')
    for n in ACCEPTED:
        witness=report['accepted_public_boundaries'][n];path=TASK/witness['publication_record'];p=read(path)
        b=p['post_accepted_target_readback']['body'] if n==route.TRANSLATED else p['target_readback']['body']
        verdict=p['last_verify_verdict']['body'] if n==route.TRANSLATED else p['last_verify_verdict']
        need(sha(path)==witness['publication_record_sha256'] and b['status']=='Proved' and b['theorem_name']==n
             and b['theorem_id']==witness['theorem_id'] and verdict['status']=='ACCEPTED' and verdict.get('id',p['submission_id'])==witness['proof_id'], 'Real Accepted public leaf differs')
        leaves[n]={'accepted':witness,'body':b,'local_role':'exact public comparator placeholder; server theorem genuinely Proved; no local closed proof asserted'}
    need(len(NEW_NAMES)==11 and len(set(INTERFACE_NAMES))==14,'Exact new analytic/interface domain differs')
    return actual,leaves

INVENTORY=r'''
namespace AnalyticTranslatedOwnedInventory
open Lean Meta
def exportInventory (anchors : Array Name) (owners : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  unless anchors.size == owners.size do throwError "Raw inventory anchor/owner domain differs"
  let mut indices : Std.HashSet Nat := {}
  for i in [:anchors.size] do
    let some idx := env.getModuleIdxFor? anchors[i]! | throwError "Raw inventory owner is not imported"
    unless env.header.moduleNames[idx.toNat]?.map Name.toString == some owners[i]! do throwError "Raw inventory owner differs"
    indices := indices.insert idx.toNat
  let mut found : Array (Name × ConstantInfo × Nat) := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if indices.contains idx.toNat then found := found.push (name,ci,idx.toNat)
  found := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut rows : Array Json := #[]
  for (name,ci,idx) in found do
    let value := match ci with | .thmInfo t => some t.value | .defnInfo d => some d.value | _ => none
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("actualOwner",toJson ((env.header.moduleNames[idx]!).toString)),
      ("ownerModuleIndex",toJson idx),("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other")),
      ("levelParams",toJson (ci.levelParams.map Name.toString)),("type",PiExponentInterfaceSnapshot.exprJson ci.type),("value",Json.null),
      ("closedType",toJson (!ci.type.hasMVar && !ci.type.hasFVar)),("closedValue",toJson (value.map (fun e => !e.hasMVar && !e.hasFVar))),
      ("isProp",toJson (← isProp ci.type)),("typeRefs",toJson ((ci.type.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("valueRefs",toJson ((value.map (fun e => e.getUsedConstants.map Name.toString) |>.getD #[]).qsort (· < ·))),
      ("axioms",toJson ((← Lean.collectAxioms name).map Name.toString |>.qsort (· < ·)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("ownerModules",toJson owners),("inventorySelection",toJson "all constants, imported ModuleIdx first"),("rawOwnedCIs",Json.arr rows)]).compress
end AnalyticTranslatedOwnedInventory
'''

SOURCE_AUX_PROBE=r'''
namespace AnalyticTranslatedSourceAuxiliary
open Lean Meta
def exportAuxiliary (roots : Array Name) (publicNames owners : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut todo : List Name := []
  for n in roots do
    let ci ← getConstInfo n
    let .thmInfo t := ci | throwError "Source root was not theorem"
    todo := t.value.getUsedConstants.toList ++ todo
  let mut seen : Std.HashSet Name := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if publicNames.contains n.toString then continue
    let some idx := env.getModuleIdxFor? n | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !owners.contains owner.toString then continue
    let some ci := env.find? n | continue
    let .thmInfo t := ci | continue
    todo := ci.type.getUsedConstants.toList ++ t.value.getUsedConstants.toList ++ todo
    rows := rows.push <| Json.mkObj [("name",toJson n.toString),("actualOwner",toJson owner.toString),
      ("privateUserName",toJson ((Lean.privateToUserName? n).map Name.toString)),("kind",toJson "theorem"),
      ("levelParams",toJson (ci.levelParams.map Name.toString)),("type",PiExponentInterfaceSnapshot.exprJson ci.type),("value",Json.null),
      ("closedType",toJson (!ci.type.hasMVar && !ci.type.hasFVar)),("closedValue",toJson (!t.value.hasMVar && !t.value.hasFVar)),
      ("isProp",toJson (← isProp ci.type)),("typeRefs",toJson ((ci.type.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("valueRefs",toJson ((t.value.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("axioms",toJson ((← Lean.collectAxioms n).map Name.toString |>.qsort (· < ·)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("roots",toJson (roots.map Name.toString)),("actualAuxiliaryCIs",Json.arr rows)]).compress
end AnalyticTranslatedSourceAuxiliary
'''

def snapshot(u,parent=None,final=False):
    target=STAGE if final else CANDIDATE;generated=parent is not None
    names=INTERFACE_NAMES+(['solution'] if generated else [])
    owners=[theorem_module(n) for n in INTERFACE_NAMES]+([SOLUTION_MODULES[parent]] if generated else []) if generated else [u[n]['source_module'] for n in INTERFACE_NAMES]
    imports=['Lean']+([theorem_module(n) for n in INTERFACE_NAMES]+[SOLUTION_MODULES[parent]] if generated else list(dict.fromkeys(u[n]['source_module'] for n in INTERFACE_NAMES)))
    ns='#['+', '.join('`'+n for n in names)+']';os='#['+', '.join(json.dumps(n) for n in owners)+']'
    graph=[json.loads(l) for l in data.base.base.GRAPH.read_text(encoding='utf-8').splitlines() if l.strip()]
    public_names='#['+', '.join(json.dumps(r['name']) for r in graph)+']'
    source_owners='#['+', '.join(json.dumps(m) for m in sorted({r['module'] for r in graph}))+']'
    early='  AnalyticTranslatedOwnedInventory.exportInventory '+ns+' '+os+' '+json.dumps(workspace_rel(target/OWNED_JSON[parent]))+'\n' if generated else '  AnalyticTranslatedSourceAuxiliary.exportAuxiliary '+ns+' '+public_names+' '+source_owners+' '+json.dumps(workspace_rel(target/SOURCE_AUX_JSON))+'\n'
    out=GENERATED_JSON[parent] if generated else SOURCE_JSON
    return (''.join('import '+m+'\n' for m in imports)+'\n'+SOURCE_CORE.read_text(encoding='utf-8').rstrip()+'\n'+source_root.PROBE+'\n'+(INVENTORY if generated else SOURCE_AUX_PROBE)+
      '\nrun_meta do\n'+early+'  SourceRootGraphSnapshot.exportRows '+ns+' '+os+' '+json.dumps(workspace_rel(target/out))+' '+str(generated).lower()+'\n'+
      ''.join('#print axioms '+n+'\n' for n in names)).encode(),imports

def candidate_files(final=False):
    actual,leaves=lookup_and_leaves();u=units();old=read(route.STAGE/'report.json');files={};wires={}
    for n in NEW_NAMES:
        raw=(route.STAGE/('candidate/'+theorem_file(n))).read_bytes();r=u[n];a,b=r['name_offsets'];v=r['value_offset']
        formal=r['command'][:a]+n.encode()+r['command'][b:v]+b':= by\n  sorry\n'
        need(raw.endswith(formal),'New global comparator full source statement differs: '+n)
        wires[n]={'preamble':raw[:-len(formal)].decode(),'formal_statement':formal.decode(),'local_role':'Open interface placeholder, not a closed proof'};files[theorem_file(n)]=raw
    files['parent-existing-wire.lean']=(actual['preamble']+actual['formal_statement']).encode()
    for n in ACCEPTED:
        b=leaves[n]['body'];files[theorem_file(n)]=(b['preamble']+b['formal_statement']).encode();wires[n]={'preamble':b['preamble'],'formal_statement':b['formal_statement'],'local_role':leaves[n]['local_role']}
    for parent in [NORM,ACTUAL]:
        raw=(route.STAGE/('candidate/Solutions/Sol_'+parent.replace('.','_')+'_graph_candidate.lean')).read_bytes();r=u[parent];a,b=r['name_offsets']
        renamed=r['command'][:a]+b'solution'+r['command'][b:]
        need(raw.endswith(renamed+b'\n') and digest(renamed[renamed.index(b':='):])==r['proof_suffix_sha256'],'Parent original full proof suffix changed')
        files[solution_file(parent)]=raw
    files[SOURCE_SNAPSHOT]=snapshot(u,None,final)[0]
    for parent in [NORM,ACTUAL]:files[GENERATED_SNAPSHOTS[parent]]=snapshot(u,parent,final)[0]
    for n,r in u.items():files['source-commands/'+n.replace('.','_')+'.lean.txt']=r['command']
    metadata={}
    descriptions={
      NORM:r'For original fixed data $d$, $\nu\ge0$, $H>0$, a column selection and a choice family $f$, the norm of the literal summand $\bigl(\prod_r choiceScalar_d(r,f(r))\bigr)\det(choiceMatrix_d(selection,f))$ is at most the exponential with exactly the source collision, analytic-error and mean-row-weight exponent.',
      route.LITERAL+'actual_minor_expansion':r'The original selected-minor determinant equals the finite sum, over choice families $f$, of the original scalar product times the choice-matrix determinant.',
      route.LITERAL+'card_choiceFamily_le':r'The number of choice families is at most $translationTermCount(d.m,d.v_0,H)^{actualRowCount_d(H)}$ under the exact source hypotheses.',
      route.LITERAL+'actualRowCount_pos':r'For original fixed data $d$ and $H>0$, the actual row count is positive: $actualRowCount_d(H)>0$.',
      route.LITERAL+'indexWeight_nonneg':r'Each transverse index has nonnegative weight: $indexWeight_d(a)\ge0$.',
      route.LITERAL+'rowWeight_le_indexWeight_of_ne_zero':r'If the original scalar for row $r$ and row choice $t$ is nonzero, then $rowWeight_d(r)\le indexWeight_d(t.1)$.',
      route.LITERAL+'sum_rowWeight_eq':r'For $H>0$, the total row weight satisfies $\sum_r rowWeight_d(r)=actualRowCount_d(H)\,H\,actualMean_d(H)$.',
      route.LITERAL+'low_transverse_capacity':r'The number of transverse indices of weight at most $d.A\,H$ is at most $lowIndexCount_d(H)$.',
      route.LITERAL+'lowIndexCount_pos':r'For $H>0$, the low-index count is positive: $lowIndexCount_d(H)>0$.',
      route.LITERAL+'norm_scalar_product_le':r'For $\nu\ge0$ and $H>0$, the original scalar product norm is bounded by the exponential of the source weight difference and translation-error budget.',
      route.LITERAL+'norm_choiceMatrix_le':r'For $H>0$, the original choice-matrix determinant norm is bounded by the exponential of its source multiplicity-square collision penalty and holomorphic-error budget.'}
    for n in NEW_NAMES:
        r=u[n];metadata[n]={'theorem_name':n,'theorem_title':'Original '+n.rsplit('.',1)[1].replace('_',' '),
          'natural_language_statement':descriptions[n]+' All binders, finite domains and hypotheses are precisely the accompanying original formal statement.',
          'source':'https://github.com/openai/math/blob/'+data.COMMIT+'/lean/'+r['source_module'].replace('.','/')+'.lean#L'+str(r['source_lines'][0])+'-L'+str(r['source_lines'][1]),
          'tags':['number-theory','openai-pi-exponent-017']}
    plan={'schema_version':1,'artifact_kind':'ap20-analytic-translated-two-layer-pending-candidate','source_commit':data.COMMIT,
      'existing_actual_parent_id':ACTUAL_ID,'existing_actual_parent_name':ACTUAL,'parent_wire_unchanged':True,'parent_existing_wire_sha256':digest(files['parent-existing-wire.lean']),
      'new_analytic_names':NEW_NAMES,'new_analytic_name_count':11,'interface_names':INTERFACE_NAMES,'graph_children':CHILDREN,
      'server_Proved_children':{n:leaves[n]['accepted'] for n in ACCEPTED},'local_accepted_leaf_role':'comparator placeholders only; server Accepted status is distinct from local sorry values',
      'wire_interfaces':wires,'academic_metadata':metadata,'exact_source_units':{n:{k:v for k,v in r.items() if k!='command'} for n,r in u.items()},
      'original_parent_proof_suffix_sha256':{n:u[n]['proof_suffix_sha256'] for n in [NORM,ACTUAL]},
      'publication_sequence':['publish norm plus seven norm siblings; verify norm sketch using genuinely Proved translated target',
        'publish three remaining actual siblings; verify existing actualMinor using norm and genuinely Proved log_norm_sum_le'],
      'final_gates':['actual seventeen-Def fulltype/value/owner/Std3 certificate','actual seventeen-Def PUBLISHED exact-byte readback'],
      'reused_existing_actual_parent_OLean':True,'Open_sketch_only':True,'closed_proof':False,'generated_Std3_only':False,
      'local_placeholder_sorryAx_expected':True,'source_original_Std3_expected':True,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False}
    files['pending-preparation.json']=encode(plan);return files

def boundary():
    global _BOUNDARY
    if _BOUNDARY is not None:
        pins,external,report=_BOUNDARY
        for p,h in pins.items():need(sha(TASK/p)==h,'Fixed graph boundary changed: '+p)
        for p,h in external.items():need(sha(Path(p))==h,'Fixed graph external OLean changed: '+p)
        return dict(pins),dict(external),report
    need(data.CERTIFICATE.exists() and PUBLICATION.exists(),'Actual17Def certificate and Published boundary remain pending')
    cert=read(data.CERTIFICATE);actual=data_consumer.validate('interface')
    need(encode(actual)==data.CERTIFICATE.read_bytes() and cert['validated'] and cert['Std3_only'],'First complete actual17Def replay differs')
    pub=read(PUBLICATION);b=pub['target_readback']['body'];raw=(data.STAGE/data.PROVIDER_FILE).read_bytes()
    need(pub['last_publish_verdict']['body']['status']=='PUBLISHED' and b['status']=='Definition' and b['definition'].encode()==raw
         and b['theorem_id']==pub['definition_id']==pub['last_publish_verdict']['body']['theorem_id'],'Actual17Def Published exact-byte boundary differs')
    prior=read(PRIOR_CERT);need(sha(PRIOR_CERT)=='5f3ebfb439c0324206140d2db54cb3626018b75b461df5d515829b969e83257d' and prior['validated'] and prior['Open_sketch_only'],'Genuine existing actualMinor OLean certificate changed')
    module=theorem_module(ACTUAL);ole=prior['emitted_oleans'][module]
    need(sha(TASK/ole['path'])==ole['sha256'] and (PRIOR_STAGE/theorem_file(ACTUAL)).read_bytes()==candidate_files()['parent-existing-wire.lean'],'Existing actualMinor comparator/OLean differs from original published wire')
    prep=read(data.STAGE/'preparation.json');pins=dict(prep['input_hashes']);external=dict(prep['external_dependency_olean_hashes']);pins.update(cert['implementation_hashes']);pins.update(cert['output_json_sha256'])
    for rec in cert['preflights'].values():data.historical(rec,pins,external)
    data.historical(prior['preflights'][theorem_file(ACTUAL)],pins,external)
    for p in [SELF,CONSUMER,Path(data.__file__),Path(data_consumer.__file__),Path(route.__file__),Path(source_root.__file__),SOURCE_CORE,RUNNER,RUNTIME,LOOKUP,route.STAGE/'report.json',data.CERTIFICATE,PUBLICATION,data.STAGE/'preparation.json',PRIOR_CERT,TASK/ole['path']]:pins[rel(p)]=sha(p)
    for name,leaf in read(route.STAGE/'report.json')['accepted_public_boundaries'].items():pins[leaf['publication_record']]=leaf['publication_record_sha256']
    report={'data_definition_id':pub['definition_id'],'data_certificate_sha256':sha(data.CERTIFICATE),'data_publication_sha256':sha(PUBLICATION),
      'data_provider_olean':cert['provider_olean'],'data_provider_olean_sha256':cert['provider_olean_sha256'],
      'exact_observed_data_closed_Prop_pairs':cert['actual_source_generated_closed_Prop_CI_pairs'],
      'CoreData_certified_closed_Prop_pair':prep['inherited_provider_binding']['CoreData_actual_closed_Prop_pair'],
      'existing_actual_parent_olean':ole,'existing_actual_parent_certificate_sha256':sha(PRIOR_CERT),'platform_proved_leaf_local_values_are_placeholders':True}
    _BOUNDARY=(dict(pins),dict(external),report);return pins,external,report

def final_files():
    pins,external,report=boundary();u=units();files=candidate_files(True);plan=read(CANDIDATE/'pending-preparation.json')
    for name,raw in candidate_files().items():
        path=CANDIDATE/name;need(path.read_bytes()==raw,'Candidate changed before finalization: '+name);pins[rel(path)]=sha(path)
    order=[theorem_file(n) for n in NEW_NAMES+ACCEPTED]+[solution_file(n) for n in [NORM,ACTUAL]]+[SOURCE_SNAPSHOT]+[GENERATED_SNAPSHOTS[n] for n in [NORM,ACTUAL]]
    rows={};commands=[]
    for i,f in enumerate(order,1):
        imports=[l.removeprefix('import ').strip() for l in files[f].decode().splitlines() if l.startswith('import ')];mode='modecheck' if f in [SOURCE_SNAPSHOT]+list(GENERATED_SNAPSHOTS.values()) else 'emit-olean'
        mf=f'c{i}.json';files[mf]=encode({'schema_version':1,'artifact_kind':'ap20-two-layer-Open-sketch-bounded-manifest','output':workspace_rel(STAGE/f),'output_sha256':digest(files[f]),
          'imports':imports,'input_hashes':pins,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,
          'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(data.base.base.PREFLIGHT),'validated':False,'submission_ready':False})
        rows[f]={'manifest':mf,'mode':mode,'imports':imports,'sha256':digest(files[f])}
        commands.append('& '+repr(data.base.PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap20/analytic-translated-two-layer-reduction-final/'+f+' --root ap20/analytic-translated-two-layer-reduction-final --imports-manifest ap20/analytic-translated-two-layer-reduction-final/'+mf+' --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    plan.update({'artifact_kind':'ap20-analytic-translated-two-layer-Open-sketch-final-preparation','boundary':report,'input_hashes':pins,'external_dependency_olean_hashes':external,
      'files':rows,'commands':commands,'final_compiler_manifests_created':True,'actual_owned_CIs_exported_before_classification':True,'whole_environment_ModuleIdx_first_inventory':True})
    files.pop('pending-preparation.json');files['preparation.json']=encode(plan);files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def write_exact(directory,files,write):
    for f,raw in files.items():
        p=directory/f
        if p.exists():need(p.read_bytes()==raw,'Refusing overwrite: '+str(p))
        elif write:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
        else:need(False,'Missing staged output: '+str(p))
    return {'checked_files':len(files),'Open_sketch_only':True,'closed_proof':False,'Lean_started':False,'API_used':False}
def check_only():return write_exact(STAGE,final_files(),False)
def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare-candidate',action='store_true');g.add_argument('--check-candidate',action='store_true');g.add_argument('--finalize',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    files=candidate_files() if a.prepare_candidate or a.check_candidate else final_files()
    result=write_exact(CANDIDATE if a.prepare_candidate or a.check_candidate else STAGE,files,a.prepare_candidate or a.finalize)
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
