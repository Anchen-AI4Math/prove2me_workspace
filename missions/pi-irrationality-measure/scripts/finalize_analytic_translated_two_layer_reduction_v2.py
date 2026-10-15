"""Isolated missing-Multiplicity import successor; reuse ten genuine unmodified emitters."""
from __future__ import annotations
import argparse,json
from contextlib import contextmanager
from pathlib import Path
import finalize_analytic_translated_two_layer_reduction as legacy

TASK,ROOT,V=legacy.TASK,legacy.ROOT,legacy.V
SELF=Path(__file__).resolve();OLD_STAGE=legacy.STAGE
STAGE=V/'ap20/analytic-translated-two-layer-reduction-final-v2'
CONSUMER=TASK/'scripts/certify_analytic_translated_two_layer_reduction_v2.py'
CERTIFICATE=STAGE/'open-sketch-interface-validation-v2.json'
MULT_STAGE=V/'ap18/multiplicity';MULT_CERT=MULT_STAGE/'actual-provider-validation.json'
MULT_PUB=MULT_STAGE/'publication-v2/publication.json'
MULT_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity'
CANONICAL_SOURCE=V/'graph-source-root-20261011/canonical-approximation-definitions.lean.txt'
CANONICAL_ALIGNMENT=V/'graph-bridge-20261011/canonical-olean-cache-alignment.json'
MISSING_CI='OAI.PiExponent.Collision.multiplicity'
CHANGED_NAME=legacy.route.LITERAL+'norm_choiceMatrix_le'
read,sha,encode,digest,need,rel,workspace_rel=legacy.read,legacy.sha,legacy.encode,legacy.digest,legacy.need,legacy.rel,legacy.workspace_rel
for _n in ['ACTUAL','NORM','CHILDREN','NEW_NAMES','ACCEPTED','INTERFACE_NAMES','ACTUAL_ID','SOURCE_SNAPSHOT','SOURCE_JSON','SOURCE_AUX_JSON',
           'GENERATED_SNAPSHOTS','GENERATED_JSON','OWNED_JSON','SOLUTION_MODULES','SOURCE_CORE','RUNNER','RUNTIME','LOOKUP','LOOKUP_SHA','CANDIDATE','data','data_consumer','source_root','route']:
    globals()[_n]=getattr(legacy,_n)
theorem_module,theorem_file,solution_file,units=legacy.theorem_module,legacy.theorem_file,legacy.solution_file,legacy.units
_FILES=None

@contextmanager
def relocated():
    saved={k:getattr(legacy,k) for k in ['STAGE','SELF','CONSUMER']}
    legacy.STAGE,legacy.SELF,legacy.CONSUMER=STAGE,SELF,CONSUMER
    try:yield
    finally:
        for k,v in saved.items():setattr(legacy,k,v)

def multiplicity_binding(pins,external):
    cert=read(MULT_CERT);pub=read(MULT_PUB);body=pub['target_readback']['body'];provider=MULT_STAGE/(MULT_MODULE.replace('.','/')+'.lean')
    need(cert['validated'] and cert['Std3_only'] and cert['definition_values_equal_and_exported'] and cert['provided_names']==[MISSING_CI]
         and cert['platform_module']==MULT_MODULE and pub['definition_id']==body['theorem_id']==pub['last_publish_verdict']['body']['theorem_id']=='9e7cfb76-3480-4078-b240-661c13a8f231'
         and pub['last_publish_verdict']['body']['status']=='PUBLISHED' and body['status']=='Definition' and body['definition'].encode()==provider.read_bytes()
         and cert['provider_source_sha256']==sha(provider) and sha(TASK/cert['provider_olean'])==cert['provider_olean_sha256'], 'Actual Published Multiplicity full-Def/Std3/OLean differs')
    for p in [MULT_CERT,MULT_PUB,provider,MULT_STAGE/'preparation.json',TASK/cert['provider_olean']]:pins[rel(p)]=sha(p)
    pins.update(cert['implementation_hashes']);pins.update(cert['output_json_sha256']);pins.update(read(MULT_STAGE/'preparation.json')['input_hashes'])
    for rec in cert['preflights'].values():data.historical(rec,pins,external)
    return {'definition_id':pub['definition_id'],'module':MULT_MODULE,'provided_names':[MISSING_CI],'certificate':rel(MULT_CERT),'certificate_sha256':sha(MULT_CERT),
      'publication':rel(MULT_PUB),'publication_sha256':sha(MULT_PUB),'provider_olean':cert['provider_olean'],'provider_olean_sha256':cert['provider_olean_sha256'],
      'source_generated_full_Def_types_values_equal':True,'Std3_only':True}

def type_import_audit(files):
    """All14 source type roots, recursive Def values, actual literal provider import closure."""
    graph={r['name']:r for r in map(json.loads,data.base.base.GRAPH.read_text(encoding='utf-8').splitlines())}
    report=read(route.STAGE/'report.json');baseline=read(route.BASELINE);providers={}
    for r in baseline['definitions']:
        p=read(TASK/r['publication_record']);name=p['publish_intent']['payload']['definition_name'];module='Definitions.Def_'+name
        coverage=next(x for x in report['actual_Published31_coverage'] if x['definition_id']==r['definition_id'])
        providers[module]={'names':set(coverage['actual_source_graph_names']),'wire':p['target_readback']['body']['definition']}
    providers[data.PLATFORM_MODULE]={'names':set(data.NAMES),'wire':read(data.STAGE/'publication/publication.json')['target_readback']['body']['definition']}
    canonical='Definitions.Def_OAI_PiExponent_ApproximationDefinitions'
    raw=CANONICAL_SOURCE.read_bytes();shared=ROOT/(canonical.replace('.','/')+'.lean')
    aligned=next(r for r in read(CANONICAL_ALIGNMENT)['copied_existing_compiled_canonical_modules'] if r['module']==canonical)
    need(raw==shared.read_bytes() and aligned['byte_identical'] and sha(Path(aligned['source']))==sha(Path(aligned['destination']))==aligned['sha256'],
         'Existing campaign canonical source/OLean alignment differs')
    providers[canonical]={'names':set(route.literal_public_names(raw.decode(),graph)),'wire':raw.decode()}
    need(MULT_MODULE in providers and MISSING_CI in providers[MULT_MODULE]['names'],'Multiplicity actual31 literal CI coverage differs')
    rows=[]
    for n in INTERFACE_NAMES:
        imports=[l[7:].strip() for l in files[theorem_file(n)].decode().splitlines() if l.startswith('import ')] if theorem_file(n) in files else [l[7:].strip() for l in files['parent-existing-wire.lean'].decode().splitlines() if l.startswith('import ')]
        todo=[m for m in imports if m.startswith('Definitions.')];seen=set();available=set()
        while todo:
            m=todo.pop()
            if m in seen:continue
            seen.add(m);need(m in providers,'Imported platform Definition has no exact Published provider witness: '+m)
            available.update(providers[m]['names']);todo.extend(l[7:].strip() for l in providers[m]['wire'].splitlines() if l.startswith('import Definitions.'))
        wanted=set();todo=list(graph[n]['typeDeps'])
        while todo:
            p=todo.pop()
            if p in wanted:continue
            wanted.add(p);g=graph[p];todo+=g['typeDeps']
            if g['kind']!='theorem':todo+=g['valueDeps']
        missing=sorted(p for p in wanted if graph[p]['kind']!='theorem' and p not in available)
        need(not missing,'Actual complete14 source type/import closure has missing provider: '+n+':'+repr(missing))
        rows.append({'name':n,'imports':imports,'actual_Published_Definition_import_closure':sorted(seen),
          'source_graph_type_and_Def_value_dependencies':sorted(wanted),'missing_data_CIs':missing})
    return {'schema_version':1,'artifact_kind':'ap20-all14-source-type-transitive-Published-provider-import-closure-audit',
      'source_names':INTERFACE_NAMES,'type_root_count':14,'rows':rows,'all_missing_data_domains_empty':True,
      'existing_canonical_campaign_module_not_counted_as_own_Published32':{'module':canonical,'source':rel(CANONICAL_SOURCE),'source_sha256':sha(CANONICAL_SOURCE),
        'alignment':rel(CANONICAL_ALIGNMENT),'alignment_sha256':sha(CANONICAL_ALIGNMENT),'olean_sha256':aligned['sha256']},
      'actual_kernel_full14_type_equivalence_remains_required_by_new_source_generated_snapshots':True}

def final_files():
    global _FILES
    if _FILES is not None:
        for p,h in read(STAGE/'preparation.json')['input_hashes'].items():need(sha(TASK/p)==h,'Frozen successor input changed')
        return dict(_FILES)
    with relocated():files=legacy.final_files()
    plan=json.loads(files['preparation.json']);pins=plan['input_hashes'];external=plan['external_dependency_olean_hashes']
    pins[rel(Path(legacy.__file__))]=sha(Path(legacy.__file__))
    pins[rel(TASK/'scripts/certify_analytic_translated_two_layer_reduction.py')]=sha(TASK/'scripts/certify_analytic_translated_two_layer_reduction.py')
    for p in [CANONICAL_SOURCE,CANONICAL_ALIGNMENT]:pins[rel(p)]=sha(p)
    for r in read(CANONICAL_ALIGNMENT)['copied_existing_compiled_canonical_modules']:
        for k in ['source','destination']:
            p=Path(r[k])
            try:pins[rel(p)]=sha(p)
            except ValueError:external[str(p)]=sha(p)
    binding=multiplicity_binding(pins,external)
    name=theorem_file(CHANGED_NAME);old_wire=(OLD_STAGE/name).read_bytes()
    files[name]=('import '+MULT_MODULE+'\n').encode()+old_wire
    plan['wire_interfaces'][CHANGED_NAME]['preamble']='import '+MULT_MODULE+'\n'+plan['wire_interfaces'][CHANGED_NAME]['preamble']
    audit=type_import_audit(files);files['type-import-closure-audit.json']=encode(audit)
    old_plan=read(OLD_STAGE/'preparation.json');reused={};commands=[]
    ordered=list(plan['files'])
    for i,f in enumerate(ordered,1):
        mf=f'c{i}.json'
        if i<=10:
            need(files[f]==(OLD_STAGE/f).read_bytes(),'Reused comparator source bytes differ')
            r=old_plan['files'][f];rec=data.context.record(OLD_STAGE/f,OLD_STAGE/r['manifest'],r['mode'],'.'.join(Path(f).with_suffix('').parts),OLD_STAGE)
            data.historical(rec,pins,external);reused[f]={'source':rel(OLD_STAGE/f),'manifest':rel(OLD_STAGE/r['manifest']),'root':rel(OLD_STAGE),'preflight':rec}
            files.pop(mf,None);plan['files'][f]['manifest']=r['manifest'];plan['files'][f]['actual_context_reused']=True
            continue
        imports=[l[7:].strip() for l in files[f].decode().splitlines() if l.startswith('import ')];r=plan['files'][f];r['imports']=imports;r['sha256']=digest(files[f]);r['actual_context_reused']=False
        m=json.loads(files[mf]);m.update({'artifact_kind':'ap20-two-layer-Multiplicity-import-successor-bounded-manifest','output_sha256':digest(files[f]),'imports':imports,'input_hashes':pins})
        files[mf]=encode(m)
        commands.append('& '+repr(data.base.PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap20/analytic-translated-two-layer-reduction-final-v2/'+f+' --root ap20/analytic-translated-two-layer-reduction-final-v2 --imports-manifest ap20/analytic-translated-two-layer-reduction-final-v2/'+mf+' --timeout-seconds 300'+(' --emit-olean' if r['mode']=='emit-olean' else ''))
    failed=(OLD_STAGE/name).with_name(Path(name).name+'.preflight.json');d=read(failed)
    need(not d['success'] and d['exit_code']!=0 and not d['timed_out'],'Prior c11 missing-import failure was not preserved')
    for p in [failed,data.context.file(d['log']),OLD_STAGE/'preparation.json',OLD_STAGE/'c11.json',OLD_STAGE/name]:pins[rel(p)]=sha(p)
    plan.update({'artifact_kind':'ap20-analytic-translated-two-layer-Multiplicity-import-successor-final-preparation','reused_actual_contexts':reused,
      'reused_context_count':10,'new_bounded_context_count':8,'commands':commands,'multiplicity_binding':binding,
      'full14_source_type_import_closure_audit_sha256':digest(files['type-import-closure-audit.json']),
      'legacy_failure':{'record':rel(failed),'record_sha256':sha(failed),'log':d['log'],'log_sha256':d['log_sha256'],'reason':'Unknown identifier Collision.multiplicity; comparator missing actual Published Definition import'},
      'only_comparator_math_change':'none; one exact actual Published Definition import added to norm_choiceMatrix_le preamble',
      'original_parent_proof_bytes_unchanged':True})
    # Every successor manifest pins the complete final provenance (including old actual contexts/failure).
    for i in range(11,19):m=json.loads(files[f'c{i}.json']);m['input_hashes']=dict(pins);files[f'c{i}.json']=encode(m)
    files['preparation.json']=encode(plan);files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();_FILES=dict(files);return files

def check_only():return legacy.write_exact(STAGE,final_files(),False)
def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--finalize',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    print(json.dumps(legacy.write_exact(STAGE,final_files(),a.finalize),indent=2))
if __name__=='__main__':main()
