"""Pure AP17 original-name generic lower mirror; genuine AP16 evidence gates finalization."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_arithmetic_lower_bound_node as parent
import stage_selected_minor_clearing_child_mirror_probe_v4 as mechanism
import validate_namespace_context_providers as context
TASK,ROOT,V=parent.TASK,parent.ROOT,parent.V
SELF=Path(__file__).resolve();STAGE=V/'ap17/generic-lower-child-mirror'
MODULE=parent.TARGET_OUTPUT[:-5].replace('/','.');OUTPUT=parent.TARGET_OUTPUT
SNAPSHOT='GeneratedSnapshot.lean';TYPE_JSON=parent.GENERATED_TYPE_JSON;REFS_JSON=parent.GENERATED_REFS_JSON
MAPPING_JSON='actual-private-mapping.json';CERTIFICATE='local-child-validation.json'
PARENT_CERTIFICATE=parent.STAGE/'validation-v2/node-validation.json'
CANDIDATE='mirror-candidate.lean.txt';PROBE_CANDIDATE='snapshot-candidate.lean.txt'
ACCEPTED=STAGE/'accepted-publication-record.json'
EQUATIONS=[]
primary_evidence=mechanism.primary_evidence
AUTOMATIC_CERT=V/'ap16/clearing-child-mirror-validation-v5/local-child-validation.json'
RUNNER=mechanism.RUNNER;LEGACY_RUNNER=mechanism.LEGACY_RUNNER
CONSUMER=TASK/'scripts/certify_selected_minor_lower_child_mirror.py'
read,sha,sha_bytes,encode,need,rel=parent.read,parent.sha,parent.sha_bytes,parent.encode,parent.need,parent.rel

def automatic_evidence():
    cert=read(AUTOMATIC_CERT)
    need(sha(AUTOMATIC_CERT)=='ba85c8b9e7d14528932616692af87e09ac3599ab86313fd3bd1c350863edcaf9' and cert['validated'] is True and cert['Std3_only'] is True,'Genuine automatic data-helper certificate differs')
    pair=cert['actual_closed_automatic_data_helper_pair']
    source_file=mechanism.parent.STAGE/mechanism.parent.SOURCE_REFS_JSON
    generated_file=mechanism.STAGE/mechanism.REFS_JSON
    source=next(r for r in read(source_file)['rows'] if r['name']==pair['name'])
    generated=next(r for r in read(generated_file)['rows'] if r['name']==pair['name'])
    need(sha_bytes(encode(source))==pair['source_complete_CI_sha256'] and sha_bytes(encode(generated))==pair['generated_complete_CI_sha256'],'Actual automatic full CI historical pair differs')
    return {'certificate':rel(AUTOMATIC_CERT),'certificate_sha256':sha(AUTOMATIC_CERT),'pair':pair,'source_json':rel(source_file),'source_json_sha256':sha(source_file),'generated_json':rel(generated_file),'generated_json_sha256':sha(generated_file)},[AUTOMATIC_CERT,source_file,generated_file]

def candidate_files():
    parent.route.check_only()
    graph,closure,provided,rows,commands,pins,lcm=parent.route.source_units()
    names=[r['name'] for r in rows];helpers=names[:-1]
    need(len(names)==22 and names[-1]==parent.TARGET,'Exact generic lower 22-CI source order differs')
    parts=[(''.join('import '+m+'\n' for m in parent.IMPORTS)+'\n').encode()];edits=[]
    for module,units in commands.items():
        namespace=parent.PREFIXES[module][:-1]
        parts.append(('namespace '+namespace+'\n\n'+'\n'.join(parent.clearing.scope_context(module))+'\n\n').encode())
        for _,name,raw in units:
            row=next(r for r in rows if r['name']==name);vs=row['ast']['valueStart']['offset']-row['start']
            need(raw.startswith(b'theorem ') and raw[vs:vs+2]==b':=','Original lower AST is not a plain theorem/proof')
            modified=raw if name==parent.TARGET else b'private '+raw
            need(modified[vs+(0 if name==parent.TARGET else 8):]==raw[vs:],'Private visibility changed source proof')
            parts.append(modified+b'\n\n')
            edits.append({'source_name':name,'source':row['source'],'source_byte_range':[row['start'],row['end']],'original_command_sha256':sha_bytes(raw),'mirror_command_sha256':sha_bytes(modified),'proof_suffix_sha256':sha_bytes(raw[vs:]),'private_visibility_prefix_only':name!=parent.TARGET,'proof_suffix_unchanged':True})
        parts.append(('end '+namespace+'\n\n').encode())
    body=b''.join(parts);need(body.count(b'private theorem ')==21 and b'theorem solution' not in body and b'import Solutions.' not in body and b'sorry' not in body,'Generic lower mirror public/private boundary differs')
    boundary=closure&provided
    raw=parent.snapshot('generated',names,boundary).decode()
    raw=raw.replace(parent.SOLUTION_MODULE,MODULE).replace(parent.workspace_rel(parent.STAGE),parent.workspace_rel(STAGE))
    evidence,paths=mechanism.primary_evidence();automatic,automatic_paths=automatic_evidence();paths+=automatic_paths
    decl='def certifiedPrimaries : Array (Name × String) := #['+', '.join('(`'+r['name']+', '+json.dumps(r['module'])+')' for r in evidence)+']\n'
    resolver=mechanism.RESOLVER.replace('def resolveRoots',decl+'def certifiedAutomaticDataHelpers : Array Name := #[`'+automatic['pair']['name']+']\n\ndef resolveRoots',1).replace('ClearingPrivateMirrorSnapshot','GenericLowerPrivateMirrorSnapshot')
    anchor='      dataEquations := dataEquations.push <| Json.mkObj ['
    extra='''      let mut automaticDataHelpers : Array Json := #[]
      let some proofValue := valueOf equationCI
        | throwError "Auxiliary equation proof value missing"
      for used in refs (mkApp equationCI.type proofValue) do
        if certifiedAutomaticDataHelpers.contains used then
          let helperCI ← getConstInfo used
          unless (← isProp helperCI.type) do
            throwError "Certified automatic data helper is not a genuine Prop CI"
          automaticDataHelpers := automaticDataHelpers.push <| Json.mkObj [
            ("actualIsProp",toJson true),("CI",Json.mkObj (← ciRow used true))]
'''
    need(resolver.count(anchor)==1,'Auxiliary helper metadata insertion anchor differs')
    resolver=resolver.replace(anchor,extra+anchor,1).replace('("closedEquationProofReferences",Json.mkObj (← ciRow n true))]', '("closedEquationProofReferences",Json.mkObj (← ciRow n true)),\n        ("actualCertifiedAutomaticDataHelpers",Json.arr automaticDataHelpers)]',1)
    marker='run_meta do\n';need(raw.count(marker)==1,'Generic lower snapshot run_meta anchor differs')
    raw=raw.replace(marker,resolver+'\n'+marker,1)
    static='#['+', '.join('`'+n for n in names)+']'
    helper_array='#['+', '.join('`'+n for n in helpers)+']'
    init='  let roots ← GenericLowerPrivateMirrorSnapshot.resolveRoots '+helper_array+' `'+parent.TARGET+' #[] '+json.dumps(MODULE)+' '+json.dumps(parent.workspace_rel(STAGE/MAPPING_JSON))+'\n'
    anchor='  PiExponentInterfaceSnapshot.exportSnapshot '+static
    need(raw.count(anchor)==1 and raw.count(static)==2,'Generic lower exact root-array anchors differ')
    raw=raw.replace(anchor,init+'  PiExponentInterfaceSnapshot.exportSnapshot roots',1).replace(' '+static+' #[',' roots #[',1)
    need(raw.count('env.constants.toList')==1,'Private lower name inventory is not one-pass')
    inputs=dict(pins)
    for p in [SELF,parent.route.SELF,mechanism.SELF,mechanism.CONSUMER,RUNNER,LEGACY_RUNNER,CONSUMER,parent.route.STAGE/'route-preparation.json',*paths]:inputs[rel(p)]=sha(p)
    outputs={CANDIDATE:body,PROBE_CANDIDATE:raw.encode()}
    for row,edit in zip(rows,edits,strict=True):
        command=(TASK/row['source']).read_bytes()[row['start']:row['end']]
        outputs['source-units/'+row['name'].replace('.','_')+'.lean.txt']=(b'private ' if edit['private_visibility_prefix_only'] else b'')+command
    outputs['candidate-spec.json']=encode({'schema_version':1,'artifact_kind':'ap17-generic-lower-private-mirror-candidate','source_name':parent.TARGET,'source_commit':parent.COMMIT,'platform_module':MODULE,'imports':parent.IMPORTS,'source_type_only_names':names,'private_helper_names':helpers,'public_platform_boundary_names':[parent.TARGET],'private_helper_count':21,'original_AST_count':22,'original_source_lines':247,'source_units':rows,'visibility_edits':edits,'all_proof_suffixes_unchanged':True,'provider_subtracted_names':sorted(boundary),'certified_auxiliary_primary_definitions':evidence,'certified_historical_automatic_data_helper_pair':automatic,'data_auxiliary_provenance_mechanism':'one-pass inventory + exact full Published Def + nullable registry results + closed forall/Eq no-approximation defEq','mechanism_sha256':sha(mechanism.SELF),'candidate_sha256':sha_bytes(body),'snapshot_candidate_sha256':sha_bytes(raw.encode()),'required_AP16_source_certificate':rel(PARENT_CERTIFICATE),'real_AP16_certificate_pending':True,'real_Accepted_Proved_boundary_pending':True,'compiler_manifests_finalized':False,'input_hashes':inputs,'validated':False,'submission_ready':False,'Lean_started':False,'API_used':False})
    return outputs

def check_candidate():
    outputs=candidate_files()
    for name,raw in outputs.items():need((STAGE/name).read_bytes()==raw,'Immutable generic mirror candidate differs: '+name)
    return {'checked_files':len(outputs),'private_helpers':21,'original_AST_units':22,'public_platform_boundary_names':[parent.TARGET],'real_AP16_certificate_and_Accepted_pending':True,'compiler_manifests_finalized':False,'Lean_started':False,'API_used':False}

def final_files():
    check_candidate();certificate=PARENT_CERTIFICATE
    need(certificate.is_file(),'Final mirror contexts await genuine AP16 kernel certificate')
    import certify_selected_minor_arithmetic_lower_bound_node_v2 as source_consumer
    previous=source_consumer.validate();need(encode(previous)==certificate.read_bytes(),'Actual AP16 source certificate does not replay exactly')
    need(previous['validated'] is True and previous['Std3_only'] is True and previous['source_and_generated_types_equal'] is True,'Actual generic source certificate differs')
    p=read(STAGE/'candidate-spec.json');inputs=dict(p['input_hashes'])
    source_olean=TASK/previous['solution_olean'];need(sha(source_olean)==previous['solution_olean_sha256'],'Actual AP16 generic source solution OLean differs')
    for path in [parent.SELF,Path(source_consumer.__file__),certificate,source_olean,parent.STAGE/'preparation.json',parent.STAGE/parent.SOURCE_TYPE_JSON,parent.STAGE/parent.SOURCE_REFS_JSON,STAGE/'candidate-spec.json',STAGE/CANDIDATE,STAGE/PROBE_CANDIDATE]:inputs[rel(path)]=sha(path)
    for f,h in previous['json_sha256'].items():need(sha(parent.STAGE/f)==h,'Certified AP16 kernel JSON changed');inputs[rel(parent.STAGE/f)]=h
    for pf in previous['preflights'].values():
        for key in ['source','manifest','log']:
            path=context.file(pf['data'][key]);inputs[rel(path)]=sha(path)
        path=TASK/pf['record'];inputs[rel(path)]=sha(path)
    files={OUTPUT:(STAGE/CANDIDATE).read_bytes(),SNAPSHOT:(STAGE/PROBE_CANDIDATE).read_bytes()};commands=[]
    for i,(output,imports,mode) in enumerate([(OUTPUT,parent.IMPORTS,'emit-olean'),(SNAPSHOT,['Lean',MODULE],'modecheck')],1):
        files[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap17-generic-private-lower-mirror-bounded-manifest','output':parent.workspace_rel(STAGE/output),'output_sha256':sha_bytes(files[output]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(parent.clearing.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'validated':False,'submission_ready':False})
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '+parent.verification_rel(STAGE/output)+' --root ap17/generic-lower-child-mirror --imports-manifest ap17/generic-lower-child-mirror/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    prep=dict(p);prep.update({'artifact_kind':'ap17-generic-private-lower-mirror-kernel-preparation','real_AP16_certificate_pending':False,'historical_source_certificate_sha256':sha(certificate),'compiler_manifests_finalized':True,'platform_boundary_certification_pending':True,'Accepted_readback_not_compiler_input':True,'input_hashes':inputs,'compile_commands':commands})
    files['preparation.json']=encode(prep);files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def check_only():
    p=read(STAGE/'preparation.json');need(p['compiler_manifests_finalized'] is True and p['platform_boundary_certification_pending'] is True and p['Accepted_readback_not_compiler_input'] is True and p['private_helper_count']==21 and p['public_platform_boundary_names']==[parent.TARGET],'Final generic kernel preparation boundary differs')
    need(sha(PARENT_CERTIFICATE)==p['historical_source_certificate_sha256'],'Pinned genuine AP16 source certificate differs')
    for i,(f,candidate,imports,mode) in enumerate([(OUTPUT,CANDIDATE,parent.IMPORTS,'emit-olean'),(SNAPSHOT,PROBE_CANDIDATE,['Lean',MODULE],'modecheck')],1):
        need((STAGE/f).read_bytes()==(STAGE/candidate).read_bytes(),'Final generic kernel source differs from original AST candidate')
        m=read(STAGE/f'c{i}.json');need(m['imports']==imports and m['mode']==mode and m['timeout_seconds']==300 and m['output_sha256']==sha(STAGE/f) and m['input_hashes']==p['input_hashes'],'Final generic manifest/schema differs')
        parent.clearing.base.runner.verify_manifest_inputs(m);parent.clearing.base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':6,'platform_boundary_certification_pending':True,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    for flag in ['prepare-candidate','check-candidate','prepare-kernel','check-only']:g.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    if a.prepare_candidate or a.prepare_kernel:
        for name,raw in (final_files() if a.prepare_kernel else candidate_files()).items():
            path=STAGE/name
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+name)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only() if a.prepare_kernel or a.check_only else check_candidate(),indent=2))
if __name__=='__main__':main()
