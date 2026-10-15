"""Pure pending AP16 clearing mirror; original proofs, 18 private helpers, one public target.

Final bounded compiler manifests are deliberately absent until the actual AP15
certificate and Accepted/Proved publication evidence are available and pinned.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_selected_minor_clearing_bound_node as parent
TASK,ROOT,V=parent.TASK,parent.ROOT,parent.V;SELF=Path(__file__).resolve();STAGE=V/'ap16/clearing-child-mirror'
MODULE=parent.TARGET_OUTPUT[:-5].replace('/','.');OUTPUT=parent.TARGET_OUTPUT;SNAPSHOT='GeneratedSnapshot.lean';CERTIFICATE='local-child-validation.json'
TYPE_JSON,REFS_JSON=parent.GENERATED_TYPE_JSON,parent.GENERATED_REFS_JSON
MAPPING_JSON='actual-private-mapping.json';CANDIDATE='mirror-candidate.lean.txt';PROBE_CANDIDATE='generated-snapshot-candidate.lean.txt'
read,sha,sha_bytes,encode,need,rel=parent.read,parent.sha,parent.sha_bytes,parent.encode,parent.need,parent.rel

PRIVATE_RESOLVER=r'''
namespace ClearingPrivateMirrorSnapshot
open Lean Meta FullRowMinorProofSnapshot

def resolvePrivate (userName : Name) (moduleName : String) : MetaM Name := do
  let env ← getEnv
  unless (env.find? userName).isNone do
    throwError "Original helper unexpectedly has a public kernel binding: {userName}"
  let mut found : Array Name := #[]
  for (actualName, _) in env.constants.toList do
    if Lean.privateToUserName? actualName == some userName &&
       (← ownerModule env actualName) == moduleName then
      found := found.push actualName
  unless found.size == 1 do
    throwError "Exact actual private name/module binding is missing or ambiguous: {userName}"
  let actualName := found[0]!
  let some ci := env.find? actualName | throwError "Actual private CI is absent"
  match ci with
  | .thmInfo _ => pure ()
  | _ => throwError "Private original helper is not a theorem"
  return actualName

def resolveRoots (helpers : Array Name) (target : Name) (equations : Array Name)
    (moduleName output : String) : MetaM (Array Name) := do
  let mut resolved : Array Name := #[]
  let mut mapping : Array Json := #[]
  for userName in helpers do
    let actualName ← resolvePrivate userName moduleName
    resolved := resolved.push actualName
    mapping := mapping.push <| Json.mkObj [
      ("sourceName",toJson userName.toString),("actualName",toJson actualName.toString),
      ("privateUserName",toJson ((Lean.privateToUserName? actualName).map Name.toString)),
      ("owner",← ownerOf (← getEnv) actualName)]
  let env ← getEnv
  unless Lean.privateToUserName? target == none && (← ownerModule env target) == moduleName do
    throwError "Original clearing target is not the unique public source theorem"
  let mut publicNames : Array Name := #[]
  for (actualName, _) in env.constants.toList do
    if (← ownerModule env actualName) == moduleName && (Lean.privateToUserName? actualName).isNone then
      publicNames := publicNames.push actualName
  publicNames := publicNames.qsort (fun a b => a.toString < b.toString)
  for n in publicNames do
    unless n == target || equations.contains n do
      throwError "Local mirror exports an unintended public CI: {n}"
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),("mapping",Json.arr mapping),
    ("publicTarget",toJson target.toString),("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("officialDataEquationCandidates",toJson (equations.map Name.toString))]).compress
  return resolved.push target ++ equations
end ClearingPrivateMirrorSnapshot
'''

def snapshot_candidate(p):
    source_names=p['source_type_only_names'];need(source_names==p['inline_helper_names']+[parent.TARGET]+parent.EQUATIONS,'Exact source 21-CI order differs')
    # Use the same verified official equation API and proof exporter. Only the
    # private root-name resolution and the module/output paths differ.
    raw=parent.snapshot('generated',source_names,set(p['provider_subtracted_names'])).decode()
    raw=raw.replace(parent.SOLUTION_MODULE,MODULE).replace(parent.workspace_rel(parent.STAGE),parent.workspace_rel(STAGE))
    marker='run_meta do\n';need(raw.count(marker)==1,'Frozen snapshot run_meta anchor differs')
    raw=raw.replace(marker,PRIVATE_RESOLVER+'\n'+marker,1)
    static='#['+', '.join('`'+n for n in source_names)+']';helpers='#['+', '.join('`'+n for n in p['inline_helper_names'])+']';eqs='#['+', '.join('`'+n for n in parent.EQUATIONS)+']'
    anchor='  PiExponentInterfaceSnapshot.exportSnapshot '+static
    init='  let roots ← ClearingPrivateMirrorSnapshot.resolveRoots '+helpers+' `'+parent.TARGET+' '+eqs+' '+json.dumps(MODULE)+' '+json.dumps(parent.workspace_rel(STAGE/MAPPING_JSON))+'\n'
    need(raw.count(anchor)==1 and raw.count(static)==2,'Frozen source root-array anchors differ')
    raw=raw.replace(anchor,init+'  PiExponentInterfaceSnapshot.exportSnapshot roots',1)
    raw=raw.replace(' '+static+' #[',' roots #[',1)
    return raw.encode()

def pending_files():
    parent.check_only();p=read(parent.STAGE/'preparation.json');need(len(p['inline_helper_names'])==18 and p['original_proof_AST_units_after_data_and_AP14']==19 and p['original_proof_source_lines_after_data_and_AP14']==201,'Original bounded clearing closure differs')
    body=(parent.STAGE/parent.SOLUTION_OUTPUT).read_bytes();outputs={};edits=[]
    for unit in p['inline_exact_source_units']:
        original=(TASK/unit['source']).read_bytes()[unit['start']:unit['end']]
        need(original.startswith(b'theorem ') and body.count(original)==1,'Private visibility edit lacks unique exact original AST command')
        modified=b'private '+original;vs=unit['ast']['valueStart']['offset']-unit['start'];need(modified[vs+8:]==original[vs:],'Private visibility changed original proof suffix')
        body=body.replace(original,modified,1);edits.append({'source_name':unit['name'],'source_module':unit['module'],'source_byte_range':[unit['start'],unit['end']],'original_command_sha256':sha_bytes(original),'private_command_sha256':sha_bytes(modified),'visibility_prefix_only':'private ','proof_suffix_sha256':sha_bytes(original[vs:]),'proof_suffix_unchanged':True,'target_private_name':'must-be-resolved-from-actual-env-privateToUserName-and-exact-owner'})
        outputs['private-source-units/'+unit['name'].replace('.','_')+'.lean.txt']=modified
    target=(parent.STAGE/'original-target-command.lean.txt').read_bytes();u=p['target_ast'];a=u['start']['offset'];ns,ne=u['nameRange']['start']['offset']-a,u['nameRange']['end']['offset']-a;renamed=target[:ns]+b'solution'+target[ne:]
    need(body.endswith(renamed+b'\n'),'Frozen clearing global solution suffix differs')
    body=body[:-len(renamed)-1]+b'namespace OAI.PiExponent.MatrixArithmetic\n\n'+target+b'\n\nend OAI.PiExponent.MatrixArithmetic\n'
    need(body.count(b'private theorem ')==18 and b'theorem solution' not in body and b'sorry' not in body and b'import Solutions.' not in body,'Private mirror leaks global solution or unsupported proof material')
    outputs[CANDIDATE]=body;outputs[PROBE_CANDIDATE]=snapshot_candidate(p)
    pins={rel(x):sha(x) for x in [SELF,parent.SELF,parent.STAGE/'preparation.json',parent.STAGE/parent.SOLUTION_OUTPUT,parent.AST,parent.SCOPES,parent.GRAPH,parent.RUNTIME,parent.SNAPSHOT_CORE]};pins.update(p['input_hashes'])
    outputs['pending-spec.json']=encode({'schema_version':1,'artifact_kind':'ap16-clearing-private-child-mirror-pending-spec','source_name':parent.TARGET,'source_commit':parent.COMMIT,'platform_module':MODULE,'final_output':OUTPUT,'final_snapshot':SNAPSHOT,'original_AST_count':19,'private_helper_count':18,'public_platform_boundary_names':[parent.TARGET],'helper_public_kernel_names_must_be_absent':p['inline_helper_names'],'private_visibility_edits':edits,'original_target_command_sha256':sha_bytes(target),'all_target_and_helper_proof_suffixes_unchanged':True,'genuine_lazy_equation_CIs':parent.EQUATIONS,'official_equation_API_with_full_primary_Def_values':True,'actual_private_names_are_not_guessed':True,'planned_context_count':2,'source_snapshot_reused_after_actual_AP15_certificate':True,'required_parent_certificate':rel(parent.STAGE/parent.CERTIFICATE),'required_Accepted_Proved_exact_wire_publication':True,'parent_certificate_available':(parent.STAGE/parent.CERTIFICATE).is_file(),'compiler_contexts_finalized':False,'candidate_sha256':sha_bytes(body),'snapshot_candidate_sha256':sha_bytes(outputs[PROBE_CANDIDATE]),'input_hashes':pins,'proof_boundary_names':p['provider_subtracted_names'],'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    return outputs

def pending_check():
    outputs=pending_files()
    for f,raw in outputs.items():
        if f!='pending-spec.json':need((STAGE/f).is_file() and (STAGE/f).read_bytes()==raw,'Pending private mirror differs: '+f)
    p=read(STAGE/'pending-spec.json');need(p['candidate_sha256']==sha(STAGE/CANDIDATE) and p['snapshot_candidate_sha256']==sha(STAGE/PROBE_CANDIDATE) and p['private_helper_count']==18 and p['compiler_contexts_finalized'] is False,'Original pending source specification changed')
    return {'checked_files':len(outputs),'private_helpers':18,'only_public_source_target':parent.TARGET,'contexts_finalized':False,'all_proof_bytes_preserved':True,'validated':False,'Lean_started':False,'API_used':False}

def stage_files():
    pending_check();source_cert=parent.STAGE/parent.CERTIFICATE;cert=read(source_cert)
    need(cert['validated'] is True and cert['Std3_only'] is True and cert['source_and_generated_types_equal'] is True and cert['source_and_generated_actual_proof_references_paired'] is True and len(cert['official_equation_pairs'])==2,'Genuine compiled parent kernel certificate differs')
    import certify_selected_minor_clearing_bound_node as original_consumer
    need(set(cert['actual_external_instance_reference_differences'])==set(original_consumer.EXTERNAL_INSTANCE_DELTAS),'Actual bounded parent instance-contract domain differs')
    p=read(parent.STAGE/'preparation.json');outputs={OUTPUT:(STAGE/CANDIDATE).read_bytes(),SNAPSHOT:(STAGE/PROBE_CANDIDATE).read_bytes()}
    inputs=dict(p['input_hashes']);inputs.update({rel(x):sha(x) for x in [SELF,Path(original_consumer.__file__),source_cert,parent.STAGE/'preparation.json',parent.STAGE/parent.SOLUTION_OUTPUT,parent.STAGE/parent.SOURCE_TYPE_JSON,parent.STAGE/parent.SOURCE_REFS_JSON,STAGE/'pending-spec.json',STAGE/CANDIDATE,STAGE/PROBE_CANDIDATE]})
    for i in range(1,3):path=parent.STAGE/f'source-equation-{i}.json';inputs[rel(path)]=sha(path)
    for f,expected in cert['json_sha256'].items():need(sha(parent.STAGE/f)==expected,'Certified parent kernel JSON changed');inputs[rel(parent.STAGE/f)]=expected
    for pf in cert['preflights'].values():
        for key in ['source','manifest','log']:
            value=pf['data'].get(key)
            if value:
                import validate_namespace_context_providers as context
                q=context.file(value);inputs[rel(q)]=sha(q)
    commands=[]
    for i,(f,imports,mode) in enumerate([(OUTPUT,parent.IMPORTS,'emit-olean'),(SNAPSHOT,['Lean',MODULE],'modecheck')],1):
        outputs[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap16-private-clearing-child-bounded-compiler-manifest','output':parent.workspace_rel(STAGE/f),'output_sha256':sha_bytes(outputs[f]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(parent.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        commands.append('python scripts/preflight_staged_module.py '+parent.verification_rel(STAGE/f)+' --root ap16/clearing-child-mirror --imports-manifest ap16/clearing-child-mirror/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    outputs['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap16-private-clearing-child-kernel-preparation','source_name':parent.TARGET,'source_commit':parent.COMMIT,'platform_module':MODULE,'output':OUTPUT,'private_helper_count':18,'source_type_only_names':p['source_type_only_names'],'public_platform_boundary_names':[parent.TARGET],'helper_public_kernel_names_must_be_absent':p['inline_helper_names'],'provider_subtracted_names':p['provider_subtracted_names'],'all_original_proof_suffixes_unchanged':True,'private_visibility_edit_only':'private ','genuine_lazy_equation_CIs':parent.EQUATIONS,'historical_parent_certificate':rel(source_cert),'historical_parent_certificate_sha256':sha(source_cert),'historical_source_type_json':rel(parent.STAGE/parent.SOURCE_TYPE_JSON),'historical_source_refs_json':rel(parent.STAGE/parent.SOURCE_REFS_JSON),'existing_external_instance_contract':original_consumer.EXTERNAL_INSTANCE_DELTAS,'published_wire_sha256':sha(parent.STAGE/parent.TARGET_OUTPUT),'platform_boundary_certification_pending':True,'real_Accepted_Proved_readback_required_for_final_certificate':True,'accepted_readback_not_a_compiler_input':True,'compiler_contexts_finalized':True,'input_hashes':inputs,'commands':commands,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    outputs['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return outputs

def check_only():
    outputs=stage_files()
    for f,raw in outputs.items():need((STAGE/f).is_file() and (STAGE/f).read_bytes()==raw,'Immutable finalized kernel context differs: '+f)
    for i,f in enumerate([OUTPUT,SNAPSHOT],1):m=read(STAGE/f'c{i}.json');parent.base.runner.verify_manifest_inputs(m);parent.base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(outputs),'private_helpers':18,'only_public_source_target':parent.TARGET,'source_kernel_certificate_sha256':sha(parent.STAGE/parent.CERTIFICATE),'compiler_contexts_finalized':True,'platform_boundary_certification_pending':True,'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare-pending',action='store_true');g.add_argument('--check-pending',action='store_true');g.add_argument('--prepare-kernel',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare_pending or a.prepare_kernel:
        for f,raw in (stage_files() if a.prepare_kernel else pending_files()).items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite pending mirror: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only() if a.prepare_kernel or a.check_only else pending_check(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
