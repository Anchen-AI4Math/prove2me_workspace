"""Pure local closed mirror of the already proved AP13 platform child; original names."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_shifted_gaussian_node as parent
TASK,ROOT,V=parent.TASK,parent.ROOT,parent.V
SELF=Path(__file__).resolve()
STAGE=V/'ap14/shifted-child-mirror'
MODULE=parent.TARGET_OUTPUT[:-5].replace('/','.')
OUTPUT=parent.TARGET_OUTPUT
SNAPSHOT='GeneratedSnapshot.lean'
TYPE_JSON,REFS_JSON='generated-types.json','generated-proof-references.json'
CERTIFICATE='local-child-validation.json'
PUBLISHED=STAGE/'accepted-publication-record.json'
read,sha,sha_bytes,encode,need,rel=parent.read,parent.sha,parent.sha_bytes,parent.encode,parent.need,parent.rel

def stage_files():
    parent.check_only();graph,closure,provided,units,commands,pins,adaptations,witness=parent.authority()
    cert=parent.STAGE/parent.CERTIFICATE;r=read(cert)
    need(r['validated'] is True and r['Std3_only'] is True and r['source_and_generated_types_equal'] is True and r['source_and_generated_actual_proof_references_paired'] is True,'Missing strict AP13 original proof certificate')
    pub=read(PUBLISHED);need(pub['confirmed_proved'] is True and pub['last_verify_verdict']['body']['status']=='ACCEPTED' and pub['target_readback']['body']['status']=='Proved' and pub['theorem_name']==parent.TARGET and (pub['target_readback']['body']['preamble']+pub['target_readback']['body']['formal_statement']).encode()==(parent.STAGE/parent.TARGET_OUTPUT).read_bytes(),'Actual Accepted parent or exact Published wire differs')
    names=[u['name'] for u in units]
    body=(''.join('import '+m+'\n' for m in parent.IMPORTS)+'\nnamespace OAI.PiExponent.Arithmetic\n\n').encode()+b'\n\n'.join(c[2] for c in commands)+b'\n\nend OAI.PiExponent.Arithmetic\n'
    need(b'theorem solution' not in body and b'sorry' not in body,'Closed mirror must retain original names without global solution')
    ns='#['+', '.join('`'+n for n in names)+']'
    probe=('import Lean\nimport '+MODULE+'\n\n'+parent.SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()+'\n'+parent.base.ap8.PROBE+'\n'+parent.PROBE+'\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot '+ns+' '+json.dumps(parent.workspace_rel(STAGE/TYPE_JSON))+'\n  ShiftedGaussianProofSnapshot.exportBundle "generated" '+json.dumps(parent.workspace_rel(STAGE/REFS_JSON))+' '+ns+' #['+json.dumps(MODULE)+'] #[]\n#print axioms '+parent.TARGET+'\n').encode()
    outputs={OUTPUT:body,SNAPSHOT:probe}
    inputs={rel(x):sha(x) for x in [SELF,parent.SELF,PUBLISHED,cert,parent.STAGE/'preparation.json',parent.STAGE/parent.SOURCE_TYPE_JSON,parent.STAGE/parent.SOURCE_REFS_JSON,parent.SNAPSHOT_CORE,parent.RUNTIME,Path(parent.base.runner.__file__)]}
    inputs.update(pins)
    commands=[]
    for i,(f,imports,mode) in enumerate([(OUTPUT,parent.IMPORTS,'emit-olean'),(SNAPSHOT,['Lean',MODULE],'modecheck')],1):
        outputs[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap14-closed-child-mirror-bounded-compiler-manifest','output':parent.workspace_rel(STAGE/f),'output_sha256':sha_bytes(outputs[f]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(parent.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        commands.append('python scripts/preflight_staged_module.py '+parent.verification_rel(STAGE/f)+' --root ap14/shifted-child-mirror --imports-manifest ap14/shifted-child-mirror/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    outputs['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap14-closed-child-mirror-preparation','source_name':parent.TARGET,'source_commit':parent.COMMIT,'module':MODULE,'output':OUTPUT,'provided_names':names,'inline_original_AST_units':units,'existing_port_adaptations':adaptations,'historical_parent_certificate':rel(cert),'historical_parent_certificate_sha256':sha(cert),'historical_source_type_json':rel(parent.STAGE/parent.SOURCE_TYPE_JSON),'historical_source_refs_json':rel(parent.STAGE/parent.SOURCE_REFS_JSON),'published_wire_sha256':sha(parent.STAGE/parent.TARGET_OUTPUT),'published_wire_unchanged':True,'local_mirror_of_actual_accepted_child':True,'accepted_evidence':rel(PUBLISHED),'accepted_evidence_sha256':sha(PUBLISHED),'accepted_theorem_id':pub['theorem_id'],'accepted_proof_id':pub['last_verify_verdict']['body']['id'],'all_original_port_command_bytes_preserved':True,'no_global_solution':True,'input_hashes':inputs,'commands':commands,'validated':False,'submission_ready':False,'proposal_status':'Draft','Lean_started':False,'API_used':False})
    outputs['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return outputs

def check_only():
    outputs=stage_files()
    for f,raw in outputs.items():need((STAGE/f).is_file() and (STAGE/f).read_bytes()==raw,'Immutable closed mirror changed: '+f)
    for i,f in enumerate([OUTPUT,SNAPSHOT],1):
        m=read(STAGE/f'c{i}.json');parent.base.runner.verify_manifest_inputs(m);parent.base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(outputs),'original_named_theorems':9,'original_named_platform_child':parent.TARGET,'no_global_solution':True,'wire_unchanged':True,'all_hashes_match':True,'validated':False,'Lean_started':False,'API_used':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for f,raw in stage_files().items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
