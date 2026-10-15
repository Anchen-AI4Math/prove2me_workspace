"""Finite metadata recursion-limit successor; reuse all fifteen genuine emitters."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import finalize_analytic_translated_two_layer_reduction_v2 as prior

for _n in ['TASK','ROOT','V','read','sha','encode','digest','need','rel','workspace_rel','ACTUAL','NORM','CHILDREN','NEW_NAMES','ACCEPTED','INTERFACE_NAMES','ACTUAL_ID','SOURCE_SNAPSHOT','SOURCE_JSON','SOURCE_AUX_JSON','GENERATED_SNAPSHOTS','GENERATED_JSON','OWNED_JSON','SOLUTION_MODULES','SOURCE_CORE','RUNNER','RUNTIME','LOOKUP','LOOKUP_SHA','CANDIDATE','data','data_consumer','source_root','route','theorem_module','theorem_file','solution_file','units','MULT_MODULE','MISSING_CI']:
    globals()[_n]=getattr(prior,_n)
SELF=Path(__file__).resolve()
OLD_STAGE=prior.STAGE
STAGE=V/'ap20/analytic-translated-two-layer-reduction-final-v3'
CONSUMER=TASK/'scripts/certify_analytic_translated_two_layer_reduction_v3.py'
CERTIFICATE=STAGE/'open-sketch-interface-validation-v3.json'
MAX_REC_DEPTH=100000

def final_files():
    plan=read(OLD_STAGE/'preparation.json');pins=dict(plan['input_hashes']);external=dict(plan['external_dependency_olean_hashes'])
    for p,h in pins.items():need(sha(TASK/p)==h,'Prior immutable input changed: '+p)
    for p,h in external.items():need(sha(Path(p))==h,'Prior immutable external input changed: '+p)
    files={}
    for f,r in plan['files'].items():
        raw=(OLD_STAGE/f).read_bytes();need(digest(raw)==r['sha256'],'Prior prepared source changed: '+f);files[f]=raw
    for n in INTERFACE_NAMES:
        f='source-commands/'+n.replace('.','_')+'.lean.txt';files[f]=(OLD_STAGE/f).read_bytes()
    for f in ['parent-existing-wire.lean','type-import-closure-audit.json']:files[f]=(OLD_STAGE/f).read_bytes()
    for f,raw in files.items():pins[rel(OLD_STAGE/f)]=digest(raw)
    for p in [SELF,CONSUMER,Path(prior.__file__),Path(prior.legacy.__file__),TASK/'scripts/certify_analytic_translated_two_layer_reduction_v2.py',TASK/'scripts/certify_analytic_translated_two_layer_reduction.py',OLD_STAGE/'preparation.json']:
        pins[rel(p)]=sha(p)
    reused=dict(plan['reused_actual_contexts']);commands=[];changes={}
    for i,(f,r) in enumerate(plan['files'].items(),1):
        if i<=15:
            if i<=10:rec=reused[f]['preflight']
            else:
                rec=data.context.record(OLD_STAGE/f,OLD_STAGE/r['manifest'],r['mode'],'.'.join(Path(f).with_suffix('').parts),OLD_STAGE)
                reused[f]={'source':rel(OLD_STAGE/f),'manifest':rel(OLD_STAGE/r['manifest']),'root':rel(OLD_STAGE),'preflight':rec}
            need(rec['data']['success'] and rec['data']['exit_code']==0 and not rec['data']['timed_out'],'Reused actual context failed')
            data.historical(rec,pins,external);r['actual_context_reused']=True
            continue
        raw=files[f];relocated=raw.replace(workspace_rel(OLD_STAGE).encode(),workspace_rel(STAGE).encode())
        at=relocated.index(b'\n\n')+2;changed=relocated[:at]+b'set_option maxRecDepth 100000\n\n'+relocated[at:]
        need(changed.replace(b'set_option maxRecDepth 100000\n\n',b'',1).replace(workspace_rel(STAGE).encode(),workspace_rel(OLD_STAGE).encode())==raw,'Metadata change exceeded recursion option and output locator')
        files[f]=changed;r.update({'actual_context_reused':False,'sha256':digest(changed),'manifest':f'c{i}.json'})
        mf=read(OLD_STAGE/r['manifest']);mf.update({'artifact_kind':'ap20-two-layer-finite-metadata-recursion-successor-bounded-manifest','output':workspace_rel(STAGE/f),'output_sha256':digest(changed),'input_hashes':pins})
        files[r['manifest']]=encode(mf);changes[f]={'prior_source':rel(OLD_STAGE/f),'prior_sha256':digest(raw),'new_sha256':digest(changed),'maxRecDepth':MAX_REC_DEPTH,'only_changes':'finite maxRecDepth option and IO output directory; all mathematical declarations unchanged'}
        commands.append('& '+repr(data.base.PYTHON)+' scripts/preflight_staged_module_windows_bounded.py ap20/analytic-translated-two-layer-reduction-final-v3/'+f+' --root ap20/analytic-translated-two-layer-reduction-final-v3 --imports-manifest ap20/analytic-translated-two-layer-reduction-final-v3/'+r['manifest']+' --timeout-seconds 300')
    failed=(OLD_STAGE/SOURCE_SNAPSHOT).with_name(SOURCE_SNAPSHOT+'.preflight.json');d=read(failed)
    need(not d['success'] and d['exit_code']!=0 and not d['timed_out'] and d['seconds']<=300,'Prior recursion failure not genuine bounded terminal')
    log=data.context.file(d['log']);need(sha(log)==d['log_sha256'] and 'maximum recursion depth' in log.read_text(encoding='utf-8'),'Prior exact recursion failure log differs')
    for p in [failed,log,OLD_STAGE/'c16.json']:pins[rel(p)]=sha(p)
    plan.update({'artifact_kind':'ap20-analytic-translated-two-layer-finite-metadata-recursion-successor-final-preparation','reused_actual_contexts':reused,'reused_context_count':15,'new_bounded_context_count':3,'commands':commands,'finite_metadata_maxRecDepth':MAX_REC_DEPTH,'metadata_only_changes':changes,
      'prior_failed_c16_preserved':{'record':rel(failed),'record_sha256':sha(failed),'log':d['log'],'log_sha256':d['log_sha256'],'reason':'maximum recursion depth reached in metadata #eval; source axioms outputs remain Std3'},'input_hashes':pins,'external_dependency_olean_hashes':external,'mathematical_proof_and_interface_bytes_unchanged':True})
    for i in range(16,19):mf=json.loads(files[f'c{i}.json']);mf['input_hashes']=dict(pins);files[f'c{i}.json']=encode(mf)
    files['preparation.json']=encode(plan);files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def check_only():return prior.legacy.write_exact(STAGE,final_files(),False)
def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--finalize',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    print(json.dumps(prior.legacy.write_exact(STAGE,final_files(),a.finalize),indent=2))
if __name__=='__main__':main()
