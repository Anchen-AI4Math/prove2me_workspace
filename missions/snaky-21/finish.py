"""Durable, sequential completion runner with task-local verification logs."""
import json
import subprocess
import sys
import time
from pathlib import Path
import pipeline
import publish
import local_completion

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    print('PHASE local closed proof',flush=True)
    if local_completion.unchanged():
        print('REUSE unchanged audited actual proof',flush=True)
    else:
        pipeline.run_checked([sys.executable,'-B','scripts/workspace.py','build','snaky-21'],'closed-build')
        local_completion.record()
    print('PHASE connected platform certificate',flush=True)
    for attempt in range(4):
        result=subprocess.run([sys.executable,'-B',str(HERE/'pipeline.py'),'--through','11'],cwd=ROOT,env=pipeline.environment())
        if not result.returncode:
            break
        error_path=HERE/'verification'/'pipeline-error.json'
        error=json.loads(error_path.read_text(encoding='utf-8')) if error_path.exists() else {}
        if attempt==3 or error.get('type') not in ('URLError','TimeoutError','ConnectionError','ConnectionResetError','RemoteDisconnected'):
            raise RuntimeError('Certificate publication chain interrupted')
        print('RESUME saved chain after transport interruption',flush=True)
        time.sleep(20)
    publish.definition(ROOT/'Definitions'/'Def_Snaky21Catalog.lean',publish.api.get_token(),publish.read_journal())
    pipeline.lemma('catalog')
    pipeline.lemma('certificate')
    pipeline.lemma('empty-force')
    spec=json.loads((HERE/'platform'/'main.json').read_text(encoding='utf-8'))
    candidate=ROOT/spec['proof_file']
    pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(candidate)],'main-submission')
    publish.submit(spec['theorem_id'],candidate,spec['explanation'],publish.api.get_token(),publish.read_journal(),spec['theorem_name'],resubmit_sketch=True)
    token=publish.api.get_token()
    target=publish.request('GET','/theorems/'+spec['theorem_id'],token)
    if target['status']!='Proved':
        raise RuntimeError('Main theorem status: '+target['status'])
    (HERE/'verification'/'final-platform.json').write_text(json.dumps(target,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('COMPLETE: exact existing main goal is Proved',flush=True)
    pipeline.run_checked([sys.executable,'-B',str(HERE/'finalize.py')],'final-audit')

if __name__=='__main__':
    main()
