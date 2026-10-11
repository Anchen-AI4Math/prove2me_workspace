"""Serial local checks for the two existing captain milestones."""
import argparse
import sys
import subprocess
import time
import hashlib
import json
from pathlib import Path
import pipeline

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    policy=pipeline.HERE/'verification'/'resource-policy.json'
    if policy.exists() and not json.loads(policy.read_text(encoding='utf-8'))['local_lean_enabled']:
        raise RuntimeError('Local Lean disabled after the reported computer freeze; use platform verification.')
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['probe','strategy','certificate'])
    args=p.parse_args()
    names=['SnakyConditional'] if args.mode=='strategy' else ['SnakyCertificate']
    for name in names:
        target='Definitions.Def_'+name
        output=pipeline.ROOT/'.lake'/'build'/'lib'/'lean'/Path(*target.split('.')).with_suffix('.olean')
        if not output.exists():
            pipeline.build_interface(target,'milestone-def-'+name)
    if args.mode=='probe':
        sources=['Solutions/SnakyMilestones/CertificateProbe.lean']
    elif args.mode=='strategy':
        sources=['missions/snaky-21/platform/milestone35-proof.lean',
                 'Solutions/SnakyMilestones/Strategy35.lean']
    else:
        sources=['Solutions/SnakyMilestones/Certificate35.lean']
    for source in sources:
        label='milestone-'+Path(source).stem
        if args.mode=='strategy':
            pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',source],label)
        else:
            started=time.monotonic()
            log=pipeline.HERE/'verification'/(label+'.log')
            memo=log.with_suffix('.inputs.json')
            tracked=[pipeline.ROOT/source,pipeline.ROOT/'Definitions'/'Def_SnakyCertificate.lean',
                     pipeline.ROOT/'lean-toolchain',pipeline.ROOT/'lake-manifest.json']
            inputs={str(p.relative_to(pipeline.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked}
            if memo.exists() and log.exists() and json.loads(memo.read_text(encoding='utf-8'))==inputs:
                print('REUSE LOCAL PASS',label,flush=True)
                continue
            with log.open('w',encoding='utf-8') as stream:
                result=subprocess.run([str(pipeline.LEAN),'-DautoImplicit=false',source],
                                      cwd=pipeline.ROOT,env=pipeline.environment(),
                                      stdout=stream,stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(label+' failed (exit '+str(result.returncode)+'); inspect '+str(log))
            if inputs!={str(p.relative_to(pipeline.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked}:
                raise RuntimeError('Sources changed during the local check')
            memo.write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
            print('LOCAL PASS',label,f'{time.monotonic()-started:.1f}s',flush=True)

if __name__=='__main__':
    main()
