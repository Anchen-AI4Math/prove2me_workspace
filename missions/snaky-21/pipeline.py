"""Publish only locally checked increments, connecting the certificate chain."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE))
import publish

LEAN=Path(r'C:\Users\anche\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe')
LAKE=LEAN.with_name('lake.exe')

def environment():
    env=os.environ.copy()
    packages=ROOT/'.lake'/'packages'
    dirs=[p/'.lake'/'build'/'lib'/'lean' for p in packages.iterdir() if p.is_dir()]
    dirs.append(ROOT/'.lake'/'build'/'lib'/'lean')
    env['LEAN_PATH']=';'.join(str(p) for p in dirs if p.exists())
    env['PATH']=str(LEAN.parent)+os.pathsep+env.get('PATH','')
    return env

def run_checked(args,label):
    policy=HERE/'verification'/'resource-policy.json'
    if Path(str(args[0])).name.lower() in {'lean.exe','lean','lake.exe','lake'} and policy.exists():
        if not json.loads(policy.read_text(encoding='utf-8')).get('local_lean_enabled',True):
            raise RuntimeError('Local Lean/Lake is disabled after the user reported a computer freeze; use the platform-only milestone queue.')
    report=HERE/'verification'/(label+'.log')
    memo=report.with_suffix('.inputs.json')
    inputs=None
    if str(args[0])==str(LEAN) and '-o' not in args and str(args[-1]).endswith('.lean'):
        candidate=Path(args[-1])
        if not candidate.is_absolute():
            candidate=ROOT/candidate
        inputs={}
        visited=set()
        def visit(path):
            if path in visited or not path.is_file():
                return
            visited.add(path)
            inputs[str(path.relative_to(ROOT))]=hashlib.sha256(path.read_bytes()).hexdigest()
            for imported in re.findall(r'^import\s+([^\n]+)',path.read_text(encoding='utf-8'),re.M):
                for module in imported.split():
                    visit(ROOT/Path(*module.split('.')).with_suffix('.lean'))
        visit(candidate)
        for path in (ROOT/'lean-toolchain', ROOT/'lake-manifest.json'):
            inputs[str(path.relative_to(ROOT))]=hashlib.sha256(path.read_bytes()).hexdigest()
        if memo.exists() and report.exists() and json.loads(memo.read_text(encoding='utf-8'))==inputs:
            print('REUSE LOCAL PASS',label,flush=True)
            return
    started=time.monotonic()
    result=subprocess.run(args,cwd=ROOT,env=environment(),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    report.write_text(result.stdout,encoding='utf-8')
    if result.returncode:
        print(result.stdout[-12000:],flush=True)
        raise RuntimeError(label+' local verification failed')
    if inputs is not None:
        memo.write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
    print('LOCAL PASS',label,f'{time.monotonic()-started:.1f}s',flush=True)

def build_interface(target,label):
    source=ROOT/Path(*target.split('.')).with_suffix('.lean')
    output=ROOT/'.lake'/'build'/'lib'/'lean'/Path(*target.split('.')).with_suffix('.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    run_checked([str(LEAN),'-DautoImplicit=false',str(source),'-o',str(output)],label)

def lemma(slug):
    spec=HERE/'platform'/(slug+'.json')
    obj=json.loads(spec.read_text(encoding='utf-8'))
    candidate=ROOT/obj['proof_file']
    previous=publish.read_journal().get('proof:'+obj['theorem_name'],{})
    digest=hashlib.sha256(candidate.read_text(encoding='utf-8').encode('utf-8')).hexdigest()
    target='Theorems.Thm_'+obj['theorem_name'].replace('.','_')
    if previous.get('status')=='ACCEPTED' and previous.get('source_sha256')==digest:
        print('REUSE ACCEPTED',slug,flush=True)
        interface=ROOT/'.lake'/'build'/'lib'/'lean'/Path(*target.split('.')).with_suffix('.olean')
        if not interface.exists():
            build_interface(target,slug+'-interface')
        return
    if not (previous.get('status')=='PENDING' and previous.get('source_sha256')==digest):
        run_checked([str(LEAN),'-DautoImplicit=false',str(candidate)],slug+'-submission')
    else:
        print('RESUME CHECKED PENDING',slug,flush=True)
    journal=publish.read_journal()
    result=publish.lemma(spec,publish.api.get_token(),journal)
    if result['status']!='ACCEPTED':
        raise RuntimeError('The proof chain still has unproved dependencies: '+slug)
    build_interface(target,slug+'-interface')

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser()
    parser.add_argument('--through',type=int,default=11)
    args=parser.parse_args()
    lemma('calculus')
    lemma('strategy')
    for block in range(args.through+1):
        # The independent reconstruction data modules were already compiled.
        path=ROOT/'Definitions'/f'Def_Snaky21Data{block:02}.lean'
        publish.definition(path,publish.api.get_token(),publish.read_journal())
        if block==11:
            publish.definition(ROOT/'Definitions'/'Def_Snaky21Calc11.lean',publish.api.get_token(),publish.read_journal())
        for part_spec in sorted((HERE/'platform').glob(f'block{block:02}-part*.json')):
            if block==11 and part_spec.stem=='block11-part23':
                for calculations in sorted((HERE/'platform').glob('final-calculations*.json')):
                    lemma(calculations.stem)
            lemma(part_spec.stem)
        lemma(f'block{block:02}')
    print('PUBLICATION CHAIN ACCEPTED through block',args.through,flush=True)

if __name__=='__main__':
    try:
        main()
    except Exception as error:
        (HERE/'verification'/'pipeline-error.json').write_text(json.dumps({'type':type(error).__name__,'message':str(error)},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        raise
