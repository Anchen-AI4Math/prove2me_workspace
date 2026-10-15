"""Compare the unmodified official oracle under --run and native compilation."""
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
OUT=VER/'native-oracle-benchmark'
OUT.mkdir(exist_ok=True)
LAKE=Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe'
TOOL=ROOT/'scripts/extract_sketch_info.lean'
EXE=ROOT/'.lake/build/bin/threeSum1960614SketchOracle.exe'
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
modules=['Submission.ThreeSumApsp.Lang.Syntax',
         'Submission.ThreeSum.ModelWitnessLogs',
         'Submission.ThreeSum.EncodedColorWantedCosts']
results=[]
for module in modules:
    source=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
    modes={}
    for mode in ['native','interpreter']:
        output=OUT/(module.replace('.','_')+'-'+mode+'.jsonl')
        stderr=output.with_suffix('.stderr.txt')
        command=([str(LAKE),'env',str(EXE),str(source)] if mode=='native' else
                 [str(LAKE),'env','lean','--run',str(TOOL),str(source)])
        started=time.monotonic()
        with output.open('w',encoding='utf-8') as out,stderr.open('w',encoding='utf-8') as err:
            run=subprocess.run(command,cwd=ROOT,env=env,stdout=out,stderr=err)
        elapsed=time.monotonic()-started
        assert run.returncode==0,(module,mode,str(stderr))
        facts=[json.loads(line) for line in output.read_text(encoding='utf-8').splitlines() if line.strip()]
        assert all(f['kind'] in ('decl','ref') for f in facts)
        modes[mode]={'elapsed_seconds':elapsed,'fact_count':len(facts),
                     'sha256':hashlib.sha256(output.read_bytes()).hexdigest(),
                     'facts':facts,'path':output.relative_to(ROOT).as_posix()}
        print(module,mode,round(elapsed,2),'seconds',len(facts),'facts',flush=True)
    # Order is not a mathematical fact; compare the complete exact JSON facts.
    normalize=lambda facts:sorted(json.dumps(f,sort_keys=True) for f in facts)
    identical=normalize(modes['native']['facts'])==normalize(modes['interpreter']['facts'])
    for record in modes.values():record.pop('facts')
    results.append({'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                    'identical_fact_set':identical,'modes':modes})
    assert identical,('Oracle fact mismatch',module)
receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),
         'official_source_sha256':hashlib.sha256(TOOL.read_bytes()).hexdigest(),
         'native_executable_sha256':hashlib.sha256(EXE.read_bytes()).hexdigest(),
         'all_fact_sets_identical':all(r['identical_fact_set'] for r in results),
         'results':results}
native=sum(r['modes']['native']['elapsed_seconds'] for r in results)
interpreted=sum(r['modes']['interpreter']['elapsed_seconds'] for r in results)
receipt.update(native_total_seconds=native,interpreter_total_seconds=interpreted,
               measured_speedup=interpreted/native)
(VER/'native-oracle-benchmark.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('Exact facts matched; measured aggregate speedup:',round(interpreted/native,3),flush=True)
