"""Check future adapters during server waits; never writes the publication journal."""
import argparse
import json
import re
import sys
from pathlib import Path
import pipeline
import publish

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser()
    parser.add_argument('--prefix',default='block10')
    args=parser.parse_args()
    seen=set()
    def ensure(module):
        if module in seen:
            return
        seen.add(module)
        source=ROOT/Path(*module.split('.')).with_suffix('.lean')
        output=ROOT/'.lake'/'build'/'lib'/'lean'/Path(*module.split('.')).with_suffix('.olean')
        if not source.exists() or output.exists():
            return
        for imported in re.findall(r'^import\s+([^\n]+)',source.read_text(encoding='utf-8'),re.M):
            for child in imported.split():
                ensure(child)
        pipeline.build_interface(module,'precheck-'+module.split('.')[-1])
    for path in sorted((HERE/'platform').glob(args.prefix+'*.json')):
        spec=json.loads(path.read_text(encoding='utf-8'))
        if 'proof_file' not in spec:
            continue
        previous=publish.read_journal().get('proof:'+spec['theorem_name'],{})
        if previous.get('status') in ('ACCEPTED','PENDING','SKETCH_ACCEPTED'):
            continue
        candidate=ROOT/spec['proof_file']
        for imported in re.findall(r'^import\s+([^\n]+)',candidate.read_text(encoding='utf-8'),re.M):
            for child in imported.split():
                ensure(child)
        pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(candidate)],path.stem+'-submission')
    print('Future adapter precheck complete',args.prefix,flush=True)

if __name__=='__main__':
    main()
