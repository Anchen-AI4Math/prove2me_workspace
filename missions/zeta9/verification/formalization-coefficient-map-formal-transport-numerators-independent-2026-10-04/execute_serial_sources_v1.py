"""Execute the seventeen granted independent source builds serially; stop on failure."""
from pathlib import Path
import json, subprocess, sys
OUT=Path(__file__).resolve().parent
PREP=json.loads((OUT/'preparation-verification.json').read_text(encoding='utf8'))
DRIVER=OUT/'run_after_lane_grant.py'
for ordinal,row in enumerate(PREP['source_copies'],1):
    print('START fresh source',ordinal,'/17',row['module'],flush=True)
    result=subprocess.run([sys.executable,str(DRIVER),'source','--module',row['module'],
        '--lane-grant','ROOT_EXPLICIT_LANE_GRANT'])
    if result.returncode:
        print('STOP: retained genuine failed call',ordinal,row['module'],flush=True)
        raise SystemExit(result.returncode)
print('All seventeen source compilations terminal actual0.',flush=True)
