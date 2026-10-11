"""Run the granted independent control calls serially; retain and stop at any failure."""
from pathlib import Path
import json, subprocess, sys
OUT=Path(__file__).resolve().parent
DRIVER=OUT/'run_after_lane_grant.py'
commands=[('alias','--module','IndependentDataValues'),
          ('alias','--module','IndependentWholeTypes'),
          ('audit','--file','IndependentSourceGraph.lean'),
          ('audit','--file','IndependentFullValues.lean'),
          ('audit','--file','IndependentBoundaries.lean'),
          ('resolver','--file','IndependentResolver.lean')]
for mode,flag,name in commands:
    print('START independent control',mode,name,flush=True)
    result=subprocess.run([sys.executable,str(DRIVER),mode,flag,name,
        '--lane-grant','ROOT_EXPLICIT_LANE_GRANT'])
    if result.returncode:
        receipt=json.loads((OUT/'actual-execution-receipt.json').read_text(encoding='utf8'))
        root=OUT.parents[3]
        log=root/receipt['rows'][-1]['log']['root_relative']
        print(log.read_text(encoding='utf8',errors='replace')[-10000:],flush=True)
        print('STOP: genuine failure retained',name,flush=True)
        raise SystemExit(result.returncode)
print('All original independent controls terminal actual0.',flush=True)
