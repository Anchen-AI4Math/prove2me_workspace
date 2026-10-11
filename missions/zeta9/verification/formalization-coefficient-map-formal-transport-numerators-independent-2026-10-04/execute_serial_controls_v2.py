"""Continue the granted lane after the retained v1 full-type failure; serial only."""
from pathlib import Path
import json, subprocess, sys
sys.stdout.reconfigure(encoding='utf8')
OUT=Path(__file__).resolve().parent
DRIVER=OUT/'run_after_lane_grant_v2.py'
commands=[('alias','--module','IndependentWholeTypesV2'),
          ('audit','--file','IndependentSourceGraph.lean'),
          ('audit','--file','IndependentFullValues.lean'),
          ('audit','--file','IndependentBoundaries.lean'),
          ('resolver','--file','IndependentResolverV2.lean')]
for mode,flag,name in commands:
    print('START independent v2 control',mode,name,flush=True)
    result=subprocess.run([sys.executable,str(DRIVER),mode,flag,name,
        '--lane-grant','ROOT_EXPLICIT_LANE_GRANT'])
    if result.returncode:
        receipt=json.loads((OUT/'actual-execution-receipt.json').read_text(encoding='utf8'))
        log=OUT.parents[3]/receipt['rows'][-1]['log']['root_relative']
        lines=log.read_text(encoding='utf8',errors='replace').splitlines()
        print('\n'.join(line for line in lines if 'error' in line.lower())[:10000],flush=True)
        print('STOP: genuine failed call and full log retained',name,flush=True)
        raise SystemExit(result.returncode)
print('All repaired full types and remaining original controls terminal actual0.',flush=True)
