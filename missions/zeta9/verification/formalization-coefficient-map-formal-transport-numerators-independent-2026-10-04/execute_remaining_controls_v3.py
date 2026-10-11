"""Continue with the new source-expression depth control; serial granted lane."""
from pathlib import Path
import json, subprocess, sys
sys.stdout.reconfigure(encoding='utf8')
OUT=Path(__file__).resolve().parent
DRIVER=OUT/'run_after_lane_grant_v2.py'
for mode,file in [('audit','IndependentSourceGraphV2.lean'),
                  ('audit','IndependentFullValues.lean'),
                  ('audit','IndependentBoundaries.lean'),
                  ('resolver','IndependentResolverV2.lean')]:
    print('START independent remaining control',file,flush=True)
    result=subprocess.run([sys.executable,str(DRIVER),mode,'--file',file,
        '--lane-grant','ROOT_EXPLICIT_LANE_GRANT'])
    if result.returncode:
        r=json.loads((OUT/'actual-execution-receipt.json').read_text(encoding='utf8'))['rows'][-1]
        text=(OUT.parents[3]/r['log']['root_relative']).read_text(encoding='utf8',errors='replace')
        print('\n'.join(line for line in text.splitlines() if 'error' in line.lower())[:10000],flush=True)
        print('STOP retained genuine failure',file,flush=True)
        raise SystemExit(result.returncode)
print('Remaining controls all terminal actual0.',flush=True)
