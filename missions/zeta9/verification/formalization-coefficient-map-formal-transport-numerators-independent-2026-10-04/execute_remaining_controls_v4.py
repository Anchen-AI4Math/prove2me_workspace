"""Serial compact control after confirmed Root-cap cancellation of the unrolled audit."""
from pathlib import Path
import json, subprocess, sys
sys.stdout.reconfigure(encoding='utf8')
OUT=Path(__file__).resolve().parent
prior=json.loads((OUT/'r23-no-residual-process-verification.json').read_text(encoding='utf8'))
assert prior['remaining_matching_Lean_lake_python_processes']==[]
assert prior['outcome']=='INTENTIONALLY_CANCELLED_AT_ROOT_CPU_CAP_NOT_PASS_NOT_THEOREM_FAILURE'
DRIVER=OUT/'run_after_lane_grant_v2.py'
for mode,file in [('audit','IndependentSourceGraphV3.lean'),
                  ('audit','IndependentFullValues.lean'),
                  ('audit','IndependentBoundaries.lean'),
                  ('resolver','IndependentResolverV2.lean')]:
    print('START independent compact remaining control',file,flush=True)
    result=subprocess.run([sys.executable,str(DRIVER),mode,'--file',file,
        '--lane-grant','ROOT_EXPLICIT_LANE_GRANT'])
    if result.returncode:
        r=json.loads((OUT/'actual-execution-receipt.json').read_text(encoding='utf8'))['rows'][-1]
        text=(OUT.parents[3]/r['log']['root_relative']).read_text(encoding='utf8',errors='replace')
        print('\n'.join(line for line in text.splitlines() if 'error' in line.lower())[:10000],flush=True)
        print('STOP retained genuine failure',file,flush=True)
        raise SystemExit(result.returncode)
print('All compact remaining controls terminal actual0.',flush=True)
